(** Link whole authenticated products in declarative order. This is a build
    publication step, not an alternative proof checker or extraction cache. *)
open SomaBuildPlan
module IO = SomaProjectBuild
let fail fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt
type piece = Product of { owner : string; name : string } | Whitespace of string
type unit_ = { name : string; output : string; pieces : piece list }
type product = { owner : string; path : string; digest : string }
type inventory = { config_hash : string; sources : (string * string) list;
                   products : (string * product) list }
let keys allowed t = List.iter (fun (key,_) -> if not (List.mem key allowed) then
    fail "unknown artifact-unit key %S" key) t
let field t key = match List.assoc_opt key t with Some e -> e
  | None -> fail "missing artifact-unit field %S" key
let table e = match e.SomaToml.value with Table t -> t | _ -> fail "expected a table at line %d" e.line
let string e = match e.SomaToml.value with String s -> s | _ -> fail "expected a string at line %d" e.line
let text t key = string (field t key)
let version t = match (field t "format").SomaToml.value with
  | Int 1 -> () | _ -> fail "unsupported artifact-unit format"
let path s = if not (relative_path s) then fail "unsafe artifact-unit path %S" s; s
let basename s = ignore (path s); if Filename.basename s<>s then fail "expected an artifact name: %S" s; s
let digest s = if not (SomaMerkle.valid_hash s) then fail "invalid SHA-256 digest"; s
let parse text = try SomaToml.parse text with SomaToml.Error (line,reason) ->
    fail "line %d: %s" line reason
let layout contents =
  let t=parse contents in keys ["format";"units"] t; version t;
  let outputs=Hashtbl.create 16 in
  table (field t "units") |> List.map (fun (name,e) ->
      ignore (basename name);
      let t=table e in keys ["output";"parts"] t;
      let output=path (text t "output") in
      if not (Filename.check_suffix output ".ml" || Filename.check_suffix output ".mli") then
        fail "unit output must be .ml or .mli";
      Hashtbl.iter (fun previous _ ->
          if output=previous || String.starts_with ~prefix:(previous ^ "/") output ||
             String.starts_with ~prefix:(output ^ "/") previous then
            fail "conflicting artifact-unit outputs %S and %S" previous output) outputs;
      Hashtbl.add outputs output ();
      let seen=Hashtbl.create 16 in
      let pieces=match (field t "parts").value with
        | Array xs when xs<>[] -> List.map (fun value ->
            let t=table {e with value} in
            if List.mem_assoc "whitespace" t then begin
              keys ["whitespace"] t;
              let s=text t "whitespace" in
              if not (String.for_all (fun c -> List.mem c [' ';'\t';'\r';'\n']) s) then
                fail "OCaml text is not allowed in artifact-unit configuration";
              Whitespace s
            end else begin
              keys ["owner";"product"] t;
              let owner=basename (text t "owner") and name=basename (text t "product") in
              if Hashtbl.mem seen name then fail "duplicate whole product %S" name;
              Hashtbl.add seen name (); Product {owner;name}
            end) xs
        | _ -> fail "unit parts must be a nonempty array" in
      if not (List.exists (function Product _ -> true | _ -> false) pieces) then
        fail "a unit must contain at least one whole product";
      {name;output;pieces})
let inventory contents =
  let t=parse contents in keys ["format";"config-sha256";"sources";"products"] t; version t;
  let config_hash=digest (text t "config-sha256") in
  let sources=table (field t "sources") |> List.map (fun (p,e) -> path p, digest (string e)) in
  if sources=[] then fail "an artifact inventory must authenticate its source inputs";
  let products=table (field t "products") |> List.map (fun (name,e) ->
      ignore (basename name);
      let t=table e in keys ["owner";"path";"sha256"] t;
      name,{owner=basename (text t "owner");path=path (text t "path");digest=digest (text t "sha256")}) in
  {config_hash;sources;products}
let execute ~config ~manifest ~selected ~check =
  let config=if Filename.is_relative config then Filename.concat (Sys.getcwd ()) config else config in
  let root=Unix.realpath (Filename.dirname config) in
  let config=IO.inside root (Filename.basename config) in
  let manifest=if Filename.is_relative manifest then Filename.concat (Sys.getcwd ()) manifest else manifest in
  let manifest_root=Unix.realpath (Filename.dirname manifest) in
  let manifest=IO.inside manifest_root (Filename.basename manifest) in
  let lock_path=IO.inside manifest_root ".soma-units.lock" in
  let lock=Unix.openfile lock_path [Unix.O_RDWR;Unix.O_CREAT;Unix.O_CLOEXEC] 0o600 in
  Fun.protect ~finally:(fun () -> Unix.close lock) (fun () ->
      Unix.lockf lock Unix.F_LOCK 0;
      let config_bytes=IO.read config and manifest_bytes=IO.read manifest in
      let units=layout config_bytes and inv=inventory manifest_bytes in
      if inv.config_hash<>SomaMerkle.string config_bytes then fail "artifact layout changed after inventory checking";
      let units=if selected=[] then units else List.map (fun name ->
          match List.find_opt (fun u -> u.name=name) units with Some u -> u
          | None -> fail "unknown artifact unit %S" name) selected in
      let products=List.map (fun (name,p) ->
          name,(p,IO.verified root p.path p.digest)) inv.products in
      List.iter (fun (p,h) -> ignore (IO.verified root p h)) inv.sources;
      let inputs=config::manifest::List.map (fun (p,_) -> IO.inside root p) inv.sources @
        List.map (fun (_,p) -> IO.inside root p.path) inv.products in
      let outputs=List.map (fun u ->
          let output=IO.inside root u.output in
          if List.exists (fun input -> input=output ||
              (Sys.file_exists output && Unix.realpath output=Unix.realpath input)) inputs then
            fail "unit output overwrites a checked input: %s" output;
          let seen=Hashtbl.create 16 in
          let contents=List.map (function
              | Whitespace s -> s
              | Product a ->
                let p,bytes=match List.assoc_opt a.name products with Some p -> p
                  | None -> fail "missing checked product %S" a.name in
                if p.owner<>a.owner then fail "product owner differs: %s" a.name;
                let physical=Unix.realpath (IO.inside root p.path) in
                if Hashtbl.mem seen physical then fail "aliased product repeats initialization: %s" a.name;
                Hashtbl.add seen physical (); bytes) u.pieces |> String.concat "" in
          let parts=List.map (function
              | Whitespace s -> "{ whitespace = " ^ IO.toml_string s ^ " }"
              | Product a ->
                let p,bytes=List.assoc a.name products in
                Printf.sprintf "{ owner = %s, product = %s, sha256 = %s, size = %d }"
                  (IO.toml_string a.owner) (IO.toml_string a.name) (IO.toml_string p.digest) (String.length bytes)) u.pieces in
          let receipt=Printf.sprintf "format = 1\nconfig-sha256 = %s\ninventory-sha256 = %s\nsha256 = %s\nparts = [%s]\n"
              (IO.toml_string inv.config_hash) (IO.toml_string (SomaMerkle.string manifest_bytes))
              (IO.toml_string (SomaMerkle.string contents)) (String.concat ",\n" parts) in
          let receipt_path=IO.inside manifest_root (u.name ^ ".composition.toml") in
          let source_map=IO.inside root (u.output ^ ".soma-parts.toml") in
          if List.mem receipt_path inputs || List.mem source_map inputs then
            fail "composition receipt overwrites a checked input";
          output,contents,receipt_path,source_map,receipt) units in
      (* Validate the full selected publication before replacing any output. *)
      if IO.read config<>config_bytes || IO.read manifest<>manifest_bytes then
        fail "artifact-unit metadata changed during publication";
      List.iter (fun (p,h) -> ignore (IO.verified root p h)) inv.sources;
      List.iter (fun (_,p) -> ignore (IO.verified root p.path p.digest)) inv.products;
      List.iter (fun (file,data,receipt_path,source_map,receipt) ->
          if check then begin
            IO.regular file;
            if IO.read file<>data then fail "whole unit differs from declared layout: %s" file;
            Printf.printf "checked %s\n%!" file
          end else begin
            let changed=IO.atomic file data in
            ignore (IO.atomic receipt_path receipt);
            ignore (IO.atomic source_map receipt);
            Printf.printf "%s %s\n%!" (if changed then "built" else "unchanged") file
          end) outputs)
let help = {|Usage: soma project assemble --config FILE --inventory FILE
                             [--unit NAME ...] [--check]
Publish complete checked artifacts in declarative order. The inventory comes
from the project's proof/origin gate; all source and product hashes are rechecked.
Only whole products and ASCII whitespace are accepted, never OCaml snippets.
This command does not replace proof checking or certify an extraction cache.
|}
let run args =
  if args=["--help"] then print_string help else
  let rec options config manifest selected check = function
    | [] ->
      (match config,manifest with Some config,Some manifest ->
         execute ~config ~manifest ~selected:(List.rev selected) ~check
       | _ -> fail "%s" help)
    | "--config"::s::xs -> options (Some s) manifest selected check xs
    | "--inventory"::s::xs -> options config (Some s) selected check xs
    | "--unit"::s::xs -> options config manifest (s::selected) check xs
    | "--check"::xs -> options config manifest selected true xs
    | s::_ -> fail "unknown artifact-unit option %S" s in
  options None None [] false args
