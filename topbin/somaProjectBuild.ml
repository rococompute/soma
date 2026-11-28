open SomaBuildPlan
let fail fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt
let read file =
  let ic = open_in_bin file in
  Fun.protect ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))
let toml_string s =
  let b=Buffer.create (String.length s+2) in
  Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n" | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 32 || Char.code c = 127 ->
        Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'; Buffer.contents b
let rec mkdir dir =
  if Sys.file_exists dir then begin
    if (Unix.lstat dir).Unix.st_kind <> Unix.S_DIR then fail "not a real directory: %s" dir
  end else begin mkdir (Filename.dirname dir); Unix.mkdir dir 0o755 end
(* No path traversal, including through symlinks. Roots themselves are canonical. *)
let inside root relative =
  if not (relative_path relative) then fail "invalid artifact path %S" relative;
  List.fold_left (fun base part ->
      let p = Filename.concat base part in
      (try if (Unix.lstat p).Unix.st_kind = Unix.S_LNK then fail "symlink in build path: %s" p
       with Unix.Unix_error (Unix.ENOENT,_,_) -> ()); p)
    root (String.split_on_char '/' relative)
let regular file = if (Unix.lstat file).Unix.st_kind <> Unix.S_REG then fail "not a regular file: %s" file
let atomic file data =
  mkdir (Filename.dirname file);
  let same = Sys.file_exists file && (regular file; read file = data) in
  if not same then begin
    let tmp, oc = Filename.open_temp_file ~temp_dir:(Filename.dirname file) ".soma-unit-" ".tmp" in
    Fun.protect ~finally:(fun () -> close_out_noerr oc; if Sys.file_exists tmp then Sys.remove tmp) (fun () ->
        output_string oc data; close_out oc; Unix.chmod tmp 0o644; Unix.rename tmp file)
  end;
  not same
let fields line =
  let len = String.length line in
  let rec skip i = if i<len && (line.[i]=' ' || line.[i]='\t') then skip (i+1) else i in
  let rec quoted start i =
    if i>=len then fail "unterminated manifest string";
    if line.[i]='\\' then quoted start (i+2)
    else if line.[i]='"' then
      (try Scanf.unescaped (String.sub line start (i-start)), i+1
       with _ -> fail "invalid manifest escape")
    else quoted start (i+1) in
  let rec token i j = if j=len || line.[j]=' ' || line.[j]='\t' then String.sub line i (j-i),j else token i (j+1) in
  let rec loop acc i = let i=skip i in if i=len then List.rev acc else
      let s,j = if line.[i]='"' then quoted (i+1) (i+1) else token i i in
      if j<len && line.[j]<>' ' && line.[j]<>'\t' then fail "invalid manifest field separator";
      loop (s::acc) j in
  loop [] 0
type leaf = { identity : string; file : string; hash : string; contents : string }
type piece = Data of leaf | Padding of string
type product = { file : string; pieces : piece list }
type artifact_row = {
  scope : string; source : string; source_hash : string;
  filename : string; digest : string; ordinal : string option;
  exported : export option;
}
let verified root path hash =
  let file = inside root path in regular file;
  let contents = read file in
  if not (SomaMerkle.valid_hash hash) || SomaMerkle.string contents <> hash then
    fail "content hash differs: %s" file;
  contents
let compiler_inventory root =
  let manifest=inside root ".soma-ocaml-files" in regular manifest;
  let entries=String.split_on_char '\n' (read manifest) |> List.filter ((<>) "") |> List.map (fun line ->
          match String.split_on_char ' ' line with
          | [file;hash] when relative_path file && SomaMerkle.valid_hash hash -> file,hash
          | _ -> fail "invalid compiler product inventory: %s" manifest) in
  if List.length entries<>List.length (List.sort_uniq String.compare (List.map fst entries)) then
    fail "duplicate compiler product in %s" manifest;
  entries
let whole_file ~root ~extract file =
  let path=inside root file in regular path;
  let contents=if file="verification.toml" then read path else begin
      let entries=compiler_inventory root in
      let hash=match List.assoc_opt file entries with
        | Some hash -> hash | None -> fail "%s is not in the completed compiler product inventory" file in
      verified root file hash
    end in
  {identity=extract ^ "/" ^ file;file;hash=SomaMerkle.string contents;contents}
let rec artifact ?expect ~root ~source_root ~extract kind scope =
  (* Static initialization publishes the namespace's bindings in one complete
     file. Its API is recorded by the value/projection manifests, not by the
     initializer manifest's single whole-file row. Check it without inserting
     a second copy of those bindings into the receiving compilation unit. *)
  if kind=Initializers then Option.iter (fun expected ->
      ignore (artifact ~expect:expected ~root ~source_root ~extract Bindings scope)) expect;
  let suffix, header = match kind with
    | Source_types -> "source_type_reexports", "source-type-reexports"
    | Modules -> "module_declarations", "module-declarations"
    | Values | Bindings -> "value_reexports", "value-reexports"
    | Aliases -> "module_aliases", "module-aliases"
    | Initializers -> "binding_initializers", "binding-initializers" in
  let manifest_name="native_" ^ suffix ^ ".manifest" in
  let manifest = inside root manifest_name in
  let decode line = match kind, fields line with
    | (Source_types | Values | Bindings | Aliases), [_symbol;scope;source;source_hash;filename;digest;name;target;ordinal]
    | Modules, [_;_symbol;scope;source;source_hash;filename;digest;name;target;ordinal] ->
      {scope;source;source_hash;filename;digest;ordinal=Some ordinal;
       exported=Some {names=String.split_on_char ',' name;target}}
    | Initializers, [scope;source;source_hash;filename;digest] ->
      {scope;source;source_hash;filename;digest;ordinal=None;exported=None}
    | _ -> fail "invalid row in %s" manifest in
  let read_rows header lines = match lines with
    | h::tail when h = "soma-native-" ^ header ^ "-v1" ->
      List.filter (fun s -> s<>"") tail |> List.map decode
    | _ -> fail "unsupported manifest: %s" manifest in
  let read_manifest name header =
    (* The compiler omits empty value/projection manifests. Bindings covers
       their ordered union, including namespaces with only one of the two. *)
    if kind=Bindings && not (List.mem_assoc name (compiler_inventory root)) &&
       not (Sys.file_exists (inside root name)) then []
    else read_rows header (String.split_on_char '\n' (whole_file ~root ~extract name).contents) in
  let all=read_manifest manifest_name header in
  let all=if kind<>Bindings then all else
      all @ read_manifest "native_binding_projections.manifest" "binding-projections" in
  let rows = List.filter (fun r -> r.scope=scope) all in
  let rows=if kind<>Bindings then rows else
      let position r=match r.ordinal with Some s ->
          (try int_of_string s with Failure _ -> fail "invalid binding ordinal")
        | None -> fail "missing binding ordinal" in
      List.sort (fun a b -> Int.compare (position a) (position b)) rows in
  if rows=[] then fail "%s: no %s artifact for namespace %S" extract (kind_name kind) scope;
  (if kind<>Initializers then Option.iter (fun expected ->
      let actual=List.filter_map (fun row -> row.exported) rows in
      if actual<>expected then fail "%s: %s export contract differs for namespace %S" extract (kind_name kind) scope) expect);
  let first=List.hd rows in
  let filename=first.filename and hash=first.digest in
  List.iteri (fun i row ->
      if row.filename<>filename || row.digest<>hash then fail "%s: namespace spans multiple artifacts" manifest;
      Option.iter (fun ordinal -> if ordinal<>string_of_int i then
          fail "%s: namespace order is incomplete or changed" manifest) row.ordinal;
      ignore (verified source_root row.source row.source_hash)) rows;
  (* A namespace selects a complete artifact; it cannot discard other scopes in that file. *)
  List.iter (fun r ->
      if r.filename=filename && r.scope<>scope then fail "%s: artifact also contains another namespace" manifest) all;
  let contents=(whole_file ~root ~extract filename).contents in
  if SomaMerkle.string contents<>hash then fail "content hash differs: %s" filename;
  {identity=extract ^ "/" ^ filename; file=filename; hash; contents}
let subprocess ~root ~env program args =
  let old=Sys.getcwd () in
  Fun.protect ~finally:(fun () -> Sys.chdir old) (fun () ->
      Sys.chdir root;
      let pid=Unix.create_process_env program (Array.of_list (program::args)) env Unix.stdin Unix.stdout Unix.stderr in
      let rec wait () = try snd (Unix.waitpid [] pid) with Unix.Unix_error (Unix.EINTR,_,_) -> wait () in
      match wait () with Unix.WEXITED 0 -> ()
        | Unix.WEXITED n -> fail "%s failed (exit %d)" program n
        | _ -> fail "%s interrupted" program)
let environment root bindings ~verify ~source_only =
  let replace = ["SOMA_PROJECT_ROOT", root] @
    (match bindings with None -> [] | Some s -> ["SOMA_OCAML_BINDINGS_MODULE",s]) @
    (if verify then ["SOMA_REQUIRE_VERIFICATION","1"] else []) @
    (if source_only then ["SOMA_SOURCE_ONLY_OCAML","1"] else []) in
  let env=Array.to_list (Unix.environment ()) |> List.filter (fun s ->
      not (List.exists (fun key -> String.starts_with ~prefix:(key ^ "=") s)
        (["SOMA_BUILD_ROOT"; "SOMA_PROJECT_CACHE"; "SOMA_PROJECT_PREFIX"; "SOMA_IMPORT_STACK"] @ List.map fst replace))) in
  Array.of_list (List.map (fun (k,v) -> k ^ "=" ^ v) replace @ env)
let rec remove dir =
  match (Unix.lstat dir).Unix.st_kind with
    | Unix.S_DIR -> Array.iter (fun n -> remove (Filename.concat dir n)) (Sys.readdir dir); Unix.rmdir dir
    | _ -> Sys.remove dir
    | exception Unix.Unix_error (Unix.ENOENT,_,_) -> ()
let rec same_tree fresh previous =
  if not (Sys.file_exists previous) then false else
  match (Unix.lstat fresh).Unix.st_kind, (Unix.lstat previous).Unix.st_kind with
  | Unix.S_REG, Unix.S_REG -> read fresh=read previous
  | Unix.S_DIR, Unix.S_DIR ->
    (* Dune owns its private cache; compiler-owned files must all match. *)
    let names dir=Sys.readdir dir |> Array.to_list |> List.filter ((<>) "_build") |> List.sort String.compare in
    let xs=names fresh in xs=names previous &&
      List.for_all (fun name -> same_tree (Filename.concat fresh name) (Filename.concat previous name)) xs
  | _ -> false
let build ?(audit=false) ~compiler ~config ~config_hash p targets =
  let root=Unix.realpath (Filename.dirname config) in
  let directory=inside root p.directory in
  if audit then begin
    if not (Sys.file_exists directory) || (Unix.lstat directory).Unix.st_kind<>Unix.S_DIR then
      fail "audit requires a completed build directory: %s" directory
  end else mkdir directory;
  let lock=Unix.openfile (inside directory ".lock") [Unix.O_CREAT;Unix.O_RDWR] 0o600 in
  Fun.protect ~finally:(fun () -> Unix.close lock) (fun () ->
      Unix.lockf lock Unix.F_LOCK 0;
      let config_unchanged () = if SomaMerkle.file_hash config <> config_hash then
          fail "build configuration changed during execution; rebuild" in
      config_unchanged ();
      let sources=Hashtbl.create 16 and products=Hashtbl.create 16 in
      let publish_or_check kind file contents =
        if not audit then atomic file contents else begin
          if not (Sys.file_exists file) then fail "missing published %s: %s" kind file;
          regular file;
          if read file<>contents then fail "published %s differs from fresh checking: %s" kind file;
          false
        end in
      let publish name output pieces =
        let leaves=List.filter_map (function Data l -> Some l | Padding _ -> None) pieces in
        let extracts=List.map (fun l -> String.sub l.identity 0 (String.index l.identity '/')) leaves
          |> List.sort_uniq String.compare in
        let proofs=List.filter_map (fun extract ->
            let native,_=Hashtbl.find sources extract in
            let file=inside native "verification.toml" in
            if not (Sys.file_exists file) then None else begin regular file;
              Some (Printf.sprintf "{ extract = %s, sha256 = %s }"
                      (toml_string extract) (toml_string (SomaMerkle.file_hash file))) end) extracts in
        List.iter (fun l ->
            let extract=String.sub l.identity 0 (String.index l.identity '/') in
            let native,_=Hashtbl.find sources extract in
            ignore (verified native l.file l.hash)) leaves;
        let data=String.concat "" (List.map (function Data l -> l.contents | Padding s -> s) pieces) in
        let file=inside directory output in
        config_unchanged ();
        let changed=publish_or_check "product" file data in
        let receipt=Printf.sprintf
            "format = 1\nconfig-sha256 = %s\noutput = %s\nsha256 = %s\nparts = [%s]\nverification = [%s]\n"
            (toml_string config_hash) (toml_string output) (toml_string (SomaMerkle.string data))
            (String.concat ",\n" (List.map (function
                 | Data l -> Printf.sprintf "{ artifact = %s, sha256 = %s }" (toml_string l.identity) (toml_string l.hash)
                 | Padding s -> "{ whitespace = " ^ toml_string s ^ " }") pieces))
            (String.concat ",\n" proofs) in
        ignore (publish_or_check "receipt" (inside directory (".receipts/" ^ name ^ ".toml")) receipt);
        Hashtbl.add products name {file;pieces};
        Printf.printf "%s %s\n%!" (if changed then "built" else "unchanged") file in
      let stages=ref [] in
      Fun.protect ~finally:(fun () -> List.iter remove !stages) (fun () ->
      List.iter (fun n -> match n.action with
          | Extract e ->
            let source_root=if e.source_root="." then root else inside root e.source_root |> Unix.realpath in
            ignore (inside source_root e.file);
            let native=
                let parent=inside directory ".extract" in mkdir parent;
                (* Fresh destination: failure never replaces the previous completed extraction. *)
                let tmp=Filename.temp_file ~temp_dir:parent (n.name ^ "-") ".stage" in
                Sys.remove tmp;
                let extraction_lock=Filename.concat parent
                    ("." ^ Filename.basename tmp ^ ".soma-ocaml.lock") in
                stages := tmp :: extraction_lock :: !stages;
                subprocess ~root:source_root ~env:(environment source_root e.bindings ~verify:e.verify ~source_only:p.source_only) compiler
                  (["extract";e.file] @ e.options @ ["-o";tmp]);
                let final=inside parent n.name in
                config_unchanged ();
                (* Readers of project products share this lock. Keep the old completed
                   extraction until the new compiler invocation has succeeded. *)
                let previous=tmp ^ ".previous" in
                stages := previous :: !stages;
                if audit then () else if same_tree tmp final then remove tmp else begin
                  if Sys.file_exists final then Unix.rename final previous;
                  (try Unix.rename tmp final with exn ->
                      if Sys.file_exists previous then Unix.rename previous final; raise exn);
                  remove previous
                end;
                if audit then tmp else final in
            Hashtbl.add sources n.name (native,source_root)
          | Publish p ->
            let native,_=Hashtbl.find sources p.extract in
            publish n.name p.output [Data (whole_file ~root:native ~extract:p.extract p.file)]
          | Compose c ->
            let pieces=List.concat_map (function
                | Unit u -> (Hashtbl.find products u).pieces
                | Whitespace s -> [Padding s]
                | Artifact a ->
                  let native,source_root=Hashtbl.find sources a.extract in
                  [Data (artifact ?expect:a.expect ~root:native ~source_root ~extract:a.extract a.kind a.namespace)]) c.parts in
            let leaves=List.filter_map (function Data l -> Some l | Padding _ -> None) pieces in
            let seen=Hashtbl.create 16 in
            List.iter (fun l ->
                (* Include the physical path so two extraction aliases cannot duplicate initialization. *)
                let extract=String.sub l.identity 0 (String.index l.identity '/') in
                let native,_=Hashtbl.find sources extract in
                let key=Unix.realpath (inside native l.file) in
                if Hashtbl.mem seen key || Hashtbl.mem seen l.file then
                  fail "%s: duplicate whole artifact %s" n.name l.identity;
                Hashtbl.add seen key (); Hashtbl.add seen l.file ()) leaves;
            publish n.name c.output pieces
          | Source_map m ->
            let p=Hashtbl.find products m.unit in
            regular p.file;
            let contents=String.concat "" (List.map (function Data l -> l.contents | Padding s -> s) p.pieces) in
            if read p.file<>contents then fail "published unit changed before source map: %s" p.file;
            let receipt=inside directory (".receipts/" ^ m.unit ^ ".toml") in regular receipt;
            let map=Printf.sprintf
                "format = 1\nconfig-sha256 = %s\noutput = %s\nsha256 = %s\nunit-receipt-sha256 = %s\nparts = [%s]\n"
                (toml_string config_hash) (toml_string (String.sub p.file (String.length directory+1)
                                                       (String.length p.file-String.length directory-1)))
                (toml_string (SomaMerkle.string contents)) (toml_string (SomaMerkle.file_hash receipt))
                (String.concat ",\n" (List.map (function
                     | Data l -> Printf.sprintf "{ artifact = %s, sha256 = %s, size = %d }"
                         (toml_string l.identity) (toml_string l.hash) (String.length l.contents)
                     | Padding s -> "{ whitespace = " ^ toml_string s ^ " }") p.pieces)) in
            config_unchanged ();
            let file=inside directory m.output in
            let changed=publish_or_check "source map" file map in
            Printf.printf "%s %s\n%!" (if changed then "built" else "unchanged") file
          | Module_list m ->
            let entries=List.map (fun unit ->
                let p=Hashtbl.find products unit in
                regular p.file;
                let contents=String.concat "" (List.map (function Data l -> l.contents | Padding s -> s) p.pieces) in
                if read p.file<>contents then fail "published unit changed before module inventory: %s" p.file;
                let module_name=String.capitalize_ascii (Filename.remove_extension (Filename.basename p.file)) in
                let identifier s = String.length s>0 && (match s.[0] with 'A'..'Z' -> true | _ -> false) &&
                  String.for_all (function 'A'..'Z'|'a'..'z'|'0'..'9'|'_'|'\'' -> true | _ -> false) s in
                if not (identifier module_name) then fail "invalid OCaml module filename %s" p.file;
                let receipt=inside directory (".receipts/" ^ unit ^ ".toml") in regular receipt;
                module_name,unit,SomaMerkle.file_hash receipt) m.units in
            let names=List.map (fun (name,_,_) -> name) entries |> List.sort_uniq String.compare in
            let contents="(" ^ String.concat " " (List.map (Printf.sprintf "%S") names) ^ ")\n" in
            config_unchanged ();
            let file=inside directory m.output in
            let changed=publish_or_check "module inventory" file contents in
            let receipt=Printf.sprintf
                "format = 1\nconfig-sha256 = %s\noutput = %s\nsha256 = %s\nunits = [%s]\n"
                (toml_string config_hash) (toml_string m.output) (toml_string (SomaMerkle.string contents))
                (String.concat ",\n" (List.map (fun (_,unit,hash) ->
                     Printf.sprintf "{ unit = %s, receipt-sha256 = %s }" (toml_string unit) (toml_string hash)) entries)) in
            ignore (publish_or_check "receipt" (inside directory (".receipts/" ^ n.name ^ ".toml")) receipt);
            Printf.printf "%s %s\n%!" (if changed then "built" else "unchanged") file
          | Dune d ->
            config_unchanged ();
            if not audit then begin
              let dir=if d.directory="." then root else inside root d.directory in
              subprocess ~root:dir ~env:(Unix.environment ()) "dune"
                (["build";"--root";dir;"--profile";"release";"--"] @ d.targets)
            end)
        (order p targets)))
let help = {|Usage: soma project (plan|build|audit) [--config FILE] [--target NAME ...]
Read [build] in soma.toml (or --config). Plan validates the entire graph.
Build checks/extracts dependencies, then publishes ordered whole OCaml artifacts.
Audit freshly checks/extracts and compares products, inventories and receipts;
it replaces no published files and skips external Dune compilation.
No source text, shell commands or partial artifacts are accepted in configuration.
For an existing proof/origin pipeline, soma project assemble --help describes
native whole-product publication from a checked input inventory.
|}
let run ~compiler args =
  (* Keep the installed symlink: the CLI locates its runtime relative to it. *)
  let compiler=if Filename.is_relative compiler && String.contains compiler '/'
    then Filename.concat (Sys.getcwd ()) compiler else compiler in
  match args with
  | [] | ["--help"] | ["help"] -> print_string help
  | command::args when command="plan" || command="build" || command="audit" ->
    let rec options config targets = function
      | [] -> config,List.rev targets
      | "--config"::s::rest -> options s targets rest
      | "--target"::s::rest -> options config (s::targets) rest
      | x::_ -> fail "unknown project option %S" x in
    let config,targets=options "soma.toml" [] args in
    let config=Unix.realpath config in
    let config_hash=SomaMerkle.file_hash config in
    let p=load config in let targets=if targets=[] then p.targets else targets in
    if SomaMerkle.file_hash config <> config_hash then fail "build configuration changed while loading";
    let ordered=order p targets in
    if command="plan" then List.iter (fun n -> Printf.printf "%s: %s\n" n.name (String.concat " " (dependencies n))) ordered
    else build ~audit:(command="audit") ~compiler ~config ~config_hash p targets
  | _ -> fail "%s" help
