type kind = Source_types | Modules | Values | Bindings | Aliases | Initializers
type export = { names : string list; target : string }
type abi_contract = { symbol : string; sha256 : string }
type part = Artifact of { extract : string; kind : kind; namespace : string; expect : export list option }
          | Unit of string
          | Whitespace of string
type action = Extract of { file : string; source_root : string; options : string list;
                           bindings : string option; verify : bool; abi : abi_contract list }
            | Publish of { extract : string; file : string; output : string }
            | Compose of { output : string; parts : part list }
            | Module_list of { output : string; units : string list }
            | Source_map of { output : string; unit : string }
            | Dune of { directory : string; targets : string list }
type node = { name : string; needs : string list; action : action }
type t = { directory : string; targets : string list; nodes : node list; source_only : bool }
exception Error of string
let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt
let kind_name = function Source_types -> "source-types" | Modules -> "modules"
  | Values -> "values" | Bindings -> "bindings" | Aliases -> "aliases" | Initializers -> "initializers"
let relative_path s =
  s <> "" && Filename.is_relative s && not (String.contains s '\000') &&
  not (String.contains s '\\') &&
  List.for_all (fun p -> p <> "" && p <> "." && p <> "..") (String.split_on_char '/' s)
let identifier s = s <> "" && String.for_all (function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' -> true | _ -> false) s
let namespace s = s <> "" && List.for_all identifier (String.split_on_char '.' s)
let table where e = match e.SomaToml.value with Table t -> t
  | _ -> error "line %d: %s must be a table" e.line where
let keys where allowed t = List.iter (fun (k, e) ->
    if not (List.mem k allowed) then error "line %d: unknown %s key %S" e.SomaToml.line where k) t
let required where k t = match List.assoc_opt k t with Some e -> e
  | None -> error "%s requires %s" where k
let string where e = match e.SomaToml.value with String s -> s
  | _ -> error "line %d: %s must be a string" e.line where
let strings where e = match e.SomaToml.value with Array xs ->
    List.map (fun v -> string where {e with value=v}) xs
  | _ -> error "line %d: %s must be an array of strings" e.line where
let get_string where k t = string (where ^ "." ^ k) (required where k t)
let optional_string where k t default = match List.assoc_opt k t with
  | None -> default | Some e -> string (where ^ "." ^ k) e
let optional_strings where k t = match List.assoc_opt k t with
  | None -> [] | Some e -> strings (where ^ "." ^ k) e
let optional_bool where k t = match List.assoc_opt k t with
  | None -> false | Some {SomaToml.value=Bool b;_} -> b
  | Some e -> error "line %d: %s.%s must be a boolean" e.SomaToml.line where k
let export_contract where t = match List.assoc_opt "expect" t with
  | None -> None
  | Some e ->
    let exported_name s = String.length s>0 &&
      (match s.[0] with 'a'..'z'|'A'..'Z'|'_' -> true | _ -> false) &&
      String.for_all (function 'a'..'z'|'A'..'Z'|'0'..'9'|'_'|'\'' -> true | _ -> false) s in
    let exports=match e.SomaToml.value with
      | Array xs when xs<>[] -> List.map (fun value ->
          let row=table (where ^ ".expect") {e with value} in
          keys where ["names";"target"] row;
          let names=strings where (required where "names" row) in
          if names=[] || not (List.for_all exported_name names) then
            error "%s: expected export names must be nonempty OCaml identifiers" where;
          let target=get_string where "target" row in
          if String.exists (fun c -> Char.code c<32 || Char.code c=127) target then
            error "%s: invalid expected export target" where;
          {names;target}) xs
      | _ -> error "%s.expect must be a nonempty array of export tables" where in
    let names=List.concat_map (fun e -> e.names) exports in
    if List.length names<>List.length (List.sort_uniq String.compare names) then
      error "%s: duplicate expected export name" where;
    Some exports
let path where s = if not (relative_path s) then error "%s: expected a relative path without . or ..: %S" where s; s
let abi_contracts where t = match List.assoc_opt "abi" t with
  | None -> []
  | Some e ->
    let contracts=match e.SomaToml.value with
      | Array xs when xs<>[] -> List.map (fun value ->
          let row=table (where ^ ".abi") {e with value} in
          keys where ["symbol";"sha256"] row;
          let symbol=get_string where "symbol" row and sha256=get_string where "sha256" row in
          if not (namespace symbol) then error "%s: invalid ABI contract symbol %S" where symbol;
          if not (SomaMerkle.valid_hash sha256) then error "%s: invalid ABI contract SHA-256" where;
          {symbol;sha256}) xs
      | _ -> error "%s.abi must be a nonempty array of ABI contract tables" where in
    let names=List.map (fun c -> c.symbol) contracts in
    if List.length names<>List.length (List.sort_uniq String.compare names) then
      error "%s: duplicate ABI contract symbol" where;
    contracts
let dependencies n = List.sort_uniq String.compare (n.needs @ match n.action with
    | Extract _ | Dune _ -> []
    | Publish p -> [p.extract]
    | Module_list m -> m.units
    | Source_map m -> [m.unit]
    | Compose c -> List.filter_map (function Artifact a -> Some a.extract | Unit s -> Some s | Whitespace _ -> None) c.parts)
let order p targets =
  let visiting = Hashtbl.create 16 and done_ = Hashtbl.create 16 in
  let result = ref [] in
  let rec visit chain name =
    if Hashtbl.mem visiting name then error "build dependency cycle: %s" (String.concat " -> " (List.rev (name :: chain)));
    if not (Hashtbl.mem done_ name) then begin
      let n = match List.find_opt (fun n -> n.name = name) p.nodes with
        | Some n -> n | None -> error "unknown build target %S" name in
      Hashtbl.add visiting name ();
      List.iter (visit (name :: chain)) (dependencies n);
      Hashtbl.remove visiting name; Hashtbl.add done_ name (); result := n :: !result
    end in
  List.iter (visit []) targets; List.rev !result
let parse toml = match List.assoc_opt "build" toml with
  | None -> None
  | Some e ->
    let b = table "build" e in
    keys "build" ["directory"; "targets"; "extract"; "publish"; "unit"; "module-list"; "source-map"; "dune"; "source-only"] b;
    let source_only=optional_bool "build" "source-only" b in
    let directory = path "build.directory" (optional_string "build" "directory" b ".soma-build") in
    let parse_group group f = match List.assoc_opt group b with
      | None -> [] | Some e -> table ("build." ^ group) e |> List.map (fun (name, e) ->
        if not (identifier name) then error "invalid build target name %S" name;
        let where = "build." ^ group ^ "." ^ name in
        let t = table where e in
        let action = f where t in
        {name; needs=optional_strings where "needs" t; action}) in
    let extracts = parse_group "extract" (fun where t ->
        keys where ["file"; "source-root"; "options"; "bindings"; "needs"; "verify"; "abi"] t;
        let file = path where (get_string where "file" t) in
        let source_root = optional_string where "source-root" t "." in
        if source_root <> "." then ignore (path where source_root);
        let options = optional_strings where "options" t in
        (* Output locations and root overrides belong to the graph, never to argv. *)
        List.iter (fun s -> if not (List.mem s ["-no-soma-prelude"; "--no-module-cache"]) then
            error "%s: unsupported extraction option %S" where s) options;
        let bindings = Option.map (string where) (List.assoc_opt "bindings" t) in
        Option.iter (fun s -> if not (identifier s) then error "%s: invalid bindings module" where) bindings;
        let verify=optional_bool where "verify" t in
        let abi=abi_contracts where t in
        Extract {file; source_root; options; bindings; verify; abi}) in
    let publications = parse_group "publish" (fun where t ->
        keys where ["extract"; "file"; "output"; "needs"] t;
        let extract=get_string where "extract" t in
        let file=path where (get_string where "file" t) in
        let output=path where (get_string where "output" t) in
        if (Filename.check_suffix output ".ml" || Filename.check_suffix output ".mli") &&
           not (List.exists (Filename.check_suffix file)
                  [".ml";".mli";".assembly";".assembly-interface";".declaration";".declaration-interface";".exports"]) then
          error "%s: an OCaml output requires a complete compiler source artifact" where;
        Publish {extract;file;output}) in
    let units = parse_group "unit" (fun where t ->
        keys where ["output"; "parts"; "needs"] t;
        let output = path where (get_string where "output" t) in
        if not (Filename.check_suffix output ".ml" || Filename.check_suffix output ".mli") then
          error "%s: output must be an OCaml .ml or .mli unit" where;
        let parts = match (required where "parts" t).value with
          | SomaToml.Array xs when xs <> [] -> List.map (fun value ->
              let p = table (where ^ ".parts") {e with value} in
              if List.mem_assoc "unit" p then begin
                keys where ["unit"] p; Unit (get_string where "unit" p)
              end else if List.mem_assoc "whitespace" p then begin
                keys where ["whitespace"] p;
                let padding=get_string where "whitespace" p in
                if not (String.for_all (function ' '|'\t'|'\r'|'\n' -> true | _ -> false) padding) then
                  error "%s: whitespace cannot contain source text" where;
                Whitespace padding
              end else begin
                keys where ["extract"; "kind"; "namespace"; "expect"] p;
                let kind = match get_string where "kind" p with
                  | "source-types" -> Source_types | "modules" -> Modules | "values" -> Values | "bindings" -> Bindings
                  | "aliases" -> Aliases | "initializers" -> Initializers
                  | k -> error "%s: unknown artifact kind %S" where k in
                let scope = get_string where "namespace" p in
                if not (namespace scope) then error "%s: invalid namespace %S" where scope;
                let expect=export_contract where p in
                Artifact {extract=get_string where "extract" p; kind; namespace=scope;expect}
              end) xs
          | _ -> error "%s.parts must be a nonempty array of tables" where in
        Compose {output; parts}) in
    let inventories = parse_group "module-list" (fun where t ->
        keys where ["output"; "units"; "needs"] t;
        let output=path where (get_string where "output" t) in
        if not (Filename.check_suffix output ".sexp") then error "%s: output must be a .sexp file" where;
        let units=optional_strings where "units" t in
        if units=[] then error "%s: units must be nonempty" where;
        Module_list {output;units}) in
    let maps = parse_group "source-map" (fun where t ->
        keys where ["output"; "unit"; "needs"] t;
        let output=path where (get_string where "output" t) in
        if not (Filename.check_suffix output ".toml") then error "%s: output must be a .toml file" where;
        Source_map {output;unit=get_string where "unit" t}) in
    let dune = parse_group "dune" (fun where t ->
        keys where ["directory"; "targets"; "needs"] t;
        let directory=optional_string where "directory" t "." in
        if directory <> "." then ignore (path where directory);
        let targets=optional_strings where "targets" t in
        if targets=[] then error "%s requires nonempty targets" where;
        List.iter (fun s -> ignore (path where s)) targets;
        Dune {directory;targets}) in
    let nodes = extracts @ publications @ units @ inventories @ maps @ dune in
    let seen = Hashtbl.create 16 and outputs = Hashtbl.create 16 in
    List.iter (fun n ->
        if Hashtbl.mem seen n.name then error "duplicate build target %S" n.name;
        Hashtbl.add seen n.name ();
        let output=match n.action with Extract _ | Dune _ -> None
          | Publish p -> Some p.output | Compose c -> Some c.output | Module_list m -> Some m.output
          | Source_map m -> Some m.output in
        Option.iter (fun output ->
          Hashtbl.iter (fun previous _ ->
              let prefix a b = String.starts_with ~prefix:(a ^ "/") b in
              if output = previous || prefix output previous || prefix previous output then
                error "conflicting build outputs %S and %S" previous output) outputs;
          if List.mem (List.hd (String.split_on_char '/' output)) [".extract"; ".receipts"; ".lock"] then
            error "reserved build output %S" output;
          Hashtbl.add outputs output ()) output) nodes;
    let targets = optional_strings "build" "targets" b in
    let targets = if targets = [] then List.map (fun n -> n.name) (publications @ units @ inventories @ maps @ dune) else targets in
    let p = {directory; targets; nodes; source_only} in
    if source_only then List.iter (fun n -> match n.action with
        | Extract e when not e.verify -> error "%s: source-only builds require verify=true for every extraction" n.name
        | _ -> ()) nodes;
    ignore (order p (List.map (fun n -> n.name) nodes));
    ignore (order p targets);
    let extraction name reference = match (List.find (fun n -> n.name=reference) nodes).action with
      | Extract _ -> () | _ -> error "%s: artifact reference %s is not an extraction" name reference in
    let ocaml_unit name reference = match (List.find (fun n -> n.name=reference) nodes).action with
      | Compose _ -> ()
      | Publish p when Filename.check_suffix p.output ".ml" || Filename.check_suffix p.output ".mli" -> ()
      | _ -> error "%s: unit reference %s is not an OCaml unit" name reference in
    List.iter (fun n -> match n.action with Extract _ | Dune _ -> ()
        | Publish p -> extraction n.name p.extract
        | Module_list m -> List.iter (ocaml_unit n.name) m.units
        | Source_map m -> ocaml_unit n.name m.unit
        | Compose c ->
        List.iter (function Whitespace _ -> () | Artifact a ->
            extraction n.name a.extract
          | Unit u -> ocaml_unit n.name u) c.parts) nodes;
    Some p
let load file =
  let ic = open_in_bin file in
  let text = Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> really_input_string ic (in_channel_length ic)) in
  let toml = try SomaToml.parse text with SomaToml.Error (line,s) -> error "%s:%d: %s" file line s in
  match parse toml with Some p -> p | None -> error "%s: missing [build] table" file
