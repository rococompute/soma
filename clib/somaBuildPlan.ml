type kind = Source_types | Modules | Values | Bindings | Aliases | Initializers
type part = Artifact of { extract : string; kind : kind; namespace : string }
          | Unit of string
type action = Extract of { file : string; source_root : string; options : string list;
                           bindings : string option }
            | Compose of { output : string; parts : part list }
            | Dune of { directory : string; targets : string list }
type node = { name : string; needs : string list; action : action }
type t = { directory : string; targets : string list; nodes : node list }
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
let path where s = if not (relative_path s) then error "%s: expected a relative path without . or ..: %S" where s; s
let dependencies n = List.sort_uniq String.compare (n.needs @ match n.action with
    | Extract _ | Dune _ -> []
    | Compose c -> List.map (function Artifact a -> a.extract | Unit s -> s) c.parts)
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
    keys "build" ["directory"; "targets"; "extract"; "unit"; "dune"] b;
    let directory = path "build.directory" (optional_string "build" "directory" b ".soma-build") in
    let parse_group group f = match List.assoc_opt group b with
      | None -> [] | Some e -> table ("build." ^ group) e |> List.map (fun (name, e) ->
        if not (identifier name) then error "invalid build target name %S" name;
        let where = "build." ^ group ^ "." ^ name in
        let t = table where e in
        let action = f where t in
        {name; needs=optional_strings where "needs" t; action}) in
    let extracts = parse_group "extract" (fun where t ->
        keys where ["file"; "source-root"; "options"; "bindings"; "needs"] t;
        let file = path where (get_string where "file" t) in
        let source_root = optional_string where "source-root" t "." in
        if source_root <> "." then ignore (path where source_root);
        let options = optional_strings where "options" t in
        (* Output locations and root overrides belong to the graph, never to argv. *)
        List.iter (fun s -> if not (List.mem s ["-no-soma-prelude"; "--no-module-cache"]) then
            error "%s: unsupported extraction option %S" where s) options;
        let bindings = Option.map (string where) (List.assoc_opt "bindings" t) in
        Option.iter (fun s -> if not (identifier s) then error "%s: invalid bindings module" where) bindings;
        Extract {file; source_root; options; bindings}) in
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
              end else begin
                keys where ["extract"; "kind"; "namespace"] p;
                let kind = match get_string where "kind" p with
                  | "source-types" -> Source_types | "modules" -> Modules | "values" -> Values | "bindings" -> Bindings
                  | "aliases" -> Aliases | "initializers" -> Initializers
                  | k -> error "%s: unknown artifact kind %S" where k in
                let scope = get_string where "namespace" p in
                if not (namespace scope) then error "%s: invalid namespace %S" where scope;
                Artifact {extract=get_string where "extract" p; kind; namespace=scope}
              end) xs
          | _ -> error "%s.parts must be a nonempty array of tables" where in
        Compose {output; parts}) in
    let dune = parse_group "dune" (fun where t ->
        keys where ["directory"; "targets"; "needs"] t;
        let directory=optional_string where "directory" t "." in
        if directory <> "." then ignore (path where directory);
        let targets=optional_strings where "targets" t in
        if targets=[] then error "%s requires nonempty targets" where;
        List.iter (fun s -> ignore (path where s)) targets;
        Dune {directory;targets}) in
    let nodes = extracts @ units @ dune in
    let seen = Hashtbl.create 16 and outputs = Hashtbl.create 16 in
    List.iter (fun n ->
        if Hashtbl.mem seen n.name then error "duplicate build target %S" n.name;
        Hashtbl.add seen n.name ();
        match n.action with Extract _ | Dune _ -> () | Compose c ->
          Hashtbl.iter (fun previous _ ->
              let prefix a b = String.starts_with ~prefix:(a ^ "/") b in
              if c.output = previous || prefix c.output previous || prefix previous c.output then
                error "conflicting build outputs %S and %S" previous c.output) outputs;
          if List.mem (List.hd (String.split_on_char '/' c.output)) [".extract"; ".receipts"; ".lock"] then
            error "reserved build output %S" c.output;
          Hashtbl.add outputs c.output ()) nodes;
    let targets = optional_strings "build" "targets" b in
    let targets = if targets = [] then List.map (fun n -> n.name) (units @ dune) else targets in
    let p = {directory; targets; nodes} in
    ignore (order p (List.map (fun n -> n.name) nodes));
    ignore (order p targets);
    List.iter (fun n -> match n.action with Extract _ | Dune _ -> () | Compose c ->
        List.iter (function Artifact a ->
            (match (List.find (fun n -> n.name=a.extract) nodes).action with
             | Extract _ -> () | Compose _ | Dune _ -> error "%s: artifact reference %s is not an extraction" n.name a.extract)
          | Unit u -> match (List.find (fun n -> n.name=u) nodes).action with
            | Compose _ -> () | Extract _ | Dune _ -> error "%s: unit reference %s is not a unit" n.name u) c.parts) nodes;
    Some p
let load file =
  let ic = open_in_bin file in
  let text = Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> really_input_string ic (in_channel_length ic)) in
  let toml = try SomaToml.parse text with SomaToml.Error (line,s) -> error "%s:%d: %s" file line s in
  match parse toml with Some p -> p | None -> error "%s: missing [build] table" file
