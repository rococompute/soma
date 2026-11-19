type status = Self | Suppressed | Selected | Orphan | Absent
type candidate = { path : string; base : string; status : status; legacy : bool * bool }
let fallback_root_name root = Filename.basename (Unix.realpath root)
let applies file = List.exists (Filename.check_suffix file) [".soma"; ".exp"; ".ext"; ".definition"]
let select ~root ~root_name ~source =
  if not (applies source) then Some [] else
  let root = Unix.realpath root in
  let dir = Unix.realpath (Filename.dirname source) in
  let folders = if dir = root then Some []
    else if String.starts_with ~prefix:(root ^ "/") dir then
      Some (String.split_on_char '/' (String.sub dir (String.length root + 1)
          (String.length dir - String.length root - 1)))
    else None in
  Option.map (fun folders ->
      let rec paths prefix = function
        | [] -> []
        | x :: rest -> let p = prefix ^ x in (p ^ "/" ^ x) :: paths (p ^ "/") rest in
      let self = Filename.concat dir (Filename.remove_extension (Filename.basename source)) in
      List.map (fun path ->
          let base = Filename.concat root path in
          let status = if base = self then Self
            else if Sys.file_exists (base ^ ".soma") then Suppressed
            else if Sys.file_exists (base ^ ".ext") then Selected
            else if Sys.file_exists (base ^ ".exp") then Orphan
            else Absent in
          {path; base; status; legacy = Sys.file_exists (base ^ ".lang"), Sys.file_exists (base ^ ".proof")})
        (root_name :: paths "" folders)) folders
let fingerprint selection =
  let text = match selection with
    | None -> "outside\n"
    | Some rows -> String.concat "" (List.map (fun row ->
        let status = match row.status with Self -> "self" | Suppressed -> "suppressed"
          | Selected -> "selected" | Orphan -> "orphan" | Absent -> "absent" in
        let lang, proof = row.legacy in
        Printf.sprintf "%S %s %b %b\n" row.path status lang proof) rows) in
  SomaMerkle.string ("soma-folder-rules 1\000" ^ text)

(* The compiler validates the complete project separately. This projection
   shares the TOML grammar and accepts exactly its project-name value shape. *)
let configured_root_name root =
  let file = Filename.concat root "soma.toml" in
  if not (Sys.file_exists file) then fallback_root_name root else
  let contents = In_channel.with_open_bin file In_channel.input_all in
  let table = SomaToml.parse contents in
  match List.assoc_opt "project" table with
  | Some { SomaToml.value = Table project; _ } ->
    (match List.assoc_opt "name" project with
     | Some { SomaToml.value = String name; _ }
       when String.length name > 0 && String.length name <= 64 &&
            name.[0] >= 'a' && name.[0] <= 'z' &&
            String.for_all (function 'a'..'z' | '0'..'9' | '_' -> true | _ -> false) name -> name
     | _ -> failwith "project name is not a string")
  | _ -> failwith "project is not a table"

let source_family source =
  let base = Filename.remove_extension source in
  List.map (fun suffix -> base ^ suffix)
    [".soma"; ".ext"; ".exp"; ".definition"; ".wasm"; ".ml"; ".mli"; ".lean"; ".lang"; ".proof"]

let candidate_paths ~root ~root_name ~source =
  let rules = match select ~root ~root_name ~source with
    | None -> []
    | Some candidates -> List.concat_map (fun candidate ->
        List.map (fun suffix -> candidate.base ^ suffix)
          [".soma"; ".ext"; ".exp"; ".lang"; ".proof"]) candidates in
  List.sort_uniq compare (Filename.concat root "soma.toml" :: source_family source @ rules)
