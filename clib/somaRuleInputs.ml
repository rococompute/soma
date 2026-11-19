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
