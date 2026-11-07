(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: [soma diff OLD NEW]: what changed between two versions of a project,
   by the hashes of vernac/somaHash.ml. A version number says what its author
   meant, and a commit which bytes it is. This says what the kernel checked: a
   comment changes nothing, another proof of a statement changes no statement,
   and a theorem whose statement is the same and whose proof began to rest on an
   axiom is reported as that, which no compilation of what uses it can show.

   Each version is compiled as a dependency, of a project made for the purpose
   in a temporary folder, one file at a time, so that a file that does not
   compile is reported and the others are still compared. So it is checked and
   not run (vernac/somaImport.ml), and nothing is written to it. Both are hashed
   here and now, so a hash need not mean the same on another machine.

   It reports and does not judge: that a definition was edited may be the point
   of the release. What is not in the kernel's terms is not compared: notations,
   instances, hints and tactics. *)

open Pp

open SomaProject

let error msg = CErrors.user_err msg

type version_source =
  | Tag of string * dependency_path * version      (* as written *)
  | Folder of string

let parse_side spec =
  match String.index_opt spec '@' with
  | Some i ->
    let written = String.sub spec 0 i in
    let v = String.sub spec (i + 1) (String.length spec - i - 1) in
    let v = if String.starts_with ~prefix:"v" v then String.sub v 1 (String.length v - 1) else v in
    let path = match parse_path written with
      | Ok p -> p
      | Error why -> error (str why) in
    let version = match parse_version v with
      | Ok parsed -> parsed
      | Error why -> error (str (Printf.sprintf "%S is no semantic version (https://semver.org): %s" v why)) in
    (match check_dependency_version ~written path version with
     | Ok () -> ()
     | Error why -> error (str why));
    Tag (written, path, version)
  | None ->
    if Sys.file_exists (Filename.concat spec file_name) then Folder (CUnix.canonical_path_name spec)
    else
      error (str spec ++ str " is no version of a project: a tag is owner/repo@1.2.3, and a folder has a " ++
             str file_name ++ str ".")

let shown = function
  | Tag (written, _, version) -> written ^ " " ^ version_to_string version
  | Folder dir -> Filename.basename dir

(* * What a version has *)

let is_ident s =
  s <> "" &&
  (match s.[0] with 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false) &&
  String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true | _ -> false) s

(* What can be imported: X/Y, of X/Y.soma, X/Y.lang, X/Y.definition or
   X/Y.wasm. A folder that is no name cannot be imported, nor what is in it;
   nor is a project inside this one, with its own soma.toml, a part of it. *)
let importable root =
  let exts = [".soma"; ".lang"; ".definition"; ".wasm"] in
  let rec walk rel =
    let dir = if rel = "" then root else Filename.concat root rel in
    List.concat_map (fun e ->
        let path = if rel = "" then e else rel ^ "/" ^ e in
        let full = Filename.concat dir e in
        if Sys.is_directory full then
          if is_ident e && not (Sys.file_exists (Filename.concat full file_name)) then walk path else []
        else if List.exists (Filename.check_suffix e) exts && is_ident (Filename.remove_extension e) then
          [if rel = "" then Filename.remove_extension e else rel ^ "/" ^ Filename.remove_extension e]
        else [])
      (List.sort compare (Array.to_list (Sys.readdir dir))) in
  List.sort_uniq compare (walk "")

type definition = {
  name : string;
  contract : string;
  witness : string;
  shape : string;
  assumes : string list;
}

let starts prefix s = String.starts_with ~prefix s
let without prefix s =
  if starts prefix s then String.sub s (String.length prefix) (String.length s - String.length prefix) else s

let remove_tree d = ignore (Sys.command (Filename.quote_command "rm" ["-rf"; d]))

(* The environment of a compilation of soma diff's own: none of Soma's own
   variables, but what asks for the hashes *)
let environment hashes =
  Array.of_list (
    List.filter (fun v -> not (starts "SOMA_" v) || starts "SOMA_OCAML_SWITCH=" v)
      (Array.to_list (Unix.environment ()))
    @ ["SOMA_HASH=" ^ hashes; "SOMA_HASH_FIELDS=1"; "SOMA_MIRAGE_BUILD=0"; "SOMA_OCAML_BUILD=0"])

let compile_quietly ~dir ~env main =
  let log = Filename.concat dir "compile.log" in
  let out = Unix.openfile log [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o644 in
  let vo = Filename.concat dir "main.vo" in
  let prog = Boot.Env.self in
  let pid = Unix.create_process_env prog [| prog; "--kind=compile"; main; "-o"; vo |] env Unix.stdin out out in
  Unix.close out;
  let rec wait () = try snd (Unix.waitpid [] pid) with Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
  let ok = wait () = Unix.WEXITED 0 in
  ok, log

(* What a compilation said first went wrong: what comes after it is that what
   imports it does not compile, as far as the file made for the purpose *)
let first_error log =
  let lines = List.filter (fun l -> not (starts "Compiling " l))
      (String.split_on_char '\n' (In_channel.with_open_bin log In_channel.input_all)) in
  let rec until_blank = function
    | "" :: _ | [] -> []
    | l :: rest -> l :: until_blank rest in
  let rec skip_blank = function
    | "" :: rest -> skip_blank rest
    | l -> l in
  String.concat "\n" (until_blank (skip_blank lines))

(* the definitions of a version, and the files of it that do not compile, with
   what was said of them *)
let definitions side =
  let root, name, key = match side with
    | Tag (written, path, version) ->
      let p = SomaDeps.fetched path version in
      p.root, p.name, Printf.sprintf "%S = %S" written (version_to_string version)
    | Folder dir ->
      let p = load dir in
      p.root, p.name, (* a literal string, as a folder's name may have anything in it *)
      Printf.sprintf "\"local/%s\" = { path = '%s' }" p.name dir in
  let tmp = Filename.temp_file "soma-diff" "" in
  Sys.remove tmp;
  Unix.mkdir tmp 0o755;
  let tmp = CUnix.canonical_path_name tmp in
  Fun.protect ~finally:(fun () -> remove_tree tmp) (fun () ->
      Out_channel.with_open_bin (Filename.concat tmp file_name) (fun oc ->
          Printf.fprintf oc "[project]\nname = \"soma_diff\"\nversion = \"0.0.0\"\n\n[dependencies]\n%s\n" key);
      let hashes = Filename.concat tmp "hashes" in
      let env = environment hashes in
      let main = Filename.concat tmp "main.soma" in
      let found = Hashtbl.create 97 in
      let failures = ref [] in
      let prefix = name ^ "." in
      List.iter (fun path ->
          Out_channel.with_open_bin main (fun oc ->
              Printf.fprintf oc "Import %s.\n"
                (name ^ "." ^ String.map (function '/' -> '.' | c -> c) path));
          let ok, log = compile_quietly ~dir:tmp ~env main in
          if ok then
            List.iter (fun l -> match String.split_on_char '\t' l with
                | n :: contract :: witness :: shape :: assumes when starts prefix n ->
                  let short = without prefix in
                  Hashtbl.replace found (short n)
                    { name = short n; contract; witness; shape;
                      assumes = List.sort compare (List.map short assumes) }
                | _ -> ())
              (SomaOpam.read_lines hashes)
          else failures := (path, first_error log) :: !failures)
        (importable root);
      name, Hashtbl.fold (fun _ d acc -> d :: acc) found [], List.rev !failures)

(* * The report *)

let run args =
  let old_spec, new_spec = match args with
    | [a; b] -> a, b
    | _ -> error (str "soma diff compares two versions: soma diff owner/repo@1.2.0 owner/repo@1.3.0, or two folders.") in
  let old_side = parse_side old_spec and new_side = parse_side new_spec in
  let old_name, old_defs, old_failures = definitions old_side in
  let new_name, new_defs, new_failures = definitions new_side in
  let find defs n = List.find_opt (fun d -> d.name = n) defs in
  let sorted = List.sort (fun a b -> compare a.name b.name) in
  let both = List.filter_map (fun o -> Option.map (fun n -> o, n) (find new_defs o.name)) (sorted old_defs) in
  let gone = List.filter (fun o -> find new_defs o.name = None) (sorted old_defs) in
  let came = List.filter (fun n -> find old_defs n.name = None) (sorted new_defs) in
  (* what a file that does not compile on one side has on the other is not gone
     or new: it is not compared, and said to be *)
  let in_failed n =
    List.exists (fun (path, _) -> starts (String.map (function '/' -> '.' | c -> c) path ^ ".") n)
      (old_failures @ new_failures) in
  let gone = List.filter (fun o -> not (in_failed o.name)) gone in
  let came = List.filter (fun n -> not (in_failed n.name)) came in
  (* a name gone, and another come with its contract: where it says what it did *)
  let moved = List.filter_map (fun o ->
      Option.map (fun n -> o, n) (List.find_opt (fun n -> n.contract = o.contract) came)) gone in
  let gone = List.filter (fun o -> not (List.exists (fun (m, _) -> m.name = o.name) moved)) gone in
  let came = List.filter (fun n -> not (List.exists (fun (_, m) -> m.name = n.name) moved)) came in
  let minus a b = List.filter (fun x -> not (List.mem x b)) a in
  let unchanged = List.filter (fun (o, n) -> o.contract = n.contract && o.witness = n.witness) both in
  let proofs = List.filter (fun (o, n) -> o.contract = n.contract && o.witness <> n.witness) both in
  let changed = List.filter (fun (o, n) -> o.contract <> n.contract) both in
  let edited = List.filter (fun (o, n) -> o.shape <> n.shape) changed in
  let same_text = List.filter (fun (o, n) -> o.shape = n.shape) changed in
  let weaker = List.filter (fun (o, n) -> minus n.assumes o.assumes <> []) same_text in
  let stronger = List.filter (fun (o, n) -> minus n.assumes o.assumes = [] && minus o.assumes n.assumes <> []) same_text in
  let beneath = List.filter (fun (o, n) -> o.assumes = n.assumes) same_text in
  let say = print_string in
  let section title lines =
    if lines <> [] then begin
      say (Printf.sprintf "\n%s\n" title);
      List.iter (fun l -> say ("  " ^ l ^ "\n")) lines
    end in
  let more (o, n) = match minus n.assumes o.assumes with
    | [] -> ""
    | added -> ", now assumes " ^ String.concat ", " added in
  say (Printf.sprintf "%s -> %s\n" (shown old_side) (shown new_side));
  if old_name <> new_name then say (Printf.sprintf "The project was %s, and is %s.\n" old_name new_name);
  section "The same, and resting on more (what uses it still builds):"
    (List.map (fun (o, n) -> n.name ^ more (o, n)) weaker);
  section "Edited:" (List.map (fun (o, n) -> n.name ^ more (o, n)) edited);
  section "Changed by what they use:" (List.map (fun (_, n) -> n.name) beneath);
  section "The same, and resting on less:"
    (List.map (fun (o, n) -> n.name ^ ", no longer assumes " ^ String.concat ", " (minus o.assumes n.assumes)) stronger);
  section "Another proof, or one beneath it, of the same statement:" (List.map (fun (_, n) -> n.name) proofs);
  section "Moved or renamed:" (List.map (fun (o, n) -> o.name ^ " -> " ^ n.name) moved);
  section "Added:" (List.map (fun n -> n.name ^ (match minus n.assumes [n.name] with
      | [] -> "" | a -> ", assumes " ^ String.concat ", " a)) came);
  section "Removed:" (List.map (fun o -> o.name) gone);
  let failed side failures =
    section (Printf.sprintf "Not compared, as it does not compile in %s:" (shown side))
      (List.map (fun (path, tail) ->
           path ^ "\n" ^ String.concat "\n" (List.map (fun l -> "      " ^ l)
                                               (List.filter (( <> ) "") (String.split_on_char '\n' tail))))
          failures) in
  failed old_side old_failures;
  failed new_side new_failures;
  say (Printf.sprintf "\n%d unchanged. Notations, instances, hints and tactics are not compared.\n"
         (List.length unchanged))
