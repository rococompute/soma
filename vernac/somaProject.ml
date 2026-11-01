(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: a project's soma.toml.

     [project]
     name = "rocq_stdpp"
     version = "0.1.0"
     description = "A shop's stock, kept in stdpp's finite maps"

   The folder of soma.toml is the project's root: [Import X] is its
   X.soma, from any of its files, and what is compiled goes to its
   .soma-cache. Without soma.toml, the root is the folder of the program
   being built, as before.

   The name is what the project will be known by to other projects, in
   Rocq and OCaml, and to opam: lowercase letters, digits and _, as Rocq's
   and OCaml's names do not take -. The version is a semantic version,
   the project's own. Every key and table is checked: one Soma does not
   know is an error rather than ignored, until Soma knows it. *)

let file_name = "soma.toml"

(* * Semantic versions (https://semver.org, 2.0.0) *)

type version = {
  major : int;
  minor : int;
  patch : int;
  pre : string list;
  build : string list;
}

let version_to_string v =
  Printf.sprintf "%d.%d.%d%s%s" v.major v.minor v.patch
    (if v.pre = [] then "" else "-" ^ String.concat "." v.pre)
    (if v.build = [] then "" else "+" ^ String.concat "." v.build)

let is_digit = function '0'..'9' -> true | _ -> false
let is_ident_char c = is_digit c || (match c with 'a'..'z' | 'A'..'Z' | '-' -> true | _ -> false)

let numeric s = s <> "" && String.for_all is_digit s

(* no leading zero, unless it is 0 *)
let leading_zero s = String.length s > 1 && s.[0] = '0'

let parse_version s =
  let ( let* ) = Result.bind in
  let split_at c s = match String.index_opt s c with
    | Some i -> String.sub s 0 i, Some (String.sub s (i + 1) (String.length s - i - 1))
    | None -> s, None in
  let s', build = split_at '+' s in
  let core, pre = split_at '-' s' in
  let identifiers what = function
    | None -> Ok []
    | Some p ->
      let ids = String.split_on_char '.' p in
      if List.exists (fun i -> i = "" || not (String.for_all is_ident_char i)) ids then
        Error (Printf.sprintf "its %s, %s, is identifiers of letters, digits and -, separated by ." what p)
      else if what = "pre-release" && List.exists (fun i -> numeric i && leading_zero i) ids then
        Error (Printf.sprintf "its pre-release, %s, has a number beginning with 0" p)
      else Ok ids in
  let* numbers = match String.split_on_char '.' core with
    | [a; b; c] when List.for_all numeric [a; b; c] ->
      if List.exists leading_zero [a; b; c] then Error "its numbers do not begin with 0"
      else (match List.map int_of_string_opt [a; b; c] with
          | [Some a; Some b; Some c] -> Ok (a, b, c)
          | _ -> Error "its numbers are too large")
    | _ -> Error "it is MAJOR.MINOR.PATCH, three numbers, as 0.1.0 or 1.2.3" in
  let* pre = identifiers "pre-release" pre in
  let* build = identifiers "build metadata" build in
  let major, minor, patch = numbers in
  Ok { major; minor; patch; pre; build }

(* * soma.toml *)

type t = {
  root : string;
  name : string;
  description : string option;
  version : version;
}

let rec find_root dir =
  if Sys.file_exists (Filename.concat dir file_name) then Some dir
  else let up = Filename.dirname dir in
    if up = dir then None else find_root up

let valid_name n =
  n <> "" && String.length n <= 64 &&
  (match n.[0] with 'a'..'z' -> true | _ -> false) &&
  String.for_all (function 'a'..'z' | '0'..'9' | '_' -> true | _ -> false) n

(* a name like [s], for messages *)
let name_like s =
  let s = String.map (function
      | 'a'..'z' | '0'..'9' | '_' as c -> c
      | 'A'..'Z' as c -> Char.lowercase_ascii c
      | _ -> '_') s in
  let s = if s <> "" && (match s.[0] with 'a'..'z' -> true | _ -> false) then s else "p" ^ s in
  if String.length s > 64 then String.sub s 0 64 else s

let read_file f = In_channel.with_open_bin f In_channel.input_all

let example root =
  Printf.sprintf "[project]\nname = %S\nversion = \"0.1.0\"\ndescription = \"What the project is\"\n"
    (name_like (Filename.basename root))

let keys = ["name", "the project's name"; "version", "its semantic version";
            "description", "what it is, in a sentence"]

let load_uncached root =
  let file = Filename.concat root file_name in
  let error line fmt =
    Printf.ksprintf (fun m ->
        CErrors.user_err Pp.(str file ++ str ":" ++ int line ++ str ": " ++ str m)) fmt in
  let toml = try SomaToml.parse (read_file file) with
    | SomaToml.Error (line, m) -> error line "%s" m
    | Sys_error m -> CErrors.user_err Pp.(str m) in
  let known = "soma.toml has one table, [project]: " ^
              String.concat ", " (List.map (fun (k, what) -> k ^ " (" ^ what ^ ")") keys) in
  List.iter (fun (k, { SomaToml.line; _ }) ->
      if List.mem_assoc k keys then
        error line "%s is a key of [project]: it goes under the line [project], which begins soma.toml:\n\n%s"
          k (example root)
      else if k <> "project" then error line "%s is not something soma.toml says (yet). %s." k known) toml;
  let project, pline = match List.assoc_opt "project" toml with
    | Some { SomaToml.value = Table t; line } -> t, line
    | Some { SomaToml.line; value } -> error line "project is %s; it is a table:\n\n%s" (SomaToml.describe value) (example root)
    | None -> error 1 "soma.toml has no [project]; it begins:\n\n%s" (example root) in
  List.iter (fun (k, { SomaToml.line; _ }) ->
      if not (List.mem_assoc k keys) then
        error line "%s is not a key of [project] (yet). [project] has %s." k
          (String.concat ", " (List.map (fun (k, what) -> k ^ " (" ^ what ^ ")") keys))) project;
  let string key = match List.assoc_opt key project with
    | Some { SomaToml.value = String s; line } -> Some (s, line)
    | Some { SomaToml.line; value } -> error line "%s is %s; it is a string, in quotes" key (SomaToml.describe value)
    | None -> None in
  let name = match string "name" with
    | None -> error pline "[project] has no name: name = %S" (name_like (Filename.basename root))
    | Some (n, line) ->
      if valid_name n then n
      else error line "%S is no project name: a name is lowercase letters, digits and _, beginning with \
                       a letter (as Rocq and OCaml name it, where - is not allowed), \
                       64 at most: name = %S" n (name_like n) in
  let version = match string "version" with
    | None -> error pline "[project] has no version: version = \"0.1.0\", the project's semantic version (https://semver.org)"
    | Some (v, line) ->
      match parse_version v with
      | Ok v -> v
      | Error why -> error line "%S is no semantic version (https://semver.org): %s" v why in
  let description = match string "description" with
    | None -> None
    | Some (d, line) ->
      if String.trim d = "" then error line "description is empty: say what the project is, or leave it out";
      Some d in
  { root; name; description; version }

let loaded = Hashtbl.create 1

let load root =
  match Hashtbl.find_opt loaded root with
  | Some p -> p
  | None -> let p = load_uncached root in Hashtbl.add loaded root p; p

let of_file f =
  let f = if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f in
  let dir = if Sys.file_exists f && Sys.is_directory f then f else Filename.dirname f in
  Option.map load (find_root (CUnix.canonical_path_name dir))
