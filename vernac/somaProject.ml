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
   know is an error rather than ignored, until Soma knows it.

   [dependencies] has the projects it is built with, each key the path it is
   fetched from and each value its version, or a checkout on disk:

     [dependencies]
     "owner/repo" = "1.2.3"
     "owner/wip" = { path = "../wip" }

   Reading them uses no network: vernac/somaDeps.ml resolves them.

   [opam] has the versions of opam packages that the program's OCaml
   libraries come from, when the newest will not do; the others are the
   newest opam has:

     [opam]
     cryptokit = "1.20" *)

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

(* the numbers, then the pre-release: none is greater than any; identifier
   by identifier, numbers by value and below others, and more of them greater *)
let compare_version a b =
  let rec pre a b = match a, b with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x :: a, y :: b ->
      let c = match numeric x, numeric y with
        | true, true -> compare (int_of_string_opt x, x) (int_of_string_opt y, y)
        | true, false -> -1
        | false, true -> 1
        | false, false -> compare x y in
      if c <> 0 then c else pre a b in
  let c = compare (a.major, a.minor, a.patch) (b.major, b.minor, b.patch) in
  if c <> 0 then c else match a.pre, b.pre with
    | [], [] -> 0
    | [], _ -> 1
    | _, [] -> -1
    | a, b -> pre a b

(* * What a dependency is fetched from

   The path is an address, as Go's are: owner/repo is on github.com, a first
   segment with a . is the host. It is not the name [Import] uses, which is
   the dependency's own [project] name: a qualid has no / and no . inside a
   component. Major 2 and above is the suffix /vN, a path of its own. *)

type dependency_path = {
  canonical : string;
  url : string;
  major : int option;
}

let example_line = "\"owner/repo\" = \"1.2.3\""

let is_segment_char = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '.' | '_' | '-' -> true
  | _ -> false

(* vN, with N a number that does not begin with 0, unless it is v0 *)
let major_suffix s =
  if String.length s < 2 || s.[0] <> 'v' then None
  else
    let n = String.sub s 1 (String.length s - 1) in
    if numeric n && not (leading_zero n) then int_of_string_opt n else None

let rec split_last = function
  | [] -> assert false
  | [x] -> [], x
  | x :: r -> let p, l = split_last r in x :: p, l

let parse_repository_path ?(explicit_host = false) s =
  let contains_sub sub =
    let n = String.length sub in
    let rec at i = i + n <= String.length s && (String.sub s i n = sub || at (i + 1)) in
    at 0 in
  if contains_sub "://" then begin
    let after = match String.index_opt s ':' with
      | Some i -> String.sub s (i + 3) (String.length s - i - 3)
      | None -> s in
    let after = if Filename.check_suffix after ".git" then Filename.chop_suffix after ".git" else after in
    let after = if String.starts_with ~prefix:"github.com/" after
      then String.sub after 11 (String.length after - 11) else after in
    Error (Printf.sprintf "%S is a URL. A dependency is a path: %S = \"1.2.3\"" s after)
  end else if not (String.contains s '/') then
    Error (Printf.sprintf "%s is no path. A dependency path is in quotes: %s" s example_line)
  else
    let segments = String.split_on_char '/' s in
    if List.exists (fun x -> x = "" || x = "." || x = "..") segments then
      Error (Printf.sprintf "%S is no path. A path is segments separated by /: %s" s example_line)
    else match List.find_opt (fun x -> not (String.for_all is_segment_char x)) segments with
      | Some bad -> Error (Printf.sprintf "%S is no path segment." bad)
      | None ->
        let host, rest = match segments with
          | first :: rest when explicit_host || String.contains first '.' -> Some first, rest
          | _ -> None, segments in
        (* a suffix comes after owner/repo: owner/v2 is a repository named v2 *)
        let base, major =
          if List.length rest < 3 then rest, None
          else
            let base, last = split_last rest in
            match major_suffix last with
            | Some n -> base, Some n
            | None -> rest, None in
        match major with
        | Some n when n < 2 ->
          let without = String.concat "/" ((match host with Some h -> [h] | None -> []) @ base) in
          Error (Printf.sprintf "%S has the suffix v%d. Major 0 and 1 have no suffix: %S = \"1.2.3\"" s n without)
        | _ ->
          let host_name = Option.default "github.com" host in
          if host_name = "github.com" && List.length base <> 2 then
            Error (Printf.sprintf "%S is no path on github.com, whose paths are owner/repo, and owner/repo/vN \
                                   for major 2 and above. A dependency in a subdirectory of a repository is \
                                   not supported yet." s)
          else if base = [] then
            Error (Printf.sprintf "%S is no path. A path is segments separated by /: %s" s example_line)
          else
            let repo = String.concat "/" (host_name :: base) in
            let suffix = match major with Some n -> Printf.sprintf "/v%d" n | None -> "" in
            Ok { canonical = repo ^ suffix; url = "https://" ^ repo ^ ".git"; major }

(* The transport is explicit, while HTTPS and SSH names of one repository
   still select and lock one package. Keep SSH in [url], including when a
   locked source has to be fetched again. *)
let parse_path written =
  let ssh authority path make_url =
    let user, host = match String.split_on_char '@' authority with
      | [host] -> "", host
      | [user; host] -> user, host
      | _ -> "", "" in
    let valid s = s <> "" && s.[0] <> '-' && String.for_all is_segment_char s in
    if not (valid host) || (String.contains authority '@' && not (valid user)) then
      Error (Printf.sprintf "%S has no valid SSH user and host. Use git@host.com:owner/repo.git or ssh://git@host.com/owner/repo.git." written)
    else
      let parts = String.split_on_char '/' path in
      let strip_git s = if Filename.check_suffix s ".git" then Filename.chop_suffix s ".git" else s in
      let parts = match List.rev parts with
        | last :: repo :: rest when List.length parts >= 3 && Option.has_some (major_suffix last) ->
          List.rev (last :: strip_git repo :: rest)
        | last :: rest -> List.rev (strip_git last :: rest)
        | [] -> [] in
      match parse_repository_path ~explicit_host:true (host ^ "/" ^ String.concat "/" parts) with
      | Error why -> Error why
      | Ok p ->
        let repository = match p.major with
          | Some _ -> fst (split_last parts)
          | None -> parts in
        Ok { p with url = make_url authority (String.concat "/" repository ^ ".git") } in
  if String.starts_with ~prefix:"ssh://" written then
    let rest = String.sub written 6 (String.length written - 6) in
    match String.index_opt rest '/' with
    | Some i -> ssh (String.sub rest 0 i)
        (String.sub rest (i + 1) (String.length rest - i - 1))
        (fun authority repo -> "ssh://" ^ authority ^ "/" ^ repo)
    | None -> Error (Printf.sprintf "%S has no repository path. Use ssh://git@host.com/owner/repo.git." written)
  else match String.index_opt written ':' with
  | Some i when String.contains (String.sub written 0 i) '@' ->
    ssh (String.sub written 0 i)
      (String.sub written (i + 1) (String.length written - i - 1))
      (fun authority repo -> authority ^ ":" ^ repo)
  | _ -> parse_repository_path written

(* The final @VERSION follows the repository path. The @ in an SSH
   user@host belongs to its address, including when no version is given. *)
let split_version spec =
  match String.rindex_opt spec '@', String.rindex_opt spec '/' with
  | Some i, Some slash when i > slash ->
    String.sub spec 0 i, Some (String.sub spec (i + 1) (String.length spec - i - 1))
  | Some i, None when not (String.contains spec ':') || String.index_opt spec '@' <> Some i ->
    String.sub spec 0 i, Some (String.sub spec (i + 1) (String.length spec - i - 1))
  | _ -> spec, None

let check_dependency_version ~written path v =
  let shown = version_to_string v in
  if v.build <> [] then
    Error (Printf.sprintf "%S has build metadata. A dependency version is a tag: %S = %S" shown written
             (version_to_string { v with build = [] }))
  else match path.major with
    | Some n when n <> v.major ->
      Error (Printf.sprintf "%S is major %d, and %S is major %d. The version's major is the /vN of the path."
               written n shown v.major)
    | None when v.major >= 2 ->
      Error (Printf.sprintf "%S is major 0 or 1, and %S is major %d. Major 2 and above is \"%s/v%d\" = %S."
               written shown v.major written v.major shown)
    | _ -> Ok ()

type dependency_source =
  | Version of version
  | Checkout of string

type dependency = {
  written : string;
  path : dependency_path;
  source : dependency_source;
  line : int;
}

(* * soma.toml *)

(* [image]: how a MirageOS image of the project is built and run *)
type user_memory = { name : string; address : int option; size : int }

type image = {
  memory : int option;      (* MB, which soma run gives the image *)
  text_start : int option;  (* where the image's code is linked, past the guest's *)
  user_memory : user_memory list;
}

let no_image = { memory = None; text_start = None; user_memory = [] }

type t = {
  root : string;
  name : string;
  description : string option;
  version : version;
  dependencies : dependency list;
  opam : (string * string) list;
  image : image;
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

let opam_example = "cryptokit = \"1.20\""

let image_example = "memory = 4096 and text_start = \"0xC0000000\""

(* solo5's hvt links an image at 1 MB: the lowest it may be *)
let lowest_text_start = 0x100000

(* [0x] then hexadecimal digits, as a linker script writes an address *)
let hex_address s =
  let n = String.length s in
  if n > 2 && n <= 18 && (String.sub s 0 2 = "0x" || String.sub s 0 2 = "0X") &&
     String.for_all (function '0'..'9' | 'a'..'f' | 'A'..'F' -> true | _ -> false) (String.sub s 2 (n - 2))
  then int_of_string_opt s else None

(* opam's names of packages, and of versions (opam's manual, "Package
   names and versions") *)
let opam_name n =
  n <> "" && String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '-' | '_' | '+' -> true | _ -> false) n &&
  String.exists (function 'a'..'z' | 'A'..'Z' -> true | _ -> false) n
let opam_version v =
  v <> "" && String.for_all (function
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '-' | '_' | '+' | '.' | '~' -> true | _ -> false) v

let keys = ["name", "the project's name"; "version", "its semantic version";
            "description", "what it is, in a sentence"]

let load_uncached ?display root =
  let file = Filename.concat root file_name in
  let shown = Option.default file display in
  let error line fmt =
    Printf.ksprintf (fun m ->
        CErrors.user_err Pp.(str shown ++ str ":" ++ int line ++ str ": " ++ str m)) fmt in
  let toml = try SomaToml.parse (read_file file) with
    | SomaToml.Error (line, m) -> error line "%s" m
    | Sys_error m -> CErrors.user_err Pp.(str m) in
  let known = "soma.toml has [project]: " ^
              String.concat ", " (List.map (fun (k, what) -> k ^ " (" ^ what ^ ")") keys) ^
              ", [dependencies] (" ^ example_line ^ "), [opam] (" ^ opam_example ^ ")" ^
              ", and [image] (" ^ image_example ^ ")" in
  List.iter (fun (k, { SomaToml.line; _ }) ->
      if List.mem_assoc k keys then
        error line "%s is a key of [project]: it goes under the line [project], which begins soma.toml:\n\n%s"
          k (example root)
      else if not (List.mem k ["project"; "dependencies"; "opam"; "image"]) then error line "%s is not something soma.toml says (yet). %s." k known) toml;
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
  let dependency (written, { SomaToml.line; value }) =
    let path = match parse_path written with
      | Ok p -> p
      | Error why -> error line "%s" why in
    let checkout_line = Printf.sprintf "A checkout is %S = { path = \"../wip\" }." written in
    let source = match value with
      | SomaToml.String v ->
        let parsed = match parse_version v with
          | Ok parsed -> parsed
          | Error why -> error line "%S is no semantic version (https://semver.org): %s" v why in
        (match check_dependency_version ~written path parsed with
         | Ok () -> Version parsed
         | Error why -> error line "%s" why)
      | SomaToml.Table t ->
        List.iter (fun (k, { SomaToml.line; _ }) ->
            if k <> "path" && k <> "version" then
              error line "%s is not a key of a checkout (yet). %s" k checkout_line) t;
        if List.mem_assoc "version" t && List.mem_assoc "path" t then
          error line "%S has path and version. %s" written checkout_line;
        (match List.assoc_opt "path" t with
         | Some { SomaToml.value = String dir; line } ->
           let dir' = if Filename.is_relative dir then Filename.concat root dir else dir in
           if not (Sys.file_exists (Filename.concat dir' file_name)) then
             error line "%S has no soma.toml." dir;
           Checkout (CUnix.canonical_path_name dir')
         | Some { SomaToml.line; value } ->
           error line "path is %s; it is a string, in quotes. %s" (SomaToml.describe value) checkout_line
         | None -> error line "%S has no path. %s" written checkout_line)
      | v ->
        error line "%S is %s. A dependency is a version: %S = \"1.2.3\", or a checkout: %S = { path = \"../wip\" }."
          written (SomaToml.describe v) written written in
    { written; path; source; line } in
  let dependencies = match List.assoc_opt "dependencies" toml with
    | None -> []
    | Some { SomaToml.value = Table t; _ } -> List.map dependency t
    | Some { SomaToml.line; value } ->
      error line "dependencies is %s; it is a table: [dependencies]" (SomaToml.describe value) in
  (* owner/repo and github.com/owner/repo are one path *)
  ignore (List.fold_left (fun seen d ->
      (match List.find_opt (fun o -> o.path.canonical = d.path.canonical) seen with
       | Some o -> error d.line "%S is %S, on line %d: one path, written twice." d.written o.written o.line
       | None -> ());
      d :: seen) [] dependencies);
  let opam = match List.assoc_opt "opam" toml with
    | None -> []
    | Some { SomaToml.value = Table t; _ } ->
      List.map (fun (package, { SomaToml.line; value }) ->
          if not (opam_name package) then
            error line "%S is no opam package's name: letters, digits, -, _ and +, as %s" package opam_example;
          match value with
          | SomaToml.String v when opam_version v -> package, v
          | SomaToml.String v ->
            error line "%S is no opam version: letters, digits, and . - _ + ~, as %s" v opam_example
          | v -> error line "%s is %s; a package's version is a string, in quotes: %s = \"1.20\""
                   package (SomaToml.describe v) package) t
    | Some { SomaToml.line; value } ->
      error line "opam is %s; it is a table: [opam], then lines as %s" (SomaToml.describe value) opam_example in
  let image = match List.assoc_opt "image" toml with
    | None -> no_image
    | Some { SomaToml.value = Table t; line = iline } ->
      List.iter (fun (k, { SomaToml.line; _ }) ->
          if k <> "memory" && k <> "text_start" && k <> "user_memory" then
            error line "%s is not a key of [image] (yet). [image] has memory, the megabytes soma run gives \
                        the image, text_start, the address its code is linked at, and user_memory regions: %s" k image_example) t;
      let memory = match List.assoc_opt "memory" t with
        | None -> None
        | Some { SomaToml.value = Int m; _ } when m > 0 && m <= 1048576 -> Some m
        | Some { SomaToml.line; value } ->
          error line "memory is %s; it is the image's megabytes, a number from 1 to 1048576, without quotes: \
                      memory = 4096" (SomaToml.describe value) in
      let text_start = match List.assoc_opt "text_start" t with
        | None -> None
        | Some { SomaToml.value = String a; line } ->
          (match hex_address a with
           | Some x when x >= lowest_text_start && x land 0xFFFF = 0 -> Some x
           | Some _ -> error line "text_start %s: an image is linked at 0x100000 (1 MB) or above, \
                                    at a multiple of 0x10000 (64 KB): text_start = \"0xC0000000\"" a
           | None -> error line "%S is no address: 0x and hexadecimal digits, in quotes: \
                                 text_start = \"0xC0000000\"" a)
        | Some { SomaToml.line; value } ->
          error line "text_start is %s; it is an address, a string: text_start = \"0xC0000000\""
            (SomaToml.describe value) in
      (* the image's code is in its memory: linked at 3 GB, it needs
         more than 3 GB *)
      (match text_start, memory with
       | Some x, Some m when m * 1048576 <= x ->
         error iline "text_start 0x%x is past the image's %d MB of memory; memory = %d at least, \
                      for the image above it" x m (x / 1048576 + 64)
       | Some x, None ->
         error iline "text_start 0x%x needs memory above it: memory = %d, megabytes, at least" x (x / 1048576 + 64)
       | _ -> ());
      let user_memory = match List.assoc_opt "user_memory" t with
        | None -> []
        | Some { SomaToml.value = Array entries; line } ->
          List.map (function
            | SomaToml.Table fields ->
              List.iter (fun (key, { SomaToml.line; _ }) ->
                  if not (List.mem key ["name"; "address"; "size"]) then
                    error line "%s is not a key of an image.user_memory region" key) fields;
              let name = match List.assoc_opt "name" fields with
                | Some { SomaToml.value = String n; _ } when n <> "" && String.length n <= 67 &&
                    String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' -> true | _ -> false) n -> n
                | _ -> error line "user memory needs a name of 1 to 67 letters and digits" in
              let bytes key = match List.assoc_opt key fields with
                | Some { SomaToml.value = Int n; _ } -> n
                | Some { SomaToml.value = String s; _ } ->
                  (match hex_address s with Some n -> n | None -> error line "user memory %s is an integer or hexadecimal string" key)
                | _ -> error line "user memory needs %s, in bytes" key in
              let size = bytes "size" in
              let address = if List.mem_assoc "address" fields then Some (bytes "address") else None in
              if size <= 0 || size land 0xFFFF <> 0 then error line "user memory size is a positive multiple of 0x10000 (64 KB)";
              (match address with
               | Some a when a < lowest_text_start || a land 0xFFFF <> 0 ->
                 error line "user memory address is at least 0x100000 and a multiple of 0x10000"
               | Some a when a > max_int - size -> error line "user memory region overflows its address space"
               | _ -> ());
              (match address, memory with
               | Some a, Some m when a > m * 1048576 || size > m * 1048576 - a ->
                 error line "user memory region is past the image's memory"
               | _ -> ());
              (match address, text_start with
               | Some a, Some code when a <= code && size > code - a ->
                 error line "user memory region overlaps text_start"
               | _ -> ());
              { name; address; size }
            | _ -> error line "user_memory is an array of region tables: [{ name = \"guest\", size = \"0x100000\" }]") entries
        | Some { SomaToml.line; _ } -> error line "user_memory is an array of region tables" in
      let rec check_regions = function
        | [] -> ()
        | (region : user_memory) :: rest ->
          List.iter (fun (other : user_memory) ->
              if region.name = other.name then error iline "user memory %S is declared twice" region.name;
              match region.address, other.address with
              | Some a, Some b when a < b + other.size && b < a + region.size ->
                error iline "user memory regions %S and %S overlap" region.name other.name
              | _ -> ()) rest;
          check_regions rest in
      check_regions user_memory;
      { memory; text_start; user_memory }
    | Some { SomaToml.line; value } ->
      error line "image is %s; it is a table: [image], then %s" (SomaToml.describe value) image_example in
  { root; name; description; version; dependencies; opam; image }

let loaded = Hashtbl.create 1

let load ?display root =
  match Hashtbl.find_opt loaded root with
  | Some p -> p
  | None -> let p = load_uncached ?display root in Hashtbl.add loaded root p; p

let reload root =
  Hashtbl.remove loaded root;
  load root

let of_file f =
  let f = if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f in
  let dir = if Sys.file_exists f && Sys.is_directory f then f else Filename.dirname f in
  Option.map load (find_root (CUnix.canonical_path_name dir))
