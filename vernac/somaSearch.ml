(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: [soma search QUERY [FILE]]: Rocq's Search, as a command. A type is what
   a definition does and a theorem's statement what it says, so they can be
   looked for by their shape, as Hoogle and Loogle do. It is run in what was
   compiled: the files of the project and of the dependencies it names, each
   imported, or what FILE sees. A file that does not compile is left out and
   said to be, so that it works while a file is being written.

   Search matches what is written, and does not unfold: a theorem about
   [discount] is not found by the [_ * _ / _] that [discount] is. It sees what is
   loaded, so of Corelib and Stdlib what the project uses.

   What it adds to Search: where each result is, what it assumes (the hashes of
   vernac/somaHash.ml), so that a false axiom is told from a theorem, and the
   order, this project first, and what matches most of the type first. *)

open Pp
open Names

(* * What a compilation reports *)

let query_var = "SOMA_SEARCH"
let out_var = "SOMA_SEARCH_OUT"
let options_var = "SOMA_SEARCH_OPTIONS"

let parse_search text =
  let pa = Procq.Parsable.make (Gramlib.Stream.of_string ("Search " ^ text ^ ".")) in
  match Procq.Entry.parse (Pvernac.main_entry None) pa with
  | Some { CAst.v = { Vernacexpr.expr = VernacSynPure (VernacSearch (s, _, r)); _ }; _ } -> s, r
  | _ -> raise Not_found

(* a name, or part of one, or a qualified one *)
let is_word q =
  q <> "" && q.[0] <> '.' && q.[String.length q - 1] <> '.' &&
  String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' | '.' -> true | _ -> false) q

(* What a result is to the query, the better first. A word: its name, part of
   its name, what mentions it, and a name close to it. A pattern: the whole type,
   its conclusion, or a part. *)
type rank = Exact | Name | Conclusion | Mentions | Part | Similar

let match_name = function
  | Exact -> "exact" | Name -> "name" | Conclusion -> "conclusion"
  | Mentions -> "mentions" | Part -> "part" | Similar -> "similar"

let rank_of_match env sigma pattern typ =
  match pattern with
  | None -> Part
  | Some pat ->
    let matches c =
      try Constr_matching.is_matching env sigma pat (EConstr.of_constr c)
      with e when CErrors.noncritical e -> false in
    if matches typ then Exact
    else if matches (snd (Term.decompose_prod typ)) then Conclusion
    else Part

(* The library of a reference, and where its compiled file is *)
let rec root_library = function
  | ModPath.MPfile d -> Some d
  | ModPath.MPbound _ -> None
  | ModPath.MPdot (mp, _) -> root_library mp

let library_of = function
  | GlobRef.VarRef _ -> None
  | GlobRef.ConstRef c -> root_library (Constant.modpath c)
  | GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _) -> root_library (MutInd.modpath m)

let contains s sub =
  let n = String.length sub in
  let rec at i = i + n <= String.length s && (String.sub s i n = sub || at (i + 1)) in
  at 0

(* project, dependency, rocq-library, library: the order of the results *)
let scope_of gr =
  match library_of gr with
  | None -> 0, "project"
  | Some d when DirPath.equal d (Lib.library_dp ()) -> 0, "project"
  | Some d ->
    match Loadpath.locate_absolute_library d with
    | Ok f when contains f "/.soma-cache/.deps/" -> 1, "dependency"
    | Ok f when contains f "/.soma-cache/rocq/" -> 2, "rocq-library"
    | Ok f when contains f "/.soma-cache/" -> 0, "project"
    | _ -> 3, "library"

(* the file and line, of a file that is there: Soma's own were compiled elsewhere *)
let location gr =
  match Nametab.cci_src_loc (Globnames.TrueGlobal gr) with
  | Some { Loc.fname = Loc.InFile { file; _ }; line_nb; _ } when Sys.file_exists file ->
    let cwd = CUnix.canonical_path_name (Sys.getcwd ()) ^ "/" in
    let file = if Filename.is_relative file then file else
      try CUnix.canonical_path_name (Filename.dirname file) ^ "/" ^ Filename.basename file
      with Sys_error _ -> file in
    let shown =
      if String.starts_with ~prefix:cwd file
      then String.sub file (String.length cwd) (String.length file - String.length cwd)
      else file in
    Some (shown, line_nb)
  | _ -> None

let one_line s =
  String.concat " " (List.filter (( <> ) "") (String.split_on_char ' '
    (String.map (function '\n' | '\t' -> ' ' | c -> c) s)))

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

let json_list l = "[" ^ String.concat "," (List.map json_string l) ^ "]"

let kernel_name = function
  | GlobRef.ConstRef c -> Some (KerName.to_string (Constant.canonical c))
  | GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _) -> Some (KerName.to_string (MutInd.canonical m))
  | GlobRef.VarRef _ -> None

let report () =
  match Sys.getenv_opt query_var, Sys.getenv_opt out_var with
  | Some query, Some out when query <> "" && out <> "" ->
    let options = String.split_on_char ' ' (Option.default "" (Sys.getenv_opt options_var)) in
    let has o = List.mem o options in
    let limit = List.fold_left (fun acc o ->
        if String.starts_with ~prefix:"limit=" o
        then Option.default acc (int_of_string_opt (String.sub o 6 (String.length o - 6)))
        else acc) 20 options in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let found = ref [] in
    let add gr env sigma typ rank =
      let scope, scope_name = scope_of gr in
      let name = Libnames.string_of_path (Nametab.path_of_global gr) in
      let first = if rank = Exact then 0 else 1 in
      (* what two searches find is one result, at the better of its ranks *)
      match List.find_opt (fun ((_, _, r, n), _) -> n = name && r <= rank) !found with
      | Some _ -> ()
      | None ->
        let shown = one_line (Pp.string_of_ppcmds (Printer.pr_ltype_env env sigma typ)) in
        found := ((first, scope, rank, name), (gr, scope_name, shown, rank))
                 :: List.filter (fun ((_, _, _, n), _) -> n <> name) !found in
    let search text rank =
      let s, r = parse_search text in
      ComSearch.run_search env sigma s r (fun gr _ env sigma typ -> add gr env sigma typ (rank gr typ)) in
    if is_word query then begin
      (* a word is a name first, and then what mentions the thing of that name *)
      if not (String.contains query '.') then
        search ("\"" ^ query ^ "\"") (fun gr _ ->
            let base = Id.to_string (Nametab.basename_of_global gr) in
            if base = query then Exact
            else if contains base query then Name
            (* Search takes a string up to typos: for when nothing else is found *)
            else Similar);
      (match Nametab.global (Libnames.qualid_of_string query) with
       | gr ->
         add gr env sigma (fst (Typeops.type_of_global_in_context env gr)) Exact;
         search query (fun _ _ -> Mentions)
       | exception e when CErrors.noncritical e -> ())
    end else begin
      (* what Search takes, and a type without its parentheses *)
      let pattern_search text =
        let s, r = parse_search text in
        let pattern = ComSearch.search_pattern env sigma s in
        ComSearch.run_search env sigma s r (fun gr _ env sigma typ ->
            add gr env sigma typ (rank_of_match env sigma pattern typ)) in
      try pattern_search query with e when CErrors.noncritical e ->
        found := [];
        try pattern_search ("(" ^ query ^ ")") with e when CErrors.noncritical e ->
          CErrors.user_err (str "The query " ++ str query ++ str " does not mean anything here:" ++ fnl () ++
                            CErrors.print_no_report e ++ fnl () ++
                            str "A notation or a name of a library that only a file imports is known in" ++ spc () ++
                            str "what that file sees: soma search QUERY FILE.")
    end;
    let sorted = List.sort (fun (a, _) (b, _) -> compare a b) !found in
    let results = if has "no-assumptions"
      then List.filter (fun (_, (gr, _, _, _)) -> SomaHash.assumptions_of gr = []) sorted
      else sorted in
    let only_similar = results <> [] && List.for_all (fun (_, (_, _, _, r)) -> r = Similar) results in
    let results = if only_similar then results
      else List.filter (fun (_, (_, _, _, r)) -> r <> Similar) results in
    let total = List.length results in
    let taken = if limit <= 0 then results else List.filteri (fun i _ -> i < limit) results in
    let line ((_, _, _, name), (gr, scope, typ, rank)) =
      let assumes = SomaHash.assumptions_of gr in
      let where = location gr in
      if has "json" then
        Printf.sprintf "{\"name\":%s,\"type\":%s,\"match\":%s,\"scope\":%s,\"file\":%s,\"line\":%s,\"assumes\":%s,\"contract\":%s}\n"
          (json_string name) (json_string typ) (json_string (match_name rank)) (json_string scope)
          (match where with Some (f, _) -> json_string f | None -> "null")
          (match where with Some (_, l) -> string_of_int l | None -> "null")
          (json_list assumes)
          (match SomaHash.contract_of gr with Some c -> json_string c | None -> "null")
      else begin
        let is_axiom = match kernel_name gr with Some k -> List.mem k assumes | None -> false in
        let others = List.filter (fun a -> Some a <> kernel_name gr) assumes in
        let notes =
          (if is_axiom then ["  is assumed, and not proved\n"] else [])
          @ (match others with
              | [] -> []
              | _ ->
                let shown = List.filteri (fun i _ -> i < 3) others in
                let more = List.length others - List.length shown in
                ["  assumes " ^ String.concat ", " shown ^
                 (if more > 0 then Printf.sprintf ", and %d more" more else "") ^ "\n"]) in
        Printf.sprintf "%s%s : %s\n%s"
          (match where with Some (f, l) -> Printf.sprintf "%s:%d: " f l | None -> "")
          name typ (String.concat "" notes)
      end in
    Out_channel.with_open_bin out (fun oc ->
        if only_similar && not (has "json") then output_string oc "Nothing of that name. Similar names:\n";
        List.iter (fun r -> output_string oc (line r)) taken;
        if not (has "json") then
          if total = 0 then output_string oc "Nothing found.\n"
          else if total > List.length taken then
            output_string oc (Printf.sprintf "%d of %d. --limit 0 shows all.\n" (List.length taken) total))
  | _ -> ()

(* * The command *)

let usage () =
  CErrors.user_err (str "soma search QUERY [FILE] [--limit N] [--no-assumptions] [--json]" ++ fnl () ++
                    str "A QUERY is a name (discount), part of one, or a type ('list nat -> nat', '_ <= _').")

let parse_args args =
  let rec go positional options = function
    | [] -> List.rev positional, List.rev options
    | "--json" :: rest -> go positional ("json" :: options) rest
    | "--no-assumptions" :: rest -> go positional ("no-assumptions" :: options) rest
    | "--limit" :: n :: rest when Option.has_some (int_of_string_opt n) ->
      go positional (("limit=" ^ n) :: options) rest
    | a :: _ when String.starts_with ~prefix:"--" a -> usage ()
    | a :: rest -> go (a :: positional) options rest in
  go [] [] args

let remove_tree d = ignore (Sys.command (Filename.quote_command "rm" ["-rf"; d]))

let environment ~query ~out ~options extra =
  Array.of_list (
    List.filter (fun v -> not (String.starts_with ~prefix:"SOMA_" v)
                          || String.starts_with ~prefix:"SOMA_OCAML_SWITCH=" v)
      (Array.to_list (Unix.environment ()))
    @ [query_var ^ "=" ^ query; out_var ^ "=" ^ out; options_var ^ "=" ^ String.concat " " options;
       "SOMA_MIRAGE_BUILD=0"; "SOMA_OCAML_BUILD=0"] @ extra)

let compile ~env ~log ~vo file =
  let fd = Unix.openfile log [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o644 in
  let prog = Sys.executable_name in
  let pid = Unix.create_process_env prog [| prog; "--kind=compile"; file; "-o"; vo |] env Unix.stdin fd fd in
  Unix.close fd;
  let rec wait () = try snd (Unix.waitpid [] pid) with Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
  wait () = Unix.WEXITED 0

(* the line of [main] an error is at, from what the compilation said *)
let error_line ~main log =
  let prefix = Printf.sprintf "File %S, line " main in
  List.find_map (fun l ->
      if String.starts_with ~prefix l then
        let rest = String.sub l (String.length prefix) (String.length l - String.length prefix) in
        match String.index_opt rest ',' with
        | Some i -> int_of_string_opt (String.sub rest 0 i)
        | None -> None
      else None) (String.split_on_char '\n' (In_channel.with_open_bin log In_channel.input_all))

(* the compilation said it, and what it said was about the query *)
let print_string_of_error log =
  prerr_endline (String.trim (SomaDiff.first_error log));
  exit 1

let run args =
  let positional, options = parse_args args in
  let query, file = match positional with
    | [q] -> q, None
    | [q; f] -> q, Some f
    | _ -> usage () in
  let tmp = Filename.temp_file "soma-search" "" in
  Sys.remove tmp;
  Unix.mkdir tmp 0o755;
  let tmp = CUnix.canonical_path_name tmp in
  Fun.protect ~finally:(fun () -> remove_tree tmp) (fun () ->
      let out = Filename.concat tmp "results" in
      let log = Filename.concat tmp "compile.log" in
      (* a compiled file is named after its source *)
      let vo_of source = Filename.concat tmp (Filename.remove_extension (Filename.basename source) ^ ".vo") in
      let finish () = print_string (In_channel.with_open_bin out In_channel.input_all) in
      match file with
      | Some f ->
        if not (Sys.file_exists f) then
          CErrors.user_err (str f ++ str " does not exist.");
        let env = environment ~query ~out ~options [] in
        if compile ~env ~log ~vo:(vo_of f) f then finish ()
        else print_string_of_error log
      | None ->
        let cwd = CUnix.canonical_path_name (Sys.getcwd ()) in
        let root = SomaProject.find_root cwd in
        let main = Filename.concat tmp "soma_search_query.soma" in
        let imports, extra = match root with
          | None ->
            prerr_endline ("No soma.toml in " ^ cwd ^ " or above: searching Soma's own libraries. " ^
                           "soma search QUERY FILE searches what FILE sees.");
            [], []
          | Some root ->
            let top = SomaProject.load root in
            let own = SomaDiff.importable root in
            (* the dependencies it names, and not what they bring *)
            let deps = List.filter (fun (s : SomaDeps.selected) ->
                List.exists (fun (d : SomaProject.dependency) -> d.path.canonical = s.path) top.dependencies)
                (SomaDeps.ensure top) in
            let qualified name p = name ^ "." ^ p in
            let dep_files = List.concat_map (fun (s : SomaDeps.selected) ->
                List.map (qualified s.project.name) (SomaDiff.importable s.project.root)) deps in
            List.map (String.map (function '/' -> '.' | c -> c)) (own @ dep_files),
            ["SOMA_PROJECT_ROOT=" ^ root] in
        let env = environment ~query ~out ~options extra in
        (* what does not compile is left out, and said to be, and the rest searched *)
        let rec attempt imports =
          Out_channel.with_open_bin main (fun oc ->
              List.iter (fun i -> Printf.fprintf oc "Import %s.\n" i) imports);
          if compile ~env ~log ~vo:(vo_of main) main then finish ()
          else match error_line ~main log with
            | Some n when n >= 1 && n <= List.length imports ->
              prerr_endline (Printf.sprintf "Not searched, as it does not compile: %s" (List.nth imports (n - 1)));
              prerr_endline (SomaDiff.first_error log);
              attempt (List.filteri (fun i _ -> i <> n - 1) imports)
            | _ -> print_string_of_error log in
        attempt imports)
