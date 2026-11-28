open Names
type policy = { owner : string; properties : string list; invariants : string list; trusted : string list }
let policies = Summary.ref ~name:"Soma verification policies" []
let sources = Summary.ref ~name:"Soma verification source kinds" []
(* Compilation boundaries and checked receipts must survive STM restoration
   while the companion proof file and extraction commands are interpreted. *)
let sealed = Hashtbl.create 16
let receipts = Hashtbl.create 16
let snapshots = Hashtbl.create 16
let error fmt = Printf.ksprintf (fun s -> CErrors.user_err Pp.(str ("Soma verification: " ^ s))) fmt
let valid_name s = s<>"" && List.for_all (fun part ->
    part<>"" && String.for_all (function 'a'..'z'|'A'..'Z'|'0'..'9'|'_'|'\'' -> true | _ -> false) part)
    (String.split_on_char '.' s)
let names text = if String.trim text="" then [] else
  let xs=String.split_on_char ';' text |> List.map String.trim in
  List.iter (fun s -> if not (valid_name s) then error "invalid policy reference %S" s) xs;
  if List.length xs<>List.length (List.sort_uniq String.compare xs) then error "duplicate policy reference";
  xs
let cache p =
  match List.find_opt (fun old -> old.owner=p.owner) !policies with
  | None -> policies:=p:: !policies
  | Some old when old=p -> ()
  | Some _ -> error "conflicting policies for %s" p.owner
let object_ = Libobject.declare_object {
    (Libobject.default_object "Soma verification policy") with
    cache_function=cache; load_function=(fun _ p -> cache p);
    classify_function=(fun _ -> Libobject.Keep);
    discharge_function=(fun p -> Some p);
  }
let declare ~properties ~invariants ~trusted =
  let owner=DirPath.to_string (Lib.library_dp ()) in
  if Hashtbl.mem sealed owner then error "declare the policy in the source program, before its expectations";
  if List.exists (fun p -> p.owner=owner) !policies then error "one policy is allowed per source library";
  let properties=names properties and invariants=names invariants and trusted=names trusted in
  List.iter (fun name -> if List.mem name properties then error "%s is classified twice" name) invariants;
  Lib.add_leaf (object_ {owner;properties;invariants;trusted})
let source_object = Libobject.declare_object {
    (Libobject.default_object "Soma verification source kind") with
    cache_function=(fun s -> sources:=s:: !sources);
    load_function=(fun _ s -> sources:=s:: !sources);
    classify_function=(fun _ -> Libobject.Keep);
    discharge_function=(fun s -> Some s);
  }
let seal ~source =
  let owner=DirPath.to_string (Lib.library_dp ()) in
  Hashtbl.replace sealed owner (List.find_opt (fun p -> p.owner=owner) !policies);
  Lib.add_leaf (source_object (owner,Filename.check_suffix source ".soma"))
let receipt ~source = Hashtbl.find_opt receipts (Unix.realpath source)
let source_inputs source =
  let base=Filename.remove_extension source in
  List.map (fun file -> file,if Sys.file_exists file then Some (SomaMerkle.file_hash file) else None)
    [source;base ^ ".exp";base ^ ".ext"]
let begin_source source = Hashtbl.replace snapshots source (source_inputs source)
let quote text =
  let b=Buffer.create (String.length text+2) in Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n" | '\r' -> Buffer.add_string b "\\r" | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c<32 || Char.code c=127 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c) text;
  Buffer.add_char b '"'; Buffer.contents b
let array xs = "[" ^ String.concat ", " (List.map quote xs) ^ "]"
let required source = match Sys.getenv_opt "SOMA_REQUIRE_VERIFICATION" with
  | Some "1" -> Filename.check_suffix source ".soma"
  | Some file when file<>"" -> (try Unix.realpath file=Unix.realpath source with Unix.Unix_error _ -> false)
  | _ -> false
let enforce ~source ~output ~interface =
  let owner=DirPath.to_string (Lib.library_dp ()) in
  let policy=List.find_opt (fun p -> p.owner=owner) !policies in
  (match Hashtbl.find_opt sealed owner with
   | Some declared when declared<>policy -> error "source Verification policy changed while checking expectations"
   | _ -> ());
  if not interface && Sys.getenv_opt "SOMA_REQUIRE_VERIFICATION"=Some "1" then
    List.iter (fun library ->
        match List.assoc_opt library !sources with
        | Some false -> () (* Foreign declarations, audited through their users. *)
        | Some true when List.exists (fun p -> p.owner=library) !policies -> ()
        | Some true -> error "imported source library %s has no source-owned Verification policy" library
        | None -> error "imported source library %s has no checked source classification; rebuild it" library)
      (SomaHash.checked_libraries ());
  match policy with
  | None -> if required source then error "%s has no source-owned Verification policy" source
  | Some p when interface -> () (* The complete proof worker enforces this policy. *)
  | Some p ->
    let inputs=match Hashtbl.find_opt snapshots source with
      | Some before when before=source_inputs source -> before
      | _ -> error "source or proof companions changed during checking" in
    SomaHash.invalidate ();
    List.iter (fun name ->
        (try ignore (Nametab.locate (Libnames.qualid_of_string name)) with Not_found ->
           error "trusted law %s does not name a loaded kernel object" name)) p.trusted;
    let definitions=SomaHash.checked_definitions () in
    let used=List.concat_map (fun d -> d.SomaHash.assumptions) definitions |> List.sort_uniq String.compare in
    (* Gradual evidence is outside the static fragment even when a policy
       accidentally names the gradual primitives as trusted laws. *)
    let gradual=List.filter (String.starts_with ~prefix:"Corelib.Gradual.") used in
    if gradual<>[] then error "gradual evidence is not permitted: %s" (String.concat ", " gradual);
    let unexpected=List.filter (fun name -> not (List.mem name p.trusted)) used in
    if unexpected<>[] then error "untrusted assumptions: %s" (String.concat ", " unexpected);
    let env=Global.env () in
    let check invariant name =
      let full=owner ^ "." ^ name in
      let d=match List.find_opt (fun d -> d.SomaHash.name=full) definitions with
        | Some d -> d | None -> error "required %s %s is missing" (if invariant then "invariant" else "property") full in
      let c=match d.SomaHash.reference with GlobRef.ConstRef c -> c
        | _ -> error "%s is not a checked proof" full in
      let cb=Environ.lookup_constant c env in
      (match cb.Declarations.const_body with
       | Declarations.Def _ -> ()
       | Declarations.OpaqueDef proof ->
         (try ignore (Global.force_proof (Library.indirect_accessor [@ocaml.alert "-deprecated"]) proof)
          with e when CErrors.noncritical e -> error "%s has no accessible checked proof" full)
       | _ -> error "%s is an assumption, not a checked proof" full);
      let sigma=Evd.from_env env in
      let sort=Retyping.get_sort_of env sigma (EConstr.of_constr cb.const_type) in
      if not (EConstr.ESorts.is_prop sigma sort) then error "%s is not a proposition" full;
      if invariant then (match EConstr.kind sigma (Reductionops.whd_all env sigma (EConstr.of_constr cb.const_type)) with
          | Constr.Prod _ -> () | _ -> error "invariant %s must quantify over inputs" full);
      name,d in
    let properties=List.map (check false) p.properties and invariants=List.map (check true) p.invariants in
    let rows kind xs = List.map (fun (name,d) -> Printf.sprintf
        "[[%s]]\nname = %s\ncontract = %s\nwitness = %s\nassumptions = %s\n"
        kind (quote name) (quote d.SomaHash.contract) (quote d.SomaHash.witness) (array d.SomaHash.assumptions)) xs in
    let input_rows=List.map (fun (file,digest) -> Printf.sprintf "[[inputs]]\nfile = %s\nsha256 = %s\n"
        (quote (Filename.basename file)) (quote (Stdlib.Option.value ~default:"absent" digest))) inputs in
    let definitions=List.sort (fun a b -> String.compare a.SomaHash.name b.SomaHash.name) definitions in
    let receipt=Printf.sprintf "format = 1\nmodule = %s\nsource-sha256 = %s\ntrusted = %s\nused-assumptions = %s\nproperty-count = %d\ninvariant-count = %d\n%s"
        (quote owner) (quote (SomaMerkle.file_hash source)) (array p.trusted) (array used)
        (List.length properties) (List.length invariants)
        (String.concat "\n" (input_rows @ rows "properties" properties @ rows "invariants" invariants @
                            rows "definitions" (List.map (fun d -> d.SomaHash.name,d) definitions))) in
    Hashtbl.replace receipts (Unix.realpath source) receipt;
    let file=output ^ ".verification.toml" in
    let temp,oc=Filename.open_temp_file ~temp_dir:(Filename.dirname file) ".soma-verification-" ".tmp" in
    Fun.protect ~finally:(fun () -> close_out_noerr oc; try Sys.remove temp with Sys_error _ -> ()) (fun () ->
        output_string oc receipt; close_out oc; Unix.rename temp file)
