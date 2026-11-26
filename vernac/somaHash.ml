(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: the hash of a definition, as Unison hashes one: of the tree that was
   checked, with its names removed and each thing it mentions replaced by that
   thing's hash. A checked definition is a kernel term, so binders are already
   indices, and elaboration, gradual casts included, has happened. Comments,
   layout, line moves, binder names and which file it is in do not enter.

   A definition has two hashes:

   - Its contract, which is what what mentions it depends on: its type, its
     body when it is transparent, and every assumption it rests on, through
     proofs too. A proof's body is not in it.
   - Its witness: the contract, the body of its proof, and the witnesses of
     what it mentions, all the way down.

   So another proof of a statement changes the witness, and what mentions the
   theorem keeps its contract, as the proof does not change what the theorem
   says. But the contract has what the proof assumes, because Soma's logic
   is inconsistent once [unknown] is used: [unknown False : False]. A proof
   that begins to rest on [unknown], on an axiom or on a Lean theorem proves
   less, and that is not the same contract.

   An assumption is a leaf: its name and declared type, and for a foreign one
   what it is (a WebAssembly export, with the digest of its module's bytes; an
   OCaml value, with its libraries and FILE.ml's digest). A primitive is its
   name. Everything else is hashed down to these, Corelib included, so a hash
   does not change with a new Soma that did not change what it mentions. The
   format is the first line of what is hashed.

   The kernel has no cycles to tie: a constant mentions constants before it, a
   [Fixpoint] group being a [fix] in each, and a mutual inductive's types refer
   to each other by index. So a member of a block is the block's hash and its
   index.

   A constructor's names enter an inductive's hash, and the type's own does
   not: [bool] and a [color] of Red and Green are different types, as Unison's
   unique types are, however alike. What is not in the kernel's terms is not in
   the hash: notations, instances, hints and tactics of a file, which change
   how what imports it is elaborated. So equal hashes say that two definitions
   are the same, and not that a file imports the same thing. *)

open Names

(* * SHA-256 (FIPS 180-4): OCaml's own Digest is MD5, without collision
   resistance, and BLAKE2 only from OCaml 5.2 *)

let k = [|
  0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
  0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
  0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
  0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
  0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
  0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
  0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
  0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 |]

let sha256 s =
  let mask = 0xFFFFFFFF in
  let rotr x n = ((x lsr n) lor (x lsl (32 - n))) land mask in
  let h = [| 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19 |] in
  let len = String.length s in
  (* the message, a 1 bit, zeros, and its length in bits on 8 bytes *)
  let padded = ((len + 8) / 64 + 1) * 64 in
  let m = Bytes.make padded '\000' in
  Bytes.blit_string s 0 m 0 len;
  Bytes.set m len '\x80';
  for i = 0 to 7 do
    Bytes.set m (padded - 1 - i) (Char.chr (((len * 8) lsr (8 * i)) land 0xFF))
  done;
  let w = Array.make 64 0 in
  for block = 0 to padded / 64 - 1 do
    for t = 0 to 15 do
      let at i = Char.code (Bytes.get m (block * 64 + t * 4 + i)) in
      w.(t) <- (at 0 lsl 24) lor (at 1 lsl 16) lor (at 2 lsl 8) lor at 3
    done;
    for t = 16 to 63 do
      let s0 = rotr w.(t-15) 7 lxor rotr w.(t-15) 18 lxor (w.(t-15) lsr 3) in
      let s1 = rotr w.(t-2) 17 lxor rotr w.(t-2) 19 lxor (w.(t-2) lsr 10) in
      w.(t) <- (w.(t-16) + s0 + w.(t-7) + s1) land mask
    done;
    let v = Array.copy h in
    for t = 0 to 63 do
      let s1 = rotr v.(4) 6 lxor rotr v.(4) 11 lxor rotr v.(4) 25 in
      let ch = (v.(4) land v.(5)) lxor ((lnot v.(4)) land mask land v.(6)) in
      let t1 = (v.(7) + s1 + ch + k.(t) + w.(t)) land mask in
      let s0 = rotr v.(0) 2 lxor rotr v.(0) 13 lxor rotr v.(0) 22 in
      let maj = (v.(0) land v.(1)) lxor (v.(0) land v.(2)) lxor (v.(1) land v.(2)) in
      let t2 = (s0 + maj) land mask in
      v.(7) <- v.(6); v.(6) <- v.(5); v.(5) <- v.(4);
      v.(4) <- (v.(3) + t1) land mask;
      v.(3) <- v.(2); v.(2) <- v.(1); v.(1) <- v.(0);
      v.(0) <- (t1 + t2) land mask
    done;
    Array.iteri (fun i x -> h.(i) <- (h.(i) + x) land mask) v
  done;
  String.concat "" (Array.to_list (Array.map (Printf.sprintf "%08x") h))

(* * What a definition's hashes are made of *)

module SMap = CString.Map

let format = "soma-hash 1\n"

let hash parts = sha256 (format ^ String.concat "" parts)

type info = {
  contract : string;
  witness : string;
  shape : string;               (* what it says itself: its bytes with what it
                                   mentions by name, and not by hash, so that a
                                   change beneath it is not a change to it *)
  assumes : string SMap.t;      (* an assumption's name, and its contract *)
}

(* One definition being written: its bytes, the universes it has met, in the
   order it met them, and what it mentions *)
type writer = {
  buf : Buffer.t;
  named : Buffer.t;             (* the same, for its shape *)
  mutable levels : int Univ.Level.Map.t;
  mutable mentioned : info list;
}

let writer () = { buf = Buffer.create 256; named = Buffer.create 256; levels = Univ.Level.Map.empty; mentioned = [] }

(* each thing written says where it ends, so that no two trees write the same *)
let add w s = Buffer.add_string w.buf s; Buffer.add_string w.named s
let tag w t = add w t; add w "("
let close w = add w ")"
let int w n = add w (string_of_int n); add w ";"
let text w s = int w (String.length s); add w s

(* a thing mentioned: its hash, and its name for the shape *)
let mention w ~hash ~name =
  Buffer.add_string w.buf (string_of_int (String.length hash) ^ ";" ^ hash);
  Buffer.add_string w.named (string_of_int (String.length name) ^ ";" ^ name)

let level w l =
  if Univ.Level.is_set l then text w "Set"
  else begin
    let n = match Univ.Level.Map.find_opt l w.levels with
      | Some n -> n
      | None ->
        let n = Univ.Level.Map.cardinal w.levels in
        w.levels <- Univ.Level.Map.add l n w.levels;
        n in
    int w n
  end

let universe w u =
  let parts = Univ.Universe.repr u in
  int w (List.length parts);
  List.iter (fun (l, n) -> level w l; int w n) parts

let quality w q = text w (Pp.string_of_ppcmds (Sorts.Quality.raw_pr q))

let sort w s =
  match Sorts.quality s, s with
  | _, Sorts.SProp -> text w "SProp"
  | _, Sorts.Prop -> text w "Prop"
  | _, Sorts.Set -> text w "SetSort"
  | _, Sorts.Type u -> tag w "Type"; universe w u; close w
  | q, (Sorts.GSort (_, u) | Sorts.VSort (_, u)) -> tag w "QSort"; quality w q; universe w u; close w

let relevance w = function
  | Sorts.Relevant -> text w "r"
  | Sorts.Irrelevant -> text w "i"
  | Sorts.RelevanceVar q -> tag w "rv"; quality w (Sorts.Quality.QVar q); close w

let instance w u =
  let qs, ls = UVars.Instance.to_array u in
  int w (Array.length qs);
  Array.iter (quality w) qs;
  int w (Array.length ls);
  Array.iter (level w) ls

(* The foreign things Soma knows are parameters, with more to them than a
   name and a type: what the bytes or the OCaml are *)
let file_digest f =
  try sha256 (In_channel.with_open_bin f In_channel.input_all)
  with Sys_error _ -> "missing"

let foreign_identity_base c =
  match !SomaForeign.image c with
  | Some i ->
    let side (a, b) = a ^ ":" ^ b in
    Some (String.concat "\n" (["wasm"; file_digest i.module_file; i.export; side i.result]
                              @ List.map side i.params))
  | None ->
    let ocaml = List.find_map (fun (m : SomaForeign.ocaml_module) ->
        List.find_map (fun (k, path, item) ->
            if Constant.CanOrd.equal k c then Some (m, path, item) else None) m.items)
        (!SomaForeign.ocaml_modules ()) in
    match ocaml with
    | Some (m, path, item) ->
      let shown = match item with
        | SomaForeign.OCamlNativeValueReexport _ | SomaForeign.OCamlNativeModuleInclude _ | SomaForeign.OCamlNativeAlgebraicReexport _ | SomaForeign.OCamlNativeModuleAlias _ | SomaForeign.OCamlNativeOpenVariant _ | SomaForeign.OCamlNativeParametricCallable _ | SomaForeign.OCamlNativeParametricVariant _ | SomaForeign.OCamlNativeExternalFamily _ | SomaForeign.OCamlNativeImmutableRecord _ | SomaForeign.OCamlNativeType _ | SomaForeign.OCamlNativeAlgebraic _ | SomaForeign.OCamlNativeOwnedRecord _ | SomaForeign.OCamlNativeOwnedVariant _ | SomaForeign.OCamlNativeCallableType _ | SomaForeign.OCamlNativeCallback _ -> SomaForeign.native_identity item
        | SomaForeign.OCamlType n -> "type " ^ string_of_int n
        | SomaForeign.OCamlValue (ty, labels) ->
          ty ^ " " ^ String.concat "," (List.map (Option.default "") labels) in
      Some (String.concat "\n"
              (["ocaml"; m.top; path; shown;
                (match m.ml_file with Some f -> file_digest f | None -> "library")]
               @ List.sort compare m.libraries))
    | None ->
      Option.map (fun p -> "foreign\n" ^ Pp.string_of_ppcmds p) (!SomaForeign.describe c)

let constants : (string, info) Hashtbl.t = Hashtbl.create 997
let inductives : (string, info) Hashtbl.t = Hashtbl.create 97

let invalidate () = Hashtbl.clear constants; Hashtbl.clear inductives

let foreign_identity c =
  let base=foreign_identity_base c in
  match List.find_opt(fun info->Names.Constant.CanOrd.equal c info.SomaForeign.assembly_owner)
    (!SomaForeign.native_assemblies())with
  |None->base
  |Some info->Some(String.concat "\n"((match base with None->[]|Some b->[b])@
      [SomaForeign.native_assembly_identity info]))
(* a block being hashed, should its own types mention it by name *)
let in_progress = ref []

let kn_constant c = KerName.to_string (Constant.canonical c)
let kn_mind m = KerName.to_string (MutInd.canonical m)

(* the proofs and bodies of libraries are as Assumptions reads them *)
let opaque_body o =
  match Global.force_proof (Library.indirect_accessor [@ocaml.alert "-deprecated"]) o with
  | c, _ -> Some c
  | exception e when CErrors.noncritical e -> None

let rec term w c =
  let open Constr in
  let binder na = relevance w na.Context.binder_relevance in
  let names w nas = int w (Array.length nas); Array.iter binder nas in
  let terms a = int w (Array.length a); Array.iter (term w) a in
  match kind c with
  | Rel n -> tag w "R"; int w n; close w
  | Var id -> tag w "V"; text w (Id.to_string id); close w
  | Meta _ | Evar _ -> CErrors.anomaly (Pp.str "soma hash: a checked term has an unsolved hole.")
  | Sort s -> tag w "S"; sort w s; close w
  | Cast (a, k, t) ->
    tag w "C";
    text w (match k with VMcast -> "vm" | DEFAULTcast -> "d" | NATIVEcast -> "n");
    term w a; term w t; close w
  | Prod (na, a, b) -> tag w "P"; binder na; term w a; term w b; close w
  | Lambda (na, a, b) -> tag w "L"; binder na; term w a; term w b; close w
  | LetIn (na, a, t, b) -> tag w "T"; binder na; term w a; term w t; term w b; close w
  | App (f, args) -> tag w "A"; term w f; terms args; close w
  | Const (k, u) ->
    let i = constant k in
    w.mentioned <- i :: w.mentioned;
    tag w "c"; mention w ~hash:i.contract ~name:(kn_constant k); instance w u; close w
  | Ind ((m, i), u) -> tag w "I"; mind w m; int w i; instance w u; close w
  | Construct (((m, i), j), u) -> tag w "K"; mind w m; int w i; int w j; instance w u; close w
  | Case (ci, u, pms, ((nas, ret), r), iv, scrut, brs) ->
    tag w "M";
    mind w (fst ci.ci_ind); int w (snd ci.ci_ind);
    instance w u; terms pms;
    names w nas; term w ret; relevance w r;
    (match iv with
     | NoInvert -> text w "n"
     | CaseInvert { indices } -> tag w "inv"; terms indices; close w);
    term w scrut;
    int w (Array.length brs);
    Array.iter (fun (nas, b) -> names w nas; term w b) brs;
    close w
  | Fix ((rec_args, i), (nas, tys, bodies)) ->
    tag w "F"; int w i; int w (Array.length rec_args); Array.iter (int w) rec_args;
    names w nas; terms tys; terms bodies; close w
  | CoFix (i, (nas, tys, bodies)) ->
    tag w "O"; int w i; names w nas; terms tys; terms bodies; close w
  | Proj (p, r, a) ->
    let m, i = Projection.inductive p in
    tag w "J"; mind w m; int w i; int w (Projection.arg p); relevance w r; term w a; close w
  | Int n -> tag w "i"; text w (Uint63.to_string n); close w
  | Float f -> tag w "f"; text w (Float64.to_hex_string f); close w
  | String s -> tag w "s"; text w (Pstring.to_string s); close w
  | Array (u, t, d, ty) -> tag w "y"; instance w u; terms t; term w d; term w ty; close w

and mind w m =
  let key = kn_mind m in
  if List.mem key !in_progress then text w ("self " ^ string_of_int (List.length !in_progress))
  else begin
    let i = inductive m in
    w.mentioned <- i :: w.mentioned;
    mention w ~hash:i.contract ~name:key
  end

and universes w = function
  | Declarations.Monomorphic -> text w "mono"
  | Declarations.Polymorphic ctx ->
    (* the context's own variables, in order, and its constraints *)
    let qs, ls = UVars.AbstractContext.size ctx in
    tag w "poly"; int w qs; int w ls;
    let cs = UVars.AbstractContext.constraints ctx in
    let univs = Univ.UnivConstraints.elements (PConstraints.univs cs) in
    int w (List.length univs);
    List.iter (fun (a, k, b) ->
        level w a;
        text w (match k with Univ.UnivConstraint.Lt -> "<" | Le -> "<=" | Eq -> "=");
        level w b) univs;
    close w

(* What [w] mentions rests on, and these flags: a definition checked with
   guard or positivity checking off is an assumption itself *)
and rests_on w ~name (flags : Declarations.typing_flags) =
  let off =
    (if flags.check_guarded then [] else ["guard"])
    @ (if flags.check_positive then [] else ["positivity"])
    @ (if flags.check_universes then [] else ["universes"]) in
  let own = List.fold_left (fun acc what ->
      let n = name ^ " (no " ^ what ^ " check)" in
      SMap.add n (hash [n]) acc) SMap.empty off in
  List.fold_left (fun acc (i : info) ->
      SMap.union (fun _ a _ -> Some a) acc i.assumes) own w.mentioned

and assumes_bytes assumes =
  String.concat "" (List.map (fun (n, c) -> n ^ "=" ^ c ^ "\n") (SMap.bindings assumes))

and witnesses w = String.concat "" (List.rev_map (fun (i : info) -> i.witness) w.mentioned)

and constant c =
  let key = kn_constant c in
  match Hashtbl.find_opt constants key with
  | Some i -> i
  | None ->
    let cb = Environ.lookup_constant c (Global.env ()) in
    let w = writer () in
    let i = match cb.const_body with
      | Undef _ | Symbol _ ->
        (* a leaf: what it is, and what its type mentions *)
        tag w "axiom"; text w key;
        Option.iter (text w) (foreign_identity c);
        term w cb.const_type; close w;
        let contract = hash ["axiom\n"; Buffer.contents w.buf] in
        { contract; witness = hash [contract; witnesses w]; shape = hash ["shape\n"; Buffer.contents w.named];
          assumes = SMap.add key contract (rests_on w ~name:key cb.const_typing_flags) }
      | Primitive p ->
        tag w "primitive"; text w (CPrimitives.to_string p); term w cb.const_type; close w;
        let contract = hash ["primitive\n"; Buffer.contents w.buf] in
        { contract; witness = contract; shape = hash ["shape\n"; Buffer.contents w.named];
          assumes = rests_on w ~name:key cb.const_typing_flags }
      | Def body ->
        tag w "def"; universes w cb.const_universes; relevance w cb.const_relevance;
        Option.iter (text w) (foreign_identity c);
        term w cb.const_type; term w body; close w;
        let assumes = rests_on w ~name:key cb.const_typing_flags in
        let contract = hash ["def\n"; Buffer.contents w.buf; assumes_bytes assumes] in
        { contract; witness = hash [contract; witnesses w]; shape = hash ["shape\n"; Buffer.contents w.named]; assumes }
      | OpaqueDef o ->
        tag w "statement"; universes w cb.const_universes; relevance w cb.const_relevance;
        term w cb.const_type; close w;
        let statement = Buffer.contents w.buf in
        let shape = hash ["shape\n"; Buffer.contents w.named] in
        (* the proof, in the same universes; its mentions count for what it
           rests on, its bytes only for the witness *)
        Buffer.clear w.buf;
        (match opaque_body o with
         | Some body -> term w body
         | None -> text w "no proof here");
        let proof = Buffer.contents w.buf in
        let assumes = rests_on w ~name:key cb.const_typing_flags in
        let contract = hash ["statement\n"; statement; assumes_bytes assumes] in
        { contract; witness = hash [contract; proof; witnesses w]; shape; assumes } in
    Hashtbl.add constants key i;
    i

and inductive m =
  let key = kn_mind m in
  match Hashtbl.find_opt inductives key with
  | Some i -> i
  | None ->
    let mb = Environ.lookup_mind m (Global.env ()) in
    let w = writer () in
    in_progress := key :: !in_progress;
    Fun.protect ~finally:(fun () -> in_progress := List.tl !in_progress) (fun () ->
        tag w "inductive";
        universes w mb.mind_universes;
        int w mb.mind_nparams; int w mb.mind_nparams_rec;
        text w (match mb.mind_finite with
            | Declarations.Finite -> "ind" | CoFinite -> "coind" | BiFinite -> "bi");
        int w (Array.length mb.mind_packets);
        Array.iter (fun (p : Declarations.one_inductive_body) ->
            term w p.mind_user_arity;
            int w (Array.length p.mind_consnames);
            Array.iteri (fun j id ->
                text w (Id.to_string id);
                term w p.mind_user_lc.(j)) p.mind_consnames)
          mb.mind_packets;
        close w);
    let assumes = rests_on w ~name:key mb.mind_typing_flags in
    let contract = hash ["inductive\n"; Buffer.contents w.buf; assumes_bytes assumes] in
    let i = { contract; witness = hash [contract; witnesses w]; shape = hash ["shape\n"; Buffer.contents w.named]; assumes } in
    Hashtbl.add inductives key i;
    i

let of_global = function
  | GlobRef.VarRef _ -> None
  | GlobRef.ConstRef c -> Some (constant c)
  | GlobRef.IndRef (m, _) | GlobRef.ConstructRef ((m, _), _) -> Some (inductive m)

let contract_of gr = Option.map (fun (i : info) -> i.contract) (of_global gr)

let assumptions_of gr =
  match of_global gr with
  | Some i -> List.map fst (SMap.bindings i.assumes)
  | None -> []

(* * soma hash *)

(* The libraries to report: the file's, and those of the project's cache,
   which has its files and its dependencies'; not the Rocq libraries there,
   which are many and which they name for themselves *)
let reported_libraries () =
  let is_soma_library dir =
    match Loadpath.locate_absolute_library dir with
    | Ok f ->
      let has sub =
        let n = String.length sub in
        let rec at i = i + n <= String.length f && (String.sub f i n = sub || at (i + 1)) in
        at 0 in
      has "/.soma-cache/" && not (has "/.soma-cache/rocq/")
    | Error _ -> false in
  Lib.library_dp () :: List.filter is_soma_library (Library.loaded_libraries ())

let rec root_library = function
  | ModPath.MPfile d -> Some (d, [])
  | ModPath.MPbound _ -> None
  | ModPath.MPdot (mp, l) ->
    Option.map (fun (d, subs) -> d, subs @ [Id.to_string l]) (root_library mp)

let report ?(cache=false) () =
  match Sys.getenv_opt "SOMA_HASH" with
  | (None | Some "") when not cache -> ()
  | destination ->
    let libraries = reported_libraries () in
    let env = Global.env () in
    let shown mp label =
      match root_library mp with
      | Some (d, subs) when List.exists (DirPath.equal d) libraries ->
        Some (String.concat "." ((DirPath.to_string d :: subs) @ [Id.to_string label]))
      | _ -> None in
    let lines = Environ.fold_constants (fun c _ acc ->
        match shown (Constant.modpath c) (Constant.label c) with
        | Some name -> (name, constant c) :: acc
        | None -> acc) env [] in
    (* a member of a block is the block and its index *)
    let lines = Environ.fold_inductives (fun m mb acc ->
        let block = lazy (inductive m) in
        snd (Array.fold_left (fun (index, acc) (p : Declarations.one_inductive_body) ->
            index + 1,
            match shown (MutInd.modpath m) p.mind_typename with
            | Some name ->
              let i = Lazy.force block in
              let n = string_of_int index in
              (name, { i with contract = hash [i.contract; n]; witness = hash [i.witness; n];
                              shape = hash [i.shape; n] }) :: acc
            | None -> acc) (0, acc) mb.mind_packets)) env lines in
    let line (name, i) =
      let assumes = List.map fst (SMap.bindings i.assumes) in
      (* for soma diff (vernac/somaDiff.ml), a field to each tab *)
      if Sys.getenv_opt "SOMA_HASH_FIELDS" = Some "1" then
        String.concat "\t" ([name; i.contract; i.witness; i.shape] @ assumes) ^ "\n"
      else
        Printf.sprintf "%s %s %s%s\n" i.contract i.witness name
          (if assumes = [] then "" else "  assumes " ^ String.concat ", " assumes) in
    (match destination with None|Some ""->()|Some file->Out_channel.with_open_bin file (fun oc ->
        List.iter (fun l -> output_string oc (line l))
          (List.sort (fun (a, _) (b, _) -> compare a b) lines)))
