(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Miniml
open Constr
open Declarations
open Mod_declarations
open Names
open ModPath
open Libnames
open Pp
open CErrors
open Util
open Table
open Extraction
open Modutil
open Common

(****************************************)
(*S Part I: computing Rocq environment. *)
(****************************************)

let toplevel_env () =
  let mp, struc = Safe_typing.flatten_env (Global.safe_env ()) in
  mp, List.rev struc

let environment_until dir_opt =
  let rec parse = function
    | [] when Option.is_empty dir_opt -> [toplevel_env ()]
    | [] -> []
    | d :: l ->
      let meb =
        Modops.destr_nofunctor (MPfile d) (mod_type @@ Global.lookup_module (MPfile d))
      in
      match dir_opt with
      | Some d' when DirPath.equal d d' -> [MPfile d, meb]
      | _ -> (MPfile d, meb) :: (parse l)
  in parse (Library.loaded_libraries ())


(*s Visit:
  a structure recording the needed dependencies for the current extraction *)

module type VISIT = sig
  type t
  (* Environment of visited data *)
  val make : unit -> t

  (* Add the module_path and all its prefixes to the mp visit list.
     We'll keep all fields of these modules. *)
  val add_mp_all : t -> ModPath.t -> unit

  (* Add reference / ... in the visit lists.
     These functions silently add the mp of their arg in the mp list *)
  val add_ref : t -> global -> unit
  val add_kn : t -> KerName.t -> InfvInst.t -> unit
  val add_decl_deps : t -> ml_decl -> unit
  val add_spec_deps : t -> ml_spec -> unit

  (* Test functions:
     is a particular object a needed dependency for the current extraction ? *)
  val needed_ind : t -> MutInd.t -> InfvInst.t -> bool
  val needed_cst : t -> Constant.t -> InfvInst.t -> bool
  val needed_mp : t -> ModPath.t -> bool
  val needed_mp_all : t -> ModPath.t -> bool
end

module Visit : VISIT = struct
  module KNOrd =
  struct
    type t = KerName.t * InfvInst.t
    let compare (kn1, i1) (kn2, i2) =
      let c = KerName.compare kn1 kn2 in
      if Int.equal c 0 then InfvInst.compare i1 i2 else c
  end
  module KNset = Set.Make(KNOrd)

  type t =
      { mutable kn : KNset.t;
        mutable mp : ModPath.Set.t;
        mutable mp_all : ModPath.Set.t }
  (* the imperative internal visit lists *)
  let make () = {
    kn = KNset.empty;
    mp = ModPath.Set.empty;
    mp_all = ModPath.Set.empty;
  }
  (* the accessor functions *)
  let needed_ind v i inst = KNset.mem (MutInd.user i, inst) v.kn
  let needed_cst v c inst = KNset.mem (Constant.user c, inst) v.kn
  let needed_mp v mp = ModPath.Set.mem mp v.mp || ModPath.Set.mem mp v.mp_all
  let needed_mp_all v mp = ModPath.Set.mem mp v.mp_all
  let add_mp v mp =
    check_loaded_modfile mp; v.mp <- ModPath.Set.union (prefixes_mp mp) v.mp
  let add_mp_all v mp =
    check_loaded_modfile mp;
    v.mp <- ModPath.Set.union (prefixes_mp mp) v.mp;
    v.mp_all <- ModPath.Set.add mp v.mp_all
  let add_kn v kn inst = v.kn <- KNset.add (kn, inst) v.kn; add_mp v (KerName.modpath kn)
  let add_ref v r = let open GlobRef in match r.glob with
    | ConstRef c -> add_kn v (Constant.user c) r.inst
    | IndRef (ind,_) | ConstructRef ((ind,_),_) -> add_kn v (MutInd.user ind) r.inst
    | VarRef _ -> assert false
  let add_decl_deps v decl =
    decl_iter_references (fun kn -> add_ref v kn) (fun r -> add_ref v r) (fun r -> add_ref v r) decl
  let add_spec_deps v spec =
    spec_iter_references (fun r -> add_ref v r) (fun r -> add_ref v r) (fun r -> add_ref v r) spec
end

let get_mono_inst_univs = function
| Monomorphic -> [InfvInst.empty]
| Polymorphic uctx -> InfvInst.generate uctx

let get_mono_inst = function
| SFBconst cb -> get_mono_inst_univs cb.const_universes
| SFBmind mib -> get_mono_inst_univs mib.mind_universes
| SFBrules _ -> [InfvInst.empty]
| SFBmodule _ | SFBmodtype _ -> assert false

let add_field_label venv mp = function
  | (lab, (SFBconst _|SFBmind _ | SFBrules _  as f)) ->
    let insts = get_mono_inst f in
    List.iter (fun inst -> Visit.add_kn venv (KerName.make mp lab) inst) insts
  | (lab, (SFBmodule _|SFBmodtype _)) -> Visit.add_mp_all venv (MPdot (mp,lab))

let rec add_labels venv mp = function
  | MoreFunctor (_,_,m) -> add_labels venv mp m
  | NoFunctor sign -> List.iter (fun f -> add_field_label venv mp f) sign

exception Impossible

let check_arity env cb =
  let t = cb.const_type in
  if Reduction.is_arity env t then raise Impossible

let get_body lbody =
  EConstr.of_constr lbody

let check_fix env sg cb i =
  match cb.const_body with
    | Def lbody ->
        (match EConstr.kind sg (get_body lbody) with
          | Fix ((_,j),recd) when Int.equal i j -> check_arity env cb; (true,recd)
          | CoFix (j,recd) when Int.equal i j -> check_arity env cb; (false,recd)
          | _ -> raise Impossible)
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> raise Impossible

let prec_declaration_equal sg (na1, ca1, ta1) (na2, ca2, ta2) =
  Array.equal (Context.eq_annot Name.equal (EConstr.ERelevance.equal sg)) na1 na2 &&
  Array.equal (EConstr.eq_constr sg) ca1 ca2 &&
  Array.equal (EConstr.eq_constr sg) ta1 ta2

let factor_fix env sg l cb msb =
  let _,recd as check = check_fix env sg cb 0 in
  let n = Array.length (let fi,_,_ = recd in fi) in
  if Int.equal n 1 then [|l|], recd, msb
  else begin
    if List.length msb < n-1 then raise Impossible;
    let msb', msb'' = List.chop (n-1) msb in
    let labels = Array.make n l in
    List.iteri
      (fun j ->
         function
           | (l,SFBconst cb') ->
              let check' = check_fix env sg cb' (j+1) in
              if not ((fst check : bool) == (fst check') &&
                        prec_declaration_equal sg (snd check) (snd check'))
               then raise Impossible;
               labels.(j+1) <- l;
           | _ -> raise Impossible) msb';
    labels, recd, msb''
  end

(** Expanding a [module_alg_expr] into a version without abbreviations
    or functor applications. This is done via a detour to entries
    (hack proposed by Elie)
*)

let vm_state =
  (* VM bytecode is not needed here *)
  let vm_handler _ _ _ () = (), Vmemitcodes.BCuncompiled in
  ((), { Mod_typing.vm_handler })

let expand_mexpr env mp me =
  let inl = Declaremods.default_inline_level() in
  (* hack: in order not to overwrite the module binding mp, we first give it a
     name that should not be part of the env and then substitute it away *)
  let mp0 = ModPath.dummy in
  let state = ((Environ.universes env, Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
  let mb, (_, cst), _ = Mod_typing.translate_module state vm_state env mp0 inl (MExpr ([], me, None)) in
  let sign = mod_type mb in
  let reso = mod_delta mb in
  Modops.subst_modtype_signature_and_resolver mp0 mp sign reso

let expand_modtype env mp me =
  let inl = Declaremods.default_inline_level () in
  let state = ((Environ.universes env, Univ.UnivConstraints.empty), Reductionops.inferred_universes) in
  let mtb, _cst, _ = Mod_typing.translate_modtype state vm_state env mp inl ([],me) in
  mtb

let no_delta = Mod_subst.empty_delta_resolver

let flatten_modtype env mp me_alg struc_opt =
  match struc_opt with
  | Some me -> me, no_delta mp
  | None ->
     let mtb = expand_modtype env mp me_alg in
     mod_type mtb, mod_delta mtb

(** Ad-hoc update of environment, inspired by [Mod_typing.check_with_aux_def].
*)

let env_for_mtb_with_def env mp me reso idl =
  let struc = Modops.destr_nofunctor mp me in
  let l = List.hd idl in
  let spot = function (l',SFBconst _) -> Id.equal l l' | _ -> false in
  let before = fst (List.split_when spot struc) in
  Environ.Internal.overwrite_structure mp before reso env

let make_cst resolver mp l =
  Mod_subst.constant_of_delta_kn resolver (KerName.make mp l)

let make_mind resolver mp l =
  Mod_subst.mind_of_delta_kn resolver (KerName.make mp l)

(* The overwrite functions below are basically a hack to work around the fact
   that extraction breaks all kinds of reasonable invariants regarding modules.
   Due to the way signatures are handled, modules can be overwritten in the
   environment to replace a concrete body by its interface. Needless to say
   that this is probably wildly unsound, but it works good enough (TM). *)

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to specifications. *)

let rec extract_structure_spec table venv env mp reso = function
  | [] -> []
  | (l, SFBconst cb) :: msig ->
    let insts = get_mono_inst_univs cb.const_universes in
    let c = make_cst reso mp l in
    let map inst = extract_constant_spec table env c inst cb in
    let consts = List.map map insts in
    let specs = extract_structure_spec table venv env mp reso msig in
    let fold s specs =
      if logical_spec s then specs
      else
        let () = Visit.add_spec_deps venv s in
        (l, Spec s) :: specs
    in
    List.fold_right fold consts specs
  | (l, SFBmind mib) :: msig ->
    let insts = get_mono_inst_univs mib.mind_universes in
    let mind = make_mind reso mp l in
    let map inst = Sind (extract_inductive table env mind inst) in
    let minds = List.map map insts in
    let specs = extract_structure_spec table venv env mp reso msig in
    let fold s specs =
      if logical_spec s then specs
      else
        let () = Visit.add_spec_deps venv s in
        (l, Spec s) :: specs
    in
    List.fold_right fold minds specs
  | (l, SFBrules _) :: msig ->
      let specs = extract_structure_spec table venv env mp reso msig in
      specs
  | (l,SFBmodule mb) :: msig ->
      let specs = extract_structure_spec table venv env mp reso msig in
      let mp = MPdot (mp, l) in
      let spec = extract_mbody_spec table venv env mp mb in
      (l,Smodule spec) :: specs
  | (l,SFBmodtype mtb) :: msig ->
      let specs = extract_structure_spec table venv env mp reso msig in
      let mp = MPdot (mp, l) in
      let spec = extract_mbody_spec table venv env mp mtb in
      (l,Smodtype spec) :: specs

(* From [module_expression] to specifications *)

(* Invariant: the [me_alg] given to [extract_mexpr_spec] and
   [extract_mexpression_spec] should come from a [mod_type_alg] field.
   This way, any encountered [MEident] should be a true module type. *)

and extract_mexpr_spec table venv env mp1 (me_struct_o,me_alg) = match me_alg with
  | MEident mp ->
    let () = Visit.add_mp_all venv mp in
    MTident mp
  | MEwith(me',WithDef(idl,(c,ctx)))->
      let () = match ctx with
      | None -> ()
      | Some auctx ->
        (* XXX *)
        if Array.is_empty (UVars.AbstractContext.names auctx).quals then ()
        else user_err Pp.(str "Extraction of \"with Definition\" clauses not supported for sort polymorphic definitions.")
      in
      let me_struct,delta = flatten_modtype env mp1 me' me_struct_o in
      let env' = env_for_mtb_with_def env mp1 me_struct delta idl in
      let mt = extract_mexpr_spec table venv env mp1 (None,me') in
      let sg = Evd.from_env env in
      (match extract_with_type table env' sg (EConstr.of_constr c) with
       (* cb may contain some kn *)
         | None -> mt
         | Some (vl,typ) ->
            let () = type_iter_references (fun r -> Visit.add_ref venv r) typ in
            MTwith (mt, ML_With_type (InfvInst.empty, idl, vl, typ)))
  | MEwith(me',WithMod(idl,mp))->
      let () = Visit.add_mp_all venv mp in
      MTwith (extract_mexpr_spec table venv env mp1 (None, me'), ML_With_module(idl, mp))
  | MEapply _ ->
     (* No higher-order module type in OCaml : we use the expanded version *)
     let me_struct,delta = flatten_modtype env mp1 me_alg me_struct_o in
     extract_msignature_spec table venv env mp1 delta me_struct

and extract_mexpression_spec table venv env mp1 (me_struct,me_alg) = match me_alg with
  | MEMoreFunctor me_alg' ->
      let mbid, mtb, me_struct' = match me_struct with
      | MoreFunctor (mbid, mtb, me') -> (mbid, mtb, me')
      | _ -> assert false
      in
      let mp = MPbound mbid in
      let env' = Environ.Internal.overwrite_module_parameter mbid mtb env in
      MTfunsig (mbid, extract_mbody_spec table venv env mp mtb,
                extract_mexpression_spec table venv env' mp1 (me_struct', me_alg'))
  | MENoFunctor m -> extract_mexpr_spec table venv env mp1 (Some me_struct, m)

and extract_msignature_spec table venv env mp1 reso = function
  | NoFunctor struc ->
      let env' = Environ.Internal.overwrite_structure mp1 struc reso env in
      MTsig (mp1, extract_structure_spec table venv env' mp1 reso struc)
  | MoreFunctor (mbid, mtb, me) ->
      let mp = MPbound mbid in
      let env' = Environ.Internal.overwrite_module_parameter mbid mtb env in
      MTfunsig (mbid, extract_mbody_spec table venv env mp mtb,
                extract_msignature_spec table venv env' mp1 reso me)

and extract_mbody_spec : 'a. State.t -> _ -> _ -> _ -> 'a generic_module_body -> _ =
  fun table venv env mp mb -> match mod_type_alg mb with
  | Some ty -> extract_mexpression_spec table venv env mp (mod_type mb, ty)
  | None -> extract_msignature_spec table venv env mp (mod_delta mb) (mod_type mb)

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to implementations.

   NB: when [all=false], the evaluation order of the list is
   important: last to first ensures correct dependencies.
*)

let rec extract_structure table access venv env mp reso ~all = function
  | [] -> []
  | (l, SFBconst cb) :: struc ->
    let sg = Evd.from_env env in
    let fix, struc = match factor_fix env sg l cb struc with
    | (vl, recd, struc) -> Some (vl, recd), struc
    | exception Impossible -> None, struc
    in
    let ms = extract_structure table access venv env mp reso ~all struc in
    let insts = get_mono_inst_univs cb.const_universes in
    let c = make_cst reso mp l in
    let map inst = match fix with
    | None ->
      let b = Visit.needed_cst venv c inst in
      if all || b then
        let d = extract_constant table access env c inst cb in
        if (not b) && (logical_decl d) then None
        else
        let () = Visit.add_decl_deps venv d in
        Some (l, SEdecl d)
      else None
    | Some (vl, recd) ->
      let vc = Array.map (make_cst reso mp) vl in
      let b = Array.exists (fun vf -> Visit.needed_cst venv vf inst) vc in
      if all || b then
        let d = extract_fixpoint table env sg vc inst recd in
        if (not b) && (logical_decl d) then None
        else
          let () = Visit.add_decl_deps venv d in
          Some (l, SEdecl d)
      else None
    in
    let consts = List.map_filter map insts in
    consts @ ms
  | (l, SFBmind mib) :: struc ->
    let ms = extract_structure table access venv env mp reso ~all struc in
    let insts = get_mono_inst_univs mib.mind_universes in
    let mind = make_mind reso mp l in
    let map inst =
      let b = Visit.needed_ind venv mind inst in
      if all || b then
        let d = Dind (extract_inductive table env mind inst) in
        if (not b) && (logical_decl d) then None
        else
          let () = Visit.add_decl_deps venv d in
          Some (l, SEdecl d)
      else None
    in
    let inds = List.map_filter map insts in
    inds @ ms
  | (l, SFBrules rrb) :: struc ->
      (* A sort-polymorphic symbol has nonempty informative instances. An
         empty-instance lookup misses every use of it and falsely reports
         "no rules". Rules are warnings, not extracted implementations: keep
         their label when any extracted instance of the symbol is needed. *)
      let b = List.exists (fun (cst, _) ->
          let cb = Environ.lookup_constant cst env in
          List.exists (Visit.needed_cst venv cst) (get_mono_inst_univs cb.const_universes))
          rrb.rewrules_rules in
      let ms = extract_structure table access venv env mp reso ~all struc in
      if all || b then begin
        List.iter (fun (cst, _) -> Table.add_symbol_rule (State.get_table table) (ConstRef cst) l) rrb.rewrules_rules;
        ms
      end else ms
  | (l,SFBmodule mb) :: struc ->
      let ms = extract_structure table access venv env mp reso ~all struc in
      let mp = MPdot (mp,l) in
      let all' = all || Visit.needed_mp_all venv mp in
      if all' || Visit.needed_mp venv mp then
        (l, SEmodule (extract_module table access venv env mp ~all:all' mb)) :: ms
      else ms
  | (l,SFBmodtype mtb) :: struc ->
      let ms = extract_structure table access venv env mp reso ~all struc in
      let mp = MPdot (mp,l) in
      if all || Visit.needed_mp venv mp then
        (l, SEmodtype (extract_mbody_spec table venv env mp mtb)) :: ms
      else ms

(* From [module_expr] and [module_expression] to implementations *)

and extract_mexpr table access venv env mp = function
  | MEwith _ -> assert false (* no 'with' syntax for modules *)
  | me when lang () != Ocaml ->
      (* In Haskell/Scheme, we expand everything.
         For now, we also extract everything, dead code will be removed later
         (see [Modutil.optimize_struct]. *)
      let sign, delta = expand_mexpr env mp me in
      extract_msignature table access venv env mp delta ~all:true sign
  | MEident mp ->
      if is_modfile mp && not (State.get_modular table) then error_MPfile_as_mod mp false;
      Visit.add_mp_all venv mp; Miniml.MEident mp
  | MEapply (me, arg) ->
      Miniml.MEapply (extract_mexpr table access venv env mp me,
                      extract_mexpr table access venv env mp (MEident arg))

and extract_mexpression table access venv env mp mty = function
  | MENoFunctor me -> extract_mexpr table access venv env mp me
  | MEMoreFunctor me ->
      let (mbid, mtb, mty) = match mty with
      | MoreFunctor (mbid, mtb, mty) -> (mbid, mtb, mty)
      | NoFunctor _ -> assert false
      in
      let mp1 = MPbound mbid in
      let env' = Environ.Internal.overwrite_module_parameter mbid mtb env in
      Miniml.MEfunctor
        (mbid,
         extract_mbody_spec table venv env mp1 mtb,
         extract_mexpression table access venv env' mp mty me)

and extract_msignature table access venv env mp reso ~all = function
  | NoFunctor struc ->
    let env' = Environ.Internal.overwrite_structure mp struc reso env in
    Miniml.MEstruct (mp, extract_structure table access venv env' mp reso ~all struc)
  | MoreFunctor (mbid, mtb, me) ->
      let mp1 = MPbound mbid in
      let env' = Environ.Internal.overwrite_module_parameter mbid mtb env in
      Miniml.MEfunctor
        (mbid,
         extract_mbody_spec table venv env mp1 mtb,
         extract_msignature table access venv env' mp reso ~all me)

and extract_module table access venv env mp ~all mb =
  (* A module has an empty [mod_expr] when :
     - it is a module variable (for instance X inside a Module F [X:SIG])
     - it is a module assumption (Declare Module).
     Since we look at modules from outside, we shouldn't have variables.
     But a Declare Module at toplevel seems legal (cf #2525). For the
     moment we don't support this situation. *)
  let impl = match Mod_declarations.mod_expr mb with
    | Abstract -> error_no_module_expr mp
    | Algebraic me -> extract_mexpression table access venv env mp (mod_type mb) me
    | Struct (reso, sign) ->
      (* This module has a signature, otherwise it would be FullStruct.
         We extract just the elements required by this signature. *)
      let () = add_labels venv mp (mod_type mb) in
      let sign = Modops.annotate_struct_body sign (mod_type mb) in
      extract_msignature table access venv env mp reso ~all:false sign
    | FullStruct -> extract_msignature table access venv env mp (mod_delta mb) ~all (mod_type mb)
  in
  (* Slight optimization: for modules without explicit signatures
     ([FullStruct] case), we build the type out of the extracted
     implementation *)
  let typ = match Mod_declarations.mod_expr mb with
    | FullStruct ->
      assert (Option.is_empty @@ mod_type_alg mb);
      mtyp_of_mexpr impl
    | _ -> extract_mbody_spec table venv env mp mb
  in
  { ml_mod_expr = impl;
    ml_mod_type = typ }

let mono_environment table ~opaque_access refs mpl =
  let venv = Visit.make () in
  let () = List.iter (fun r -> Visit.add_ref venv r) refs in
  let () = List.iter (fun mp -> Visit.add_mp_all venv mp) mpl in
  let env = Global.env () in
  let l = List.rev (environment_until None) in
  List.rev_map
    (fun (mp,struc) ->
      mp, extract_structure table opaque_access venv env mp (no_delta mp) ~all:(Visit.needed_mp_all venv mp) struc)
    l

(**************************************)
(*S Part II : Input/Output primitives *)
(**************************************)

let descr () = match lang () with
  | Ocaml -> Ocaml.ocaml_descr
  | Haskell -> Haskell.haskell_descr
  | Scheme -> Scheme.scheme_descr
  | JSON -> Json.json_descr

(* From a filename string "foo.ml" or "foo", builds "foo.ml" and "foo.mli"
   Works similarly for the other languages. *)

let default_id = Id.of_string "Main"

let mono_filename f =
  let d = descr () in
  match f with
    | None -> None, None, default_id
    | Some f ->
        let f =
          if Filename.check_suffix f d.file_suffix then
            Filename.chop_suffix f d.file_suffix
          else f
        in
        let id =
          if lang () != Haskell then default_id
          else
            try Id.of_string (Filename.basename f)
            with UserError _ ->
              user_err Pp.(str "Extraction: provided filename is not a valid identifier")
        in
        let f =
          if Filename.is_relative f then
            Filename.concat (output_directory ()) f
          else f
        in
        Some (f^d.file_suffix), Option.map ((^) f) d.sig_suffix, id

(* Builds a suitable filename from a module id *)

let module_filename ?directory table mp =
  let directory = match directory with Some dir -> dir | None -> output_directory () in
  let f = file_of_modfile (State.get_table table) mp in
  let id = Id.of_string f in
  let f = Filename.concat directory f in
  let d = descr () in
  let fimpl_base = d.file_naming table mp ^ d.file_suffix in
  let fimpl = Filename.concat directory fimpl_base in
  Some fimpl, Option.map ((^) f) d.sig_suffix, id

(*s Extraction of one decl to stdout. *)

let print_one_decl table struc mp decl =
  let d = descr () in
  let () = State.reset table in
  let table = State.set_phase table Pre in
  ignore (d.pp_struct table struc);
  let table = State.set_phase table Impl in
  let ans = State.with_visibility table mp [] begin fun table ->
    d.pp_decl table decl
  end in
  v 0 ans

(*s Extraction of a ml struct to a file. *)

(** For Recursive Extraction, writing directly on stdout
    won't work with rocqide, we use a buffer instead *)

let formatter buf dry file =
  let ft =
    if dry then Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ())
    else
      match file with
        | Some f -> Topfmt.with_output_to f
        | None -> Format.formatter_of_buffer buf
  in
  (* XXX: Fixme, this shouldn't depend on Topfmt *)
  (* We never want to see ellipsis ... in extracted code *)
  Format.pp_set_max_boxes ft max_int;
  (* We reuse the width information given via "Set Printing Width" *)
  (match Topfmt.get_margin () with
    | None -> ()
    | Some i ->
      Format.pp_set_margin ft i;
      Format.pp_set_max_indent ft (i-10));
      (* note: max_indent should be < margin above, otherwise it's ignored *)
  ft

let get_comment () =
  let s = file_comment () in
  if String.is_empty s then None
  else
    let split_comment = Str.split (Str.regexp "[ \t\n]+") s in
    Some (prlist_with_sep spc str split_comment)

(* With the runtime of gradual casts, [?] and [err] may be values of
   inductive types (see gradual_rt.ml): every [match] on such a type goes
   through [Gradual_rt.check], which raises them when they are eliminated. *)
let gradual_guard_cases struc =
  let custom_ind br =
    is_custom_match br ||
    Array.exists (fun (_, p, _) -> match p with
        | Pusual r | Pcons (r, _) ->
          begin match r.glob with
            | GlobRef.ConstructRef (ind, _) -> is_custom { r with glob = GlobRef.IndRef ind }
            | _ -> false
          end
        | Ptuple _ | Prel _ | Pwild -> false) br
  in
  let rec guard a =
    match a with
    | MLif (MLapp (MLraw "Gradual_rt.is_exc_value", [MLrel i]) as c, p, MLcase (typ, (MLrel j as e), br))
      when Int.equal i j ->
      (* already guarded: extraction propagates [?] and [err] there *)
      MLif (c, guard p, MLcase (typ, e, Array.map (fun (ids, pat, b) -> (ids, pat, guard b)) br))
    | _ ->
      match Mlutil.ast_map guard a with
      | MLcase (typ, e, br) when not (custom_ind br) ->
        MLcase (typ, MLapp (MLraw "Gradual_rt.check", [e]), br)
      | a -> a
  in
  Modutil.struct_ast_map guard struc

let print_structure_to_file ?(shared_gradual=false) table (fn,si,mo) dry struc =
  let buf = Buffer.create 1000 in
  let d = descr () in
  let () = State.reset table in
  let unsafe_needs = {
    mldummy = struct_ast_search Mlutil.isMLdummy struc;
    tdummy = struct_type_search Mlutil.isTdummy struc;
    tunknown = struct_type_search ((==) Tunknown) struc;
    magic =
      if lang () != Haskell then false
      else struct_ast_search (function MLmagic _ -> true | _ -> false) struc;
    gradual_rt = shared_gradual || struct_ast_search (function MLraw _ -> true | _ -> false) struc }
  in
  let struc = if unsafe_needs.gradual_rt && lang () == Ocaml then gradual_guard_cases struc else struc in
  (* First, a dry run, for computing objects to rename or duplicate *)
  let table = State.set_phase table Pre in
  ignore (d.pp_struct table struc);
  let opened = opened_libraries table in
  (* Print the implementation *)
  let cout = if dry then None else Option.map open_out fn in
  let ft = formatter buf dry cout in
  let comment = get_comment () in
  begin try
    (* The real printing of the implementation *)
    let table = State.set_phase table Impl in
    pp_with ft (d.preamble table mo comment opened unsafe_needs);
    pp_with ft (d.pp_struct table struc);
    Format.pp_print_flush ft ();
    Option.iter close_out cout;
  with reraise ->
    Format.pp_print_flush ft ();
    Option.iter close_out cout; raise reraise
  end;
  if not dry then Option.iter info_file fn;
  (* Now, let's print the signature *)
  Option.iter
    (fun si ->
       let cout = open_out si in
       let ft = formatter buf false (Some cout) in
       begin try
         let table = State.set_phase table Intf in
         pp_with ft (d.sig_preamble table mo comment opened unsafe_needs);
         pp_with ft (d.pp_sig table (signature_of_structure struc));
         Format.pp_print_flush ft ();
         close_out cout;
       with reraise ->
         Format.pp_print_flush ft ();
         close_out cout; raise reraise
       end;
       info_file si)
    (if dry then None else si);
  (* Print the buffer content via Rocq standard formatter (ok with rocqide). *)
  if not (Int.equal (Buffer.length buf) 0) then begin
    Feedback.msg_notice (str (Buffer.contents buf));
  end


(*********************************************)
(*s Part III: the actual extraction commands *)
(*********************************************)

let init ?(inner=false) ~modular ~library () =
  if not inner then check_inside_section ();
  let keywords = (descr ()).keywords in
  let state = State.make ~modular ~library ~keywords () in
  if modular && lang () == Scheme then error_scheme ();
  state

let warns table =
  let table = State.get_table table in
  warning_opaques table (access_opaque ());
  warning_axioms table

(* For a qualid, let's retrieve whether it corresponds
   to a module or globref. If both, Warn the user and return the module. *)
let locate_ref qid =
  let open Either in
  let mpo = try Some (Nametab.locate_module qid) with Not_found -> None
  and ro =
    try
      let gr = Smartlocate.global_with_alias qid in
      let inst = Environ.universes_of_global (Global.env ()) gr in
      Some (List.map (fun inst -> { glob = gr; inst }) (InfvInst.generate inst))
    with Nametab.GlobalizationError _ | UserError _ -> None
  in
  match mpo, ro with
  | None, None -> Nametab.error_global_not_found ~info:Exninfo.null qid
  | None, Some r ->
    Left r
  | Some mp, None -> Right mp
  | Some mp, Some r ->
    let () = warning_ambiguous_name ?loc:qid.CAst.loc (qid, mp, (List.hd r).glob) in
    Right mp

let locate_refs l =
  let refs, mods = List.partition_map locate_ref l in
  List.flatten refs, mods

(*s Recursive extraction in the Rocq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. Also used when
    extracting to a file with the command:
    \verb!Extraction "file"! [qualid1] ... [qualidn]. *)

let structure_has_gradual_runtime struc =
  struct_ast_search (function
      | MLraw s -> String.starts_with ~prefix:"Gradual_rt." s
      | _ -> false) struc

let full_extr opaque_access f (refs,mps) =
  let table = init ~modular:false ~library:false () in
  List.iter (fun mp -> if is_modfile mp then error_MPfile_as_mod mp true) mps;
  let struc = optimize_struct table (refs,mps) (mono_environment table ~opaque_access refs mps) in
  let () = warns table in
  print_structure_to_file table (mono_filename f) false struc;
  if lang()=Ocaml && !SomaImport.generated_output then begin
    let capture(reference,type_)=
      let candidates=List.filter(fun r->GlobRef.CanOrd.equal r.glob reference)refs in
      let r=match candidates with [r]->r
        |_->user_err(str "A static assembly export has "++int(List.length candidates)++
          str " extraction instances: "++Libnames.pr_qualid(Libnames.qualid_of_path(Nametab.path_of_global reference)))in
      let declaration=get_decl_in_structure r struc in
      let actual,arity=match type_,declaration with
        |true,Dtype(actual,parameters,_)->actual,List.length parameters
        |true,Dind block->
          let packet=Array.find_opt(fun p->GlobRef.CanOrd.equal p.ip_typename_ref.glob reference &&
            not p.ip_logical)block.ind_packets in
          (match packet with Some p->p.ip_typename_ref,List.length p.ip_vars
           |None->user_err(str "A static assembly type was erased during extraction."))
        |false,Dterm(actual,_,_)->actual,0
        |false,Dfix(actual,_,_)->
          (match Array.find_opt(fun r->GlobRef.CanOrd.equal r.glob reference)actual with
           |Some r->r,0|None->user_err(str "A static assembly value is absent from extraction."))
        |_->user_err(str "A static assembly export changed kind during extraction.")in
      reference,type_,Common.pp_global_name table (if type_ then Common.Type else Common.Term)actual,arity in
    SomaForeign.native_static_extracted_names:=List.map capture !SomaForeign.native_static_extraction_requests
  end

(* Explicit output names in Soma builds are relative to the source project's
   root, independently of Cd and Extraction Output Directory. Resolve existing
   ancestors (and output symlinks) even when the output does not exist yet. *)
let extraction_project_root () =
  let env name = match Sys.getenv_opt name with
    | Some s when s <> "" -> Some s
    | _ -> None in
  let root = match env "SOMA_BUILD_ROOT", env "SOMA_PROJECT_ROOT" with
    | Some r, _ | None, Some r -> Some r
    | None, None ->
      let loc = Loc.get_current_command_loc () in
      let source = match loc with
        | Some { Loc.fname = Loc.InFile { file; _ }; _ } -> file
        | _ -> Option.default (Filename.concat (Sys.getcwd ()) "_") !(SomaImport.source_file) in
      let dir = Unix.realpath (Filename.dirname source) in
      (match SomaProject.find_root dir with
       | Some root -> Some root
       | None when SomaImport.applies ?loc () -> Some dir
       | None -> None) in
  if !SomaImport.generated_output then None else root

let project_extraction_path ~relative ~outputs target =
  match extraction_project_root () with
  | None -> target
  | Some root ->
    let refuse () = user_err Pp.(str "Extraction target " ++ quote (str target) ++
      str (if relative then " must be relative and stay inside the project being built."
           else " must stay inside the project being built.")) in
    if relative && not (Filename.is_relative target) then refuse ();
    let rec canonical path =
      try Unix.realpath path with
      | Unix.Unix_error (Unix.ENOENT, _, _) ->
        (match Unix.lstat path with
         | { Unix.st_kind = Unix.S_LNK; _ } -> refuse ()
         | _ -> ()
         | exception Unix.Unix_error (Unix.ENOENT, _, _) -> ());
        let parent = Filename.dirname path in
        if parent = path then refuse ();
        let parent = canonical parent in
        match Filename.basename path with
        | "." -> parent
        | ".." -> Filename.dirname parent
        | name -> Filename.concat parent name in
    let root = Unix.realpath root in
    let inside path =
      let path = try canonical path with Unix.Unix_error _ -> refuse () in
      let prefix = Filename.concat root "" in
      if not (CString.is_sub prefix path 0) then refuse ();
      path in
    let path = inside (if Filename.is_relative target then Filename.concat root target else target) in
    List.iter (fun f -> ignore (inside f)) (outputs path);
    path

let project_extraction_target target =
  project_extraction_path ~relative:true ~outputs:(fun path ->
      (* mono_filename adds language suffixes; check the actual files too
         before opening either one, including a signature symlink. *)
      let impl, intf, _ = mono_filename (Some path) in
      List.filter_map (fun x -> x) [impl; intf]) target

(* Modular commands have no explicit target. Their default is the source
   project, not the invoker's cwd. An output-directory setting is rooted in
   the same project and checked before it can create a directory or open a
   file. Check both names before writing either, including existing symlinks. *)
let project_module_filename table mp =
  match extraction_project_root () with
  | None -> module_filename table mp
  | Some root ->
    let directory = match output_directory_setting () with
      | None -> root
      | Some dir -> if Filename.is_relative dir then Filename.concat root dir else dir in
    let impl, intf, id = module_filename ~directory table mp in
    let confine = project_extraction_path ~relative:false ~outputs:(fun path -> [path]) in
    let impl, intf = Option.map confine impl, Option.map confine intf in
    List.iter (fun file -> System.mkdir (Filename.dirname file))
      (List.filter_map (fun x -> x) [impl; intf]);
    impl, intf, id

(* One compilation unit gives all modular outputs the same exception marker,
   type descriptions and constructor-cast registry. Cast keys remain canonical
   kernel inductive identities (not module-local OCaml pointers). *)
let shared_gradual_runtime_file () =
  let directory = match extraction_project_root () with
    | None -> output_directory ()
    | Some root -> match output_directory_setting () with
      | None -> root
      | Some dir -> if Filename.is_relative dir then Filename.concat root dir else dir in
  let base = String.uncapitalize_ascii shared_gradual_runtime_module in
  let confine = project_extraction_path ~relative:false ~outputs:(fun path -> [path]) in
  let impl = confine (Filename.concat directory (base ^ ".ml")) in
  let intf = confine (Filename.concat directory (base ^ ".mli")) in
  let marker = "(* Generated by Soma: shared gradual extraction runtime, ABI 2. *)\n" in
  if Sys.file_exists intf then user_err (str "Shared gradual runtime signature " ++
    quote (str intf) ++ str " already exists: use a new extraction directory.");
  let content = marker ^ Gradual_rt_source.source in
  if Sys.file_exists impl then begin
    let previous = In_channel.with_open_bin impl In_channel.input_all in
    if not (String.starts_with ~prefix:marker previous) then
      user_err (str "Shared gradual runtime target " ++ quote (str impl) ++
        str " is not generated by Soma: use a new extraction directory.")
  end;
  impl, content

let write_shared_gradual_runtime (file, content) =
  System.mkdir (Filename.dirname file);
  let tmp, oc = Filename.open_temp_file ~temp_dir:(Filename.dirname file) ".soma-gradual-" ".tmp" in
  Fun.protect ~finally:(fun () ->
      close_out_noerr oc;
      try Sys.remove tmp with Sys_error _ -> ()) (fun () ->
      output_string oc content;
      close_out oc;
      Sys.rename tmp file);
  info_file file

(* Soma: a dependency is checked, not run: what writes a file is refused in
   its compilation (vernac/somaImport.ml). Printing is not. *)
let refuse_in_check_only command =
  if Sys.getenv_opt "SOMA_CHECK_ONLY" = Some "1" then
    user_err (str command ++
      str " writes extracted files and is not available in soma check; " ++
      str "use soma build or soma extract.")

let full_extraction ~opaque_access f lr =
  if Option.has_some f then refuse_in_check_only "Extraction";
  if Option.has_some f then SomaImport.refuse_in_dependency "Extraction";
  let f = Option.map project_extraction_target f in
  full_extr opaque_access f (locate_refs lr)

(* Modular output shares its marker, exceptions, descriptor ABI and cast
   registry through one compilation unit. Every consumer in the selected
   structure is printed with guards, including ordinary matches without
   casts. Printed dependencies must advertise the same shared ABI; stale
   runtime-free/embedded dependencies fail closed until re-extracted. *)
let modular_gradual_runtime struc =
  let has_runtime = structure_has_gradual_runtime struc in
  if lang () != Ocaml then begin
    if has_runtime then user_err (str "Modular gradual extraction requires OCaml output.");
    false
  end else
  let has_cases = struct_ast_search (function MLcase _ -> true | _ -> false) struc in
  let gradual = Option.has_some (Gradual.get (Global.env ()) Gradual.GCast) in
  has_runtime || (gradual && has_cases)

(*s Separate extraction is similar to recursive extraction, with the output
   decomposed in many files, one per Rocq .v file *)

let separate_extraction ~opaque_access lr =
  refuse_in_check_only "Separate Extraction";
  SomaImport.refuse_in_dependency "Separate Extraction";
  let table = init ~modular:true ~library:false () in
  let refs,mps = locate_refs lr in
  let struc = optimize_struct table (refs,mps) (mono_environment table ~opaque_access refs mps) in
  let shared_gradual = modular_gradual_runtime struc in
  let () = List.iter (function
    | MPfile _, _ -> ()
    | (MPdot _ | MPbound _), _ ->
      user_err (str "Separate Extraction from inside a module is not supported."))
      struc
  in
  let () = warns table in
  let files = List.map (function
    | (MPfile dir, sel) as e ->
        project_module_filename table dir, e
    | (MPdot _ | MPbound _), _ -> assert false
  ) struc in
  let runtime = if shared_gradual then Some (shared_gradual_runtime_file ()) else None in
  Option.iter write_shared_gradual_runtime runtime;
  let () = List.iter (fun (names, e) ->
      print_structure_to_file ~shared_gradual table names false [e]) files in
  ()

(*s Simple extraction in the Rocq toplevel. The vernacular command
    is \verb!Extraction! [qualid]. *)

let simple_extraction ~opaque_access r =
  match locate_ref r with
  | Right mp -> full_extr opaque_access None ([], [mp])
  | Left (r::_) ->
    (* locate_ref returns all sort poly instantiations, should we extract all or just the Type one?
       (currently just the Type one) *)
    let table = init ~modular:false ~library:false () in
    let struc = optimize_struct table ([r],[]) (mono_environment table ~opaque_access [r] []) in
    let d = get_decl_in_structure r struc in
    let () = warns table in
    let flag =
      if is_custom r then str "(** User defined extraction *)" ++ fnl()
      else mt ()
    in
    let ans = flag ++ print_one_decl table struc (modpath_of_r r) d in
    Feedback.msg_notice ans
  | Left [] -> assert false


(*s (Recursive) Extraction of a library. The vernacular command is
  \verb!(Recursive) Extraction Library! [M]. *)

let extraction_library ~opaque_access is_rec CAst.{loc;v=m} =
  let command = if is_rec then "Recursive Extraction Library" else "Extraction Library" in
  refuse_in_check_only command;
  SomaImport.refuse_in_dependency command;
  let table = init ~modular:true ~library:true () in
  let dir_m =
    (* XXX WTF is going on here? *)
    let q = qualid_of_ident m in
    try Nametab.full_name_module q with Not_found -> error_unknown_module ?loc q
  in
  let dir_m = dirpath_of_path dir_m in
  let venv = Visit.make () in
  let () = Visit.add_mp_all venv (MPfile dir_m) in
  let env = Global.env () in
  let l = List.rev (environment_until (Some dir_m)) in
  let select l (mp,struc) =
    if Visit.needed_mp venv mp
    then (mp, extract_structure table opaque_access venv env mp (no_delta mp) ~all:true struc) :: l
    else l
  in
  let struc = List.fold_left select [] l in
  let struc = optimize_struct table ([],[]) struc in
  let shared_gradual = modular_gradual_runtime struc in
  let () = warns table in
  let files = List.map (function
    | (MPfile dir, sel) as e ->
        let dry = not is_rec && not (DirPath.equal dir dir_m) in
        project_module_filename table dir, dry, e
    | _ -> assert false
  ) struc in
  let runtime = if shared_gradual then Some (shared_gradual_runtime_file ()) else None in
  Option.iter write_shared_gradual_runtime runtime;
  let () = List.iter (fun (names, dry, e) ->
      print_structure_to_file ~shared_gradual table names dry [e]) files in
  ()

(* For the test-suite :
   extraction to a temporary file + run ocamlc on it *)

let compile f =
  try
    let args = [ "ocamlc"
               ; "-package";"zarith"
               ; "-I"; Filename.dirname f
               ; "-c"; f^"i"
               ; f
               ] in
    let res = CUnix.sys_command (Boot.Env.ocamlfind ()) args in
    match res with
    | Unix.WEXITED 0 -> ()
    | Unix.WEXITED n | Unix.WSIGNALED n | Unix.WSTOPPED n ->
       CErrors.user_err
         Pp.(str "Compilation of file " ++ str f ++
             str " failed with exit code " ++ int n)
  with Unix.Unix_error (e,_,_) ->
    CErrors.user_err
      Pp.(str "Compilation of file " ++ str f ++
          str " failed with error " ++ str (Unix.error_message e))

let remove f =
  if Sys.file_exists f then Sys.remove f

let extract_and_compile ~opaque_access l =
  refuse_in_check_only "Extraction TestCompile";
  SomaImport.refuse_in_dependency "Extraction TestCompile";
  if lang () != Ocaml then
    CErrors.user_err (Pp.str "This command only works with OCaml extraction");
  let f = Filename.temp_file "testextraction" ".ml" in
  (* The temporary name is trusted; the dependency refusal above still applies. *)
  let () = full_extr opaque_access (Some f) (locate_refs l) in
  let () = compile f in
  let () = remove f; remove (f^"i") in
  let base = Filename.chop_suffix f ".ml" in
  let () = remove (base^".cmo"); remove (base^".cmi") in
  Feedback.msg_notice (str "Extracted code successfully compiled")

(* Show the extraction of the current ongoing proof *)
let show_extraction ~pstate =
  let table = init ~inner:true ~modular:false ~library:false () in
  let prf = Declare.Proof.get pstate in
  let sigma, env = Declare.Proof.get_current_context pstate in
  let trms = Proof.partial_proof prf in
  let extr_term t =
    (* FIXME: substitute relevances with ground ones *)
    let ast, ty = extract_constr table env sigma t in
    let mp = Lib.current_mp () in
    let l = Declare.Proof.get_name pstate in
    let fake_ref = { glob = GlobRef.ConstRef (Constant.make2 mp l); inst = InfvInst.empty } in
    let decl = Dterm (fake_ref, ast, ty) in
    print_one_decl table [] mp decl
  in
  Feedback.msg_notice (Pp.prlist_with_sep Pp.fnl extr_term trms)
