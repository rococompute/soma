(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: WebAssembly modules (theories/Soma/Wasm.v).

   FILE.definition declares, [name : type.], what Soma takes the exports
   of FILE.wasm to be: each is a parameter (vernac/g_vernac.mlg), which
   [Wasm Bind], at the end of the file, ties to the export of its name,
   once it checked that the export exists, takes as many arguments, and
   that its numbers fit the declared types. The bindings are kept with
   the library, and are known wherever it is loaded.

   When Soma evaluates a term (SomaForeign.evaluate), a call of a bound
   parameter whose arguments are numbers is computed by the WebAssembly
   reference interpreter, and replaced by what it returns. What does not
   fit (a negative number for an [N], an argument too large for an
   [i64], a trap) becomes a cast that fails, so that it is a run-time
   error saying so, as any other. *)

open Names
open Pp

(* What a declared type is, and the module's numbers *)
type kind = KN | KZ | KAny | KI64 | KI32
type wnum = W32 | W64

type binding = {
  file : string;            (* FILE.wasm, absolute *)
  export : string;
  params : (kind * wnum) list;
  result : kind * wnum;
}

let bindings = Summary.ref ~name:"soma-wasm-bindings" Cmap_env.empty

let in_binding : Constant.t * binding -> Libobject.obj =
  Libobject.declare_object @@ Libobject.superglobal_object_nodischarge "Soma Wasm binding"
    ~cache:(fun (c, b) -> bindings := Cmap_env.add c b !bindings)
    ~subst:None

let wnum_name = function W32 -> "i32" | W64 -> "i64"

(* * The modules *)

let read file =
  try In_channel.with_open_bin file In_channel.input_all
  with Sys_error e -> CErrors.user_err (str "Cannot read the WebAssembly module " ++ str file ++ str ": " ++ str e ++ str ".")

let decode file =
  try Wasm.Decode.decode file (read file)
  with Wasm.Decode.Code (_, msg) ->
    CErrors.user_err (str file ++ str " is not a WebAssembly module: " ++ str msg ++ str ".")

(* the functions a module exports, with their types *)
let exported_functions m =
  List.filter_map (fun (ex : Wasm.Ast.export) ->
      match Wasm.Ast.export_type m ex with
      | Wasm.Types.ExternFuncType (Wasm.Types.FuncType (ps, rs)) ->
        Some (Wasm.Utf8.encode ex.Wasm.Source.it.Wasm.Ast.name, (ps, rs))
      | _ -> None) m.Wasm.Source.it.Wasm.Ast.exports

let pr_num_type = function
  | Wasm.Types.NumType Wasm.Types.I32Type -> "i32"
  | Wasm.Types.NumType Wasm.Types.I64Type -> "i64"
  | Wasm.Types.NumType Wasm.Types.F32Type -> "f32"
  | Wasm.Types.NumType Wasm.Types.F64Type -> "f64"
  | Wasm.Types.VecType _ -> "v128"
  | Wasm.Types.RefType _ -> "ref"

let pr_function (name, (ps, rs)) =
  str name ++ str " (" ++ str (String.concat ", " (List.map pr_num_type ps)) ++ str ") -> " ++
  str (match rs with [] -> "()" | [r] -> pr_num_type r | rs -> "(" ^ String.concat ", " (List.map pr_num_type rs) ^ ")")

(* instances, by file, made once: a module has no imports, or does not
   link *)
let instances : (string, Wasm.Instance.module_inst) Hashtbl.t = Hashtbl.create 3

let instance file =
  match Hashtbl.find_opt instances file with
  | Some i -> i
  | None ->
    let i =
      try Wasm.Eval.init (decode file) []
      with
      | Wasm.Eval.Link (_, msg) ->
        CErrors.user_err (str file ++ str " imports what Soma does not give it yet: " ++ str msg ++ str ".")
      | Wasm.Eval.Trap (_, msg) ->
        CErrors.user_err (str file ++ str " trapped when it started: " ++ str msg ++ str ".")
    in
    Hashtbl.add instances file i; i

(* * Wasm Bind *)

let ref_of name = Rocqlib.lib_ref name

let wasm_global name =
  try Some (Nametab.global (Libnames.qualid_of_string ("Soma.Wasm." ^ name)))
  with e when CErrors.noncritical e -> None

let kind_of env sigma t =
  let t = Reductionops.whd_all env sigma t in
  if GradualTyping.is_unknown_type env sigma t then Some KAny
  else
    let is name = match wasm_global name with
      | Some gr -> EConstr.isRefX env sigma gr t
      | None -> false in
    if EConstr.isRefX env sigma (ref_of "num.N.type") t then Some KN
    else if EConstr.isRefX env sigma (ref_of "num.Z.type") t then Some KZ
    else if is "i64" then Some KI64
    else if is "i32" then Some KI32
    else None

let fits kind w = match kind, w with
  | KI64, W32 | KI32, W64 -> false
  | _ -> true

(* [name : Any -> ... -> Any], with [arity] arguments: an export that the
   .definition does not declare, or of a module without one, which gradual
   types make usable as it is *)
let declare_any name arity =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let text = String.concat " -> " (List.init (arity + 1) (fun _ -> "Any")) in
  let sigma, typ = Constrintern.interp_type_evars env sigma (Procq.parse_string Procq.Constr.lconstr text) in
  let sigma, entry = Declare.prepare_parameter ~poly:PolyFlags.default
      ~udecl:UState.default_univ_decl ~types:typ sigma in
  ignore sigma;
  Declare.declare_constant ~name ~kind:Decls.(IsAssumption Definitional) (Declare.ParameterEntry entry)

let bind file =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let lib = Lib.library_dp () in
  let m = decode file in
  let exports = exported_functions m in
  let here c = match Constant.modpath c with ModPath.MPfile d -> DirPath.equal d lib | _ -> false in
  let constants = Environ.fold_constants (fun c cb acc -> if here c then (c, cb) :: acc else acc) env [] in
  let constants = List.sort (fun (a, _) (b, _) -> Constant.CanOrd.compare a b) constants in
  let base = Filename.basename file in
  let exported () =
    str "It exports " ++ prlist_with_sep pr_comma pr_function exports ++ str "." in
  List.iter (fun (c, cb) ->
      let name = Id.to_string (Constant.label c) in
      match cb.Declarations.const_body with
      | Declarations.Undef _ ->
        let ps, rs = match List.assoc_opt name exports with
          | Some t -> t
          | None ->
            CErrors.user_err (hov 0 (str (Filename.remove_extension base ^ ".definition") ++ str " declares " ++
                                     str name ++ str ", which " ++ str base ++ str " does not export." ++
                                     spc () ++ exported ())) in
        let wnum t = match t with
          | Wasm.Types.NumType Wasm.Types.I32Type -> W32
          | Wasm.Types.NumType Wasm.Types.I64Type -> W64
          | t -> CErrors.user_err (str name ++ str ": " ++ str base ++ str "'s " ++ str name ++ str " has a " ++
                                   str (pr_num_type t) ++ str ", and Soma only gives and takes i32 and i64 yet.") in
        let wps = List.map wnum ps in
        let wr = match rs with
          | [r] -> wnum r
          | _ -> CErrors.user_err (str name ++ str ": " ++ str base ++ str "'s " ++ str name ++
                                   str " returns " ++ int (List.length rs) ++ str " values, and Soma takes one.") in
        (* the declared type, as arguments and a result *)
        let typ = EConstr.of_constr cb.Declarations.const_type in
        let decls, result = Reductionops.whd_decompose_prod env sigma typ in
        let decls = List.rev decls in
        if List.length decls <> List.length wps then
          CErrors.user_err (hov 0 (str name ++ str " is declared with " ++ int (List.length decls) ++
                                   str " arguments, and " ++ str base ++ str "'s takes " ++ int (List.length wps) ++
                                   str ":" ++ spc () ++ pr_function (name, (ps, rs)) ++ str "."));
        let declared t w =
          match kind_of env sigma t with
          | Some k when fits k w -> k
          | Some _ ->
            CErrors.user_err (str name ++ str ": " ++ Printer.pr_econstr_env env sigma t ++
                              str " is not " ++ str base ++ str "'s " ++ str (wnum_name w) ++ str ".")
          | None ->
            CErrors.user_err (hov 0 (str name ++ str ": a declared type is N, Z, Any, i64 or i32," ++ spc () ++
                                     str "and not " ++ Printer.pr_econstr_env env sigma t ++ str "."))
        in
        let params = List.map2 (fun (_, t) w -> declared t w, w) decls wps in
        let result = declared result wr, wr in
        Lib.add_leaf (in_binding (c, { file; export = name; params; result }))
      | _ ->
        CErrors.user_err (str (Filename.remove_extension base ^ ".definition") ++
                          str " declares what " ++ str base ++ str " exports, and defines nothing: " ++
                          str name ++ str " is a definition."))
    constants;
  (* the exports it does not declare: of type Any, as gradual types allow *)
  let declared = List.map (fun (c, _) -> Id.to_string (Constant.label c)) constants in
  List.iter (fun (name, (ps, rs)) ->
      let wnum t = match t with
        | Wasm.Types.NumType Wasm.Types.I32Type -> Some W32
        | Wasm.Types.NumType Wasm.Types.I64Type -> Some W64
        | _ -> None in
      let valid = try ignore (Id.of_string name); true with e when CErrors.noncritical e -> false in
      if valid && not (List.mem name declared) then
        match List.map wnum ps, rs with
        | wps, [r] when List.for_all Option.has_some wps && Option.has_some (wnum r) ->
          let c = declare_any (Id.of_string name) (List.length ps) in
          Lib.add_leaf (in_binding (c, { file; export = name;
                                         params = List.map (fun w -> KAny, Option.get w) wps;
                                         result = KAny, Option.get (wnum r) }))
        | _ -> ())
    exports

(* * Calls *)

(* numbers as Soma has them, and back *)
let rec positive_of env sigma c =
  let f, args = EConstr.decompose_app sigma c in
  if EConstr.isRefX env sigma (ref_of "num.pos.xH") f then Some Z.one
  else if EConstr.isRefX env sigma (ref_of "num.pos.xO") f then
    Option.map (fun p -> Z.mul (Z.of_int 2) p) (positive_of env sigma args.(0))
  else if EConstr.isRefX env sigma (ref_of "num.pos.xI") f then
    Option.map (fun p -> Z.succ (Z.mul (Z.of_int 2) p)) (positive_of env sigma args.(0))
  else None

let rec nat_of env sigma c =
  let f, args = EConstr.decompose_app sigma c in
  if EConstr.isRefX env sigma (ref_of "num.nat.O") f then Some Z.zero
  else if EConstr.isRefX env sigma (ref_of "num.nat.S") f then Option.map Z.succ (nat_of env sigma args.(0))
  else None

(* the number a value is, and its type: N, Z or nat; an Any holding one *)
let rec number_of env sigma c =
  let f, args = EConstr.decompose_app sigma c in
  if EConstr.isRefX env sigma (ref_of "num.N.N0") f then Some Z.zero
  else if EConstr.isRefX env sigma (ref_of "num.N.Npos") f then positive_of env sigma args.(0)
  else if EConstr.isRefX env sigma (ref_of "num.Z.Z0") f then Some Z.zero
  else if EConstr.isRefX env sigma (ref_of "num.Z.Zpos") f then positive_of env sigma args.(0)
  else if EConstr.isRefX env sigma (ref_of "num.Z.Zneg") f then Option.map Z.neg (positive_of env sigma args.(0))
  else if EConstr.isRefX env sigma (ref_of "num.nat.O") f || EConstr.isRefX env sigma (ref_of "num.nat.S") f
  then nat_of env sigma c
  else match EConstr.kind sigma f with
    | Const (k, _) when Gradual.kind_of env k = Some Gradual.GCast && Array.length args = 3 ->
      (* an Any, made of a number *)
      number_of env sigma args.(2)
    | _ -> None

(* an Any made of a closed value of a type that is no number's: its type
   and the value *)
let any_value env sigma c =
  let f, args = EConstr.decompose_app sigma c in
  match EConstr.kind sigma f with
  | Const (k, _) when Gradual.kind_of env k = Some Gradual.GCast && Array.length args = 3 ->
    let source = args.(0) and v = args.(2) in
    let head, _ = EConstr.decompose_app sigma v in
    let is_value = match EConstr.kind sigma head with
      | Construct _ | Int _ | Float _ | String _ -> true
      | _ -> false in
    if is_value && EConstr.Vars.closed0 sigma v && EConstr.Vars.closed0 sigma source then Some (source, v) else None
  | _ -> None

let rec mk_positive z =
  if Z.equal z Z.one then EConstr.mkRef (ref_of "num.pos.xH", EConstr.EInstance.empty)
  else
    let half = mk_positive (Z.div z (Z.of_int 2)) in
    let c = if Z.equal (Z.rem z (Z.of_int 2)) Z.zero then "num.pos.xO" else "num.pos.xI" in
    EConstr.mkApp (EConstr.mkRef (ref_of c, EConstr.EInstance.empty), [|half|])

let mk_ref name = EConstr.mkRef (ref_of name, EConstr.EInstance.empty)

let mk_N z =
  if Z.equal z Z.zero then mk_ref "num.N.N0"
  else EConstr.mkApp (mk_ref "num.N.Npos", [|mk_positive z|])

let mk_Z z =
  if Z.equal z Z.zero then mk_ref "num.Z.Z0"
  else if Z.gt z Z.zero then EConstr.mkApp (mk_ref "num.Z.Zpos", [|mk_positive z|])
  else EConstr.mkApp (mk_ref "num.Z.Zneg", [|mk_positive (Z.neg z)|])

let wasm_ref name = match wasm_global name with
  | Some gr -> EConstr.mkRef (gr, EConstr.EInstance.empty)
  | None -> CErrors.anomaly (str "Soma.Wasm." ++ str name ++ str " is not loaded.")

let gradual env k = match Gradual.get env k with
  | Some c -> EConstr.mkConstU (c, EConstr.EInstance.empty)
  | None -> CErrors.anomaly (str "Gradual typing is not loaded.")

let any_type env = EConstr.mkApp (gradual env Gradual.GUnknown, [|EConstr.mkSort EConstr.ESorts.type1|])

let type_of_kind env = function
  | KN -> mk_ref "num.N.type"
  | KZ -> mk_ref "num.Z.type"
  | KAny -> any_type env
  | KI64 -> wasm_ref "i64"
  | KI32 -> wasm_ref "i32"

let cast env a b v = EConstr.mkApp (gradual env Gradual.GCast, [|a; b; v|])

(* the module's number, as its own type: I64 z *)
let mk_wasm env w z =
  EConstr.mkApp (wasm_ref (match w with W64 -> "I64" | W32 -> "I32"), [|mk_Z z|])

let wasm_type w = wasm_ref (wnum_name w)

(* a value of type [declared] that fails, as the cast of [v], of type [a],
   to [b] does, then is [raise] at [declared] *)
let failing env ~declared a b v =
  let failed = cast env a b v in
  if EConstr.eq_constr Evd.empty b declared then failed
  else
    (* through Any, which does not fail of its own: what fails, and is
       said, is the cast of [v] *)
    let any = any_type env in
    cast env any declared (cast env b any failed)

let range = function
  | W64 -> Z.neg (Z.shift_left Z.one 63), Z.pred (Z.shift_left Z.one 63)
  | W32 -> Z.neg (Z.shift_left Z.one 31), Z.pred (Z.shift_left Z.one 31)

let to_value w z = match w with
  | W64 -> Wasm.Values.Num (Wasm.Values.I64 (Z.to_int64 z))
  | W32 -> Wasm.Values.Num (Wasm.Values.I32 (Z.to_int32 z))

let of_value = function
  | Wasm.Values.Num (Wasm.Values.I64 x) -> Some (Z.of_int64 x)
  | Wasm.Values.Num (Wasm.Values.I32 x) -> Some (Z.of_int32 x)
  | _ -> None

(* the result of a call, as a value of its declared type, or as a cast
   that fails, saying why *)
let call env sigma b args =
  let rkind, rw = b.result in
  let declared = type_of_kind env rkind in
  (* the arguments: each a number that the module's type holds *)
  let rec arguments acc = function
    | [] -> Ok (List.rev acc)
    | ((k, w), (a, ty)) :: rest ->
      match number_of env sigma a with
      | None ->
        begin match any_value env sigma a with
          (* an Any holding a value of another type, "two" : string: no
             number of the module's is one *)
          | Some (source, v) -> Error (Some (failing env ~declared source (wasm_type w) v))
          | None -> Error None (* not a number yet: the call waits *)
        end
      | Some z ->
        let lo, hi = range w in
        let negative_for_N = (k = KN && Z.lt z Z.zero) in
        if Z.lt z lo || Z.gt z hi || negative_for_N then
          (* it fails as the cast of the argument to the module's type *)
          Error (Some (failing env ~declared ty (wasm_type w) a))
        else arguments (to_value w z :: acc) rest
  in
  let typed = List.map2 (fun p a -> p, a) b.params args in
  match arguments [] (List.map (fun (p, a) -> p, (a, type_of_kind env (fst p))) typed) with
  | Error None -> None
  | Error (Some failed) -> Some failed
  | Ok values ->
    let inst = instance b.file in
    let func = match Wasm.Instance.export inst (Wasm.Utf8.decode b.export) with
      | Some (Wasm.Instance.ExternFunc f) -> f
      | _ -> CErrors.user_err (str b.file ++ str " no longer exports the function " ++ str b.export ++ str ".") in
    let trapped msg =
      (* the message, as a string literal is ("..." is a Soma string) *)
      let message = fst (Constrintern.interp_constr env sigma
                           (CAst.make (Constrexpr.CPrim (Constrexpr.String msg)))) in
      Some (failing env ~declared (wasm_ref "trap")
              declared (EConstr.mkApp (wasm_ref "Trapped", [|message|]))) in
    match Wasm.Eval.invoke func values with
    | [r] ->
      begin match of_value r with
        | None -> None
        | Some z ->
          match rkind with
          | KN when Z.lt z Z.zero ->
            (* what the module gave, which an N cannot hold *)
            Some (failing env ~declared (wasm_type rw) declared (mk_wasm env rw z))
          | KN -> Some (mk_N z)
          | KZ -> Some (mk_Z z)
          | KI64 | KI32 -> Some (mk_wasm env rw z)
          | KAny -> Some (cast env (mk_ref "num.Z.type") (any_type env) (mk_Z z))
      end
    | _ -> None
    | exception Wasm.Eval.Trap (_, msg) -> trapped msg
    | exception Wasm.Eval.Exhaustion (_, msg) -> trapped msg
    | exception Wasm.Eval.Crash (_, msg) -> trapped msg

(* SomaForeign.step: the calls of [c] whose arguments are numbers, computed *)
let step env sigma c =
  if Cmap_env.is_empty !bindings then None else
  let changed = ref false in
  let rec visit c =
    let c = EConstr.map sigma visit c in
    match EConstr.kind sigma c with
    | App (f, args) ->
      begin match EConstr.kind sigma f with
        | Const (k, _) ->
          begin match Cmap_env.find_opt k !bindings with
            | Some b when Array.length args = List.length b.params ->
              (match call env sigma b (Array.to_list args) with
               | Some r -> changed := true; r
               | None -> c)
            | _ -> c
          end
        | _ -> c
      end
    | _ -> c
  in
  let c = visit c in
  if !changed then Some c else None

let describe c =
  match Cmap_env.find_opt c !bindings with
  | None -> None
  | Some b ->
    let kind = function KN -> "N" | KZ -> "Z" | KAny -> "Any" | KI64 -> "i64" | KI32 -> "i32" in
    Some (str (Filename.basename b.file) ++ str "'s " ++ str b.export ++ str " (" ++
          str (String.concat ", " (List.map (fun (_, w) -> wnum_name w) b.params)) ++ str ") -> " ++
          str (wnum_name (snd b.result)) ++ str ", taken to be " ++
          str (String.concat " -> " (List.map (fun (k, _) -> kind k) (b.params @ [b.result]))) ++
          str ", which each call checks")

let () =
  SomaForeign.step := step;
  SomaForeign.describe := describe
