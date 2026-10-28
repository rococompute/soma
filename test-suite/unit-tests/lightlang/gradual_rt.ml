(* The runtime of casts in extracted code (plugins/extraction/gradual_rt.ml),
   which Lightlang's Mirage images run: casts that succeed, and the words
   of those that fail *)

open Utest
open Extraction_plugin.Gradual_rt

let log_out_ch = open_log_out_ch __FILE__

let nat = ind "Corelib.Init.Datatypes.nat" false []
let bool = ind "Corelib.Init.Datatypes.bool" false []
let int = prim "int"
let float = prim "float"
(* a type whose values can hold [err]: a failure is then a value *)
let data_list = ind "Corelib.Init.Datatypes.list" true [ty_arg nat]

(* The message of the [Cast_error] that [f] raises *)
let cast_error f =
  match f () with
  | _ -> "no error"
  | exception Cast_error msg -> msg

let same_type = mk_eq_test "gradual-rt-same-type"
    "a cast to the same type is the value"
    3 (Obj.obj (cast nat nat (Obj.repr 3)))

let through_unknown = mk_eq_test "gradual-rt-through-unknown"
    "a value injected into ? and projected back is itself"
    3 (Obj.obj (cast unknown_ty nat (cast nat unknown_ty (Obj.repr 3))))

let mismatch = mk_eq_test "gradual-rt-mismatch"
    "different types: expected and actual, by short names"
    "expected a bool, but got a nat"
    (cast_error (fun () -> cast nat bool (Obj.repr 3)))

let mismatch_through_unknown = mk_eq_test "gradual-rt-mismatch-through-unknown"
    "a value of type ? projected to another type: the type it was injected from"
    "expected a bool, but got a nat"
    (cast_error (fun () -> cast unknown_ty bool (cast nat unknown_ty (Obj.repr 3))))

let article = mk_eq_test "gradual-rt-article"
    "an int, before a vowel"
    "expected a float, but got an int"
    (cast_error (fun () -> cast int float (Obj.repr 3)))

let fn = mk_eq_test "gradual-rt-function"
    "a function where data is expected"
    "expected a nat, but got a function"
    (cast_error (fun () -> cast (pi nat (fun _ -> nat)) nat (Obj.repr (fun x -> x))))

let arguments = mk_eq_test "gradual-rt-arguments"
    "the arguments of an inductive type, by short names"
    "expected a nat, but got a list nat"
    (cast_error (fun () -> cast data_list nat (Obj.repr [])))

let failure_is_value = mk_bool_test "gradual-rt-failure-is-value"
    "a failed cast to a type that can hold err is an error value, raised when matched"
    (let v = cast nat data_list (Obj.repr 3) in
     is_error v && cast_error (fun () -> check v) = "expected a list nat, but got a nat")

let tests = [ same_type; through_unknown; mismatch; mismatch_through_unknown; article;
              fn; arguments; failure_is_value ]

let _ = run_tests __FILE__ log_out_ch tests
