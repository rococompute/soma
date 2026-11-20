(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Soma: C modules. FILE.c, next to FILE.definition, is bound like an
   OCaml module (plugins/soma_ocaml: OCaml Bind C), whose OCaml is
   generated here: FILE.soma.h, the C declarations FILE.c defines, which
   it includes; the stubs that convert OCaml's values to C's and back; and
   the OCaml module of externals that the bindings call. FILE.c is plain C,
   with no OCaml in it.

   A declaration's type is made of these, each with its C type:
   - int (Rocq's primitive 63-bit integer), nat: int64_t (a nat never
     below 0: a negative result is 0)
   - bool: bool; float: double
   - word64 (Soma.Word64): uint64_t
   - string: soma_str { ptr; len } as an argument, valid during the call;
     as a result, a soma_buf the function fills with malloc'd bytes, which
     the stub copies and frees
   - a type the definition declares (ctx : Type.): soma_handle, an
     uintptr_t that Soma never looks into
   - unit, as the only argument (no arguments in C) or the result (void)
   - option of one of these, as the result: the function returns whether
     there is one, and writes it to its last argument
   Each declaration is the C function FILE_name. *)

type atom =
  | Int                 (* int, nat *)
  | Nat
  | Word                (* Soma.Word64's word64 *)
  | Buf                 (* Sandbox's buffer: OCaml's bytes, an argument *)
  | Bool
  | Float
  | Str
  | Handle of string    (* a declared type, by its name *)

type result = Unit | Value of atom | Optional of atom

type signature = {
  args : atom list;     (* [] when the only argument is unit *)
  result : result;
}

let trim = String.trim

(* split on " -> " outside parentheses *)
let arrows ty =
  let n = String.length ty in
  let parts = ref [] and depth = ref 0 and start = ref 0 in
  let i = ref 0 in
  while !i < n do
    (match ty.[!i] with
     | '(' -> incr depth
     | ')' -> decr depth
     | '-' when !depth = 0 && !i + 1 < n && ty.[!i + 1] = '>' ->
       parts := String.sub ty !start (!i - !start) :: !parts;
       start := !i + 2;
       incr i
     | _ -> ());
    incr i
  done;
  List.rev_map trim (String.sub ty !start (n - !start) :: !parts)

let strip_parens s =
  let s = trim s in
  if String.length s >= 2 && s.[0] = '(' && s.[String.length s - 1] = ')'
  then trim (String.sub s 1 (String.length s - 2)) else s

(* an atom of an OCaml type as soma_ocaml writes it: the module's own
   types are [Top.name] *)
let atom ~top s =
  match strip_parens s with
  | "Uint63.t" -> Ok Int
  | "Soma_nat.nat" -> Ok Nat
  | "Soma_word64.t" -> Ok Word
  | "Bytes.t" -> Ok Buf
  | "bool" -> Ok Bool
  | "float" -> Ok Float
  | "string" -> Ok Str
  | s ->
    let prefix = top ^ "." in
    let k = String.length prefix in
    if String.length s > k && String.sub s 0 k = prefix
       && not (String.contains (String.sub s k (String.length s - k)) '.')
       && not (String.contains s ' ')
    then Ok (Handle (String.sub s k (String.length s - k)))
    else Error s

let suffix = " option"

let result ~top s =
  let s = strip_parens s in
  if s = "unit" then Ok Unit
  else
    let n = String.length s and k = String.length suffix in
    let no_buffer = function Ok Buf -> Error "buffer result" | r -> r in
    if n > k && String.sub s (n - k) k = suffix then
      Result.map (fun a -> Optional a) (no_buffer (atom ~top (String.sub s 0 (n - k))))
    else Result.map (fun a -> Value a) (no_buffer (atom ~top s))

(* the signature of a declaration, from its OCaml type, or what in it C
   cannot take *)
let signature ~top ty =
  match arrows ty with
  | [] | [_] -> Error "a C module's value is a function (unit -> A for one without arguments)"
  | parts ->
    let rev = List.rev parts in
    let res = List.hd rev and args = List.rev (List.tl rev) in
    let res = result ~top res in
    let args = match args with
      | ["unit"] -> Ok []
      | args ->
        List.fold_right (fun a acc -> match acc, atom ~top a with
            | Ok l, Ok x -> Ok (x :: l)
            | (Error _ as e), _ -> e
            | _, Error s -> Error s) args (Ok []) in
    match args, res with
    | Ok args, Ok result -> Ok { args; result }
    | Error s, _ | _, Error s ->
      Error ("C has no " ^ s ^ ": a C module's arguments are int, nat, word64, bool, float, string, buffer (Sandbox's, written in place) or a type the definition declares (unit alone for none), its result one of these but buffer, unit, or an option of one")

(* the C name of a declaration *)
let c_name ~file name = file ^ "_" ^ name

(* the file's base name (lx_machine for lx_machine.c), as C names start *)
let base_of file = Filename.remove_extension (Filename.basename file)

let c_type = function
  | Int | Nat -> "int64_t"
  | Word -> "uint64_t"
  | Bool -> "bool"
  | Float -> "double"
  | Str -> "soma_str"
  | Buf -> "soma_bytes"
  | Handle _ -> "soma_handle"

let out_type = function
  | Str -> "soma_buf"
  | a -> c_type a

let prototype ~file (name, s) =
  let params = List.mapi (fun i a -> Printf.sprintf "%s a%d" (c_type a) i) s.args in
  let ret, params = match s.result with
    | Unit -> "void", params
    | Value Str -> "void", params @ ["soma_buf *out"]
    | Value a -> c_type a, params
    | Optional a -> "bool", params @ [out_type a ^ " *out"] in
  Printf.sprintf "%s %s(%s)" ret (c_name ~file name)
    (if params = [] then "void" else String.concat ", " params)

let header_h ~file ~definition sigs =
  let guard = "SOMA_" ^ String.uppercase_ascii file ^ "_H" in
  Printf.sprintf
    "/* Generated by Soma from %s (vernac/somaC.ml): the functions %s.c\n\
    \   defines, which Soma calls. Include it in %s.c. */\n\
     #ifndef %s\n#define %s\n\
     #include <stdint.h>\n#include <stdbool.h>\n#include <stddef.h>\n\
     #ifndef SOMA_C_TYPES\n#define SOMA_C_TYPES\n\
     /* a string argument: its bytes, valid only during the call */\n\
     typedef struct { const uint8_t *ptr; size_t len; } soma_str;\n\
     /* a string result: bytes from malloc, which Soma copies and frees */\n\
     typedef struct { uint8_t *ptr; size_t len; } soma_buf;\n\
     /* a buffer argument (Sandbox's): its bytes, which C may read and\n\
    \   write in place, valid only during the call */\n\
     typedef struct { uint8_t *ptr; size_t len; } soma_bytes;\n\
     /* a value of a type the definition declares, opaque to Soma */\n\
     typedef uintptr_t soma_handle;\n\
     #endif\n\n%s\n#endif\n"
    definition file file guard guard
    (String.concat "" (List.map (fun s -> prototype ~file s ^ ";\n") sigs))

(* OCaml value -> C *)
let of_value a v = match a with
  | Int | Nat -> Printf.sprintf "(int64_t)Long_val(%s)" v
  | Word -> Printf.sprintf "(uint64_t)Int64_val(%s)" v
  | Bool -> Printf.sprintf "(bool)Bool_val(%s)" v
  | Float -> Printf.sprintf "Double_val(%s)" v
  | Str -> Printf.sprintf "(soma_str){ (const uint8_t *)String_val(%s), caml_string_length(%s) }" v v
  | Buf -> Printf.sprintf "(soma_bytes){ (uint8_t *)Bytes_val(%s), caml_string_length(%s) }" v v
  | Handle _ -> Printf.sprintf "(soma_handle)Long_val(%s)" v

(* C -> OCaml value *)
let to_value a c = match a with
  | Int -> Printf.sprintf "Val_long(%s)" c
  | Nat -> Printf.sprintf "Val_long(%s < 0 ? 0 : %s)" c c
  | Word -> Printf.sprintf "caml_copy_int64((int64_t)%s)" c
  | Bool -> Printf.sprintf "Val_bool(%s)" c
  | Float -> Printf.sprintf "caml_copy_double(%s)" c
  | Str -> Printf.sprintf "soma_c_string(&%s)" c
  | Buf -> assert false (* refused by [result] *)
  | Handle _ -> Printf.sprintf "Val_long((intnat)%s)" c

let stub_name ~file name = file ^ "_soma_" ^ name

let stub ~file (name, s) =
  let n = List.length s.args in
  let vs = if n = 0 then ["v_unit"] else List.mapi (fun i _ -> Printf.sprintf "v%d" i) s.args in
  let params = String.concat ", " (List.map (fun v -> "value " ^ v) vs) in
  let args = List.mapi (fun i a -> Printf.sprintf "  %s a%d = %s;\n" (c_type a) i (of_value a (List.nth vs i))) s.args in
  let call extra = Printf.sprintf "%s(%s)" (c_name ~file name)
      (String.concat ", " (List.mapi (fun i _ -> Printf.sprintf "a%d" i) s.args @ extra)) in
  let body = match s.result with
    | Unit -> Printf.sprintf "  %s;\n  CAMLreturn(Val_unit);\n" (call [])
    | Value Str ->
      Printf.sprintf "  soma_buf out = { NULL, 0 };\n  %s;\n  res = soma_c_string(&out);\n  CAMLreturn(res);\n" (call ["&out"])
    | Value a ->
      Printf.sprintf "  %s r = %s;\n  res = %s;\n  CAMLreturn(res);\n" (c_type a) (call []) (to_value a "r")
    | Optional a ->
      Printf.sprintf "  %s out%s;\n  if (!%s) CAMLreturn(Val_none);\n  inner = %s;\n  res = caml_alloc_some(inner);\n  CAMLreturn(res);\n"
        (out_type a) (if a = Str then " = { NULL, 0 }" else "") (call ["&out"]) (to_value a "out") in
  let native = Printf.sprintf "value %s(%s)\n{\n  CAMLparam0();\n  CAMLlocal2(res, inner);\n  (void)inner; (void)res;\n%s%s%s}\n"
      (stub_name ~file name) params (if n = 0 then "  (void)v_unit;\n" else "") (String.concat "" args) body in
  (* OCaml passes more than 5 arguments to a bytecode stub as an array *)
  let byte = if n <= 5 then "" else
      Printf.sprintf "value %s_byte(value *argv, int argn)\n{\n  (void)argn;\n  return %s(%s);\n}\n"
        (stub_name ~file name) (stub_name ~file name)
        (String.concat ", " (List.init n (Printf.sprintf "argv[%d]"))) in
  native ^ byte

let stubs_c ~file sigs =
  Printf.sprintf
    "/* Generated by Soma (vernac/somaC.ml): OCaml's values to %s.c's and back. */\n\
     #define CAML_NAME_SPACE\n\
     #include <stdlib.h>\n#include <caml/mlvalues.h>\n#include <caml/memory.h>\n#include <caml/alloc.h>\n\
     #include \"%s.soma.h\"\n\n\
     /* a string result, copied, its malloc'd bytes freed */\n\
     static value soma_c_string(soma_buf *b)\n{\n\
    \  value s = caml_alloc_initialized_string(b->len, (const char *)(b->ptr ? (const char *)b->ptr : \"\"));\n\
    \  free(b->ptr);\n  b->ptr = NULL;\n  return s;\n}\n\n%s"
    file file (String.concat "\n" (List.map (stub ~file) sigs))

let ocaml_atom = function
  | Int | Nat | Handle _ -> "int"
  | Word -> "int64"
  | Bool -> "bool"
  | Float -> "float"
  | Str -> "string"
  | Buf -> "bytes"

(* FILE's OCaml module: its declared types, as the handles C gives (an
   OCaml int, which Soma never looks into), and its values, externals.
   Plain int rather than Uint63.t or Soma_nat.nat, which are int: an
   image builds this module in a library of its own, which cannot see the
   program's modules. *)
let module_ml ~file ~types ~labels sigs =
  "(* Generated by Soma (vernac/somaC.ml): " ^ file ^ ".c's functions, as OCaml externals. *)\n" ^
  String.concat "" (List.map (fun t -> Printf.sprintf "type %s = int\n" t) types) ^
  String.concat "" (List.map (fun (name, s) ->
      let ls = try List.assoc name labels with Not_found -> [] in
      let label i = match List.nth_opt ls i with Some (Some l) -> l ^ ":" | _ -> "" in
      let args = if s.args = [] then ["unit"] else List.mapi (fun i a -> label i ^ ocaml_atom a) s.args in
      let res = match s.result with
        | Unit -> "unit"
        | Value a -> ocaml_atom a
        | Optional a -> ocaml_atom a ^ " option" in
      let stub = stub_name ~file name in
      let names = if List.length s.args > 5 then Printf.sprintf "%S %S" (stub ^ "_byte") stub
        else Printf.sprintf "%S" stub in
      Printf.sprintf "external %s : %s -> %s = %s\n" name (String.concat " -> " args) res names) sigs)
