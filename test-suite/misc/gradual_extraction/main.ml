(* Runs the code extracted from gradual_prog.v and compares each result with
   the value the kernel computes (the [Goal]s of gradual_prog.v, written here
   as this file prints values). The output is compared with main.out.

   As in the kernel, [unk] and [raise] at an inductive type extracted as an
   OCaml variant are values, printed as such below. The differences
   documented in GRADUAL.md ("Extraction differs from the kernel") are
   accepted and marked: eliminating them raises, where the kernel
   propagates them through the [match], and casts to a type mapped to an
   OCaml type (bool here) raise at once. Any other difference is reported
   as a disagreement. *)
open Gradual_prog

type outcome = Value of string | Raise of string | Unk of string

let contains s sub =
  let n = String.length s and m = String.length sub in
  let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
  go 0

let disagreements = ref 0

let run name f kernel =
  let outcome = match f () with
    | s -> Value s
    | exception Gradual_rt.Cast_error m -> Raise m
    | exception Gradual_rt.Unknown_term m -> Unk m
  in
  let shown, verdict = match outcome with
    | Value s -> s, if s = kernel then `Same else `Differs
    | Raise m ->
      "raise (" ^ m ^ ")",
      if kernel = "raise" then `Same else if contains kernel "raise" then `Documented else `Differs
    | Unk m ->
      "unk (" ^ m ^ ")",
      if kernel = "unk" then `Same else if contains kernel "unk" then `Documented else `Differs
  in
  match verdict with
  | `Same -> Printf.printf "%s = %s\n" name shown
  | `Documented -> Printf.printf "%s = %s (kernel: %s, documented difference)\n" name shown kernel
  | `Differs ->
    incr disagreements;
    Printf.printf "%s = %s DISAGREES with the kernel: %s\n" name shown kernel

(* Printers that look at a value only after checking it is not [unk] or
   [raise] (matching on those is undefined in OCaml). *)
let data show v =
  if Gradual_rt.is_unknown v then "unk" else if Gradual_rt.is_error v then "raise" else show v

let rec nat v = data (fun v ->
    let rec succs k v =
      if Gradual_rt.is_unknown v || Gradual_rt.is_error v then
        let rec wrap k x = if k = 0 then x else if k = 1 then "S " ^ x else "S (" ^ wrap (k - 1) x ^ ")" in
        wrap k (nat v)
      else match v with O -> string_of_int k | S p -> succs (k + 1) p
    in
    succs 0 v) v

let list show v =
  let rec items v = data (fun v -> match v with
      | Nil -> ""
      | Cons (x, Nil) -> show x
      | Cons (x, l) -> show x ^ "; " ^ items l) v
  in
  "[" ^ items v ^ "]"

let bool = string_of_bool
let rec tree v = data (fun (Node (x, f)) -> nat x ^ forest f) v
and forest v = data (function Fnil -> "" | Fcons (t, f) -> "(" ^ tree t ^ ")" ^ forest f) v
let rec rose v = data (fun (Rnode (x, l)) ->
    let rec kids l = data (function Nil -> "" | Cons (r, l) -> "(" ^ rose r ^ ")" ^ kids l) l in
    nat x ^ kids l) v
let pair f g v = data (fun (Pair (a, b)) -> "(" ^ f a ^ ", " ^ g b ^ ")") v
let option f v = data (function Some x -> "Some " ^ f x | None -> "None") v
let rec nth n l = match Gradual_rt.check l with
  | Nil -> failwith "nth" | Cons (x, l) -> if n = 0 then x else nth (n - 1) l
let one = S O

let () =
  run "t_ok" (fun () -> nat (t_ok ())) "42";
  run "t_bad" (fun () -> nat (t_bad ())) "raise";
  run "t_app" (fun () -> nat (t_app ())) "4";
  run "t_app_bad" (fun () -> nat (t_app_bad ())) "raise";
  run "t_list" (fun () -> list nat (t_list ())) "[1; 2]";
  run "t_list_bad" (fun () -> list nat (t_list_bad ())) "[1; raise]";
  run "t_list_bad_length" (fun () -> nat (t_list_bad_length ())) "2";
  run "t_list_bad_head" (fun () -> nat (t_list_bad_head ())) "1";
  run "t_pair" (fun () -> pair nat bool (t_pair ())) "(1, true)";
  run "t_pair_bad" (fun () -> pair bool nat (t_pair_bad ())) "(raise, raise)";
  run "t_option" (fun () -> option bool (t_option ())) "Some false";
  run "t_fs (first)" (fun () -> nat (nth 0 (t_fs ()) one)) "2";
  run "t_fs (second)" (fun () -> nat (nth 1 (t_fs ()) one)) "raise";
  run "t_record" (fun () -> nat (t_record ())) "1";
  run "t_record_bad" (fun () -> nat (t_record_bad ())) "raise";
  run "t_sig" (fun () -> nat (t_sig ())) "1";
  run "t_vec" (fun () -> nat (t_vec ())) "1";
  run "t_vec_bad" (fun () -> nat (vhead one (t_vec_bad ()))) "raise";
  run "t_dep" (fun () -> nat (t_dep ())) "2";
  run "t_dep_bad" (fun () -> nat (t_dep_bad ())) "raise";
  run "t_tree" (fun () -> tree (t_tree ())) "1(2)";
  run "t_tree_bad" (fun () -> tree (t_tree_bad ())) "1(raise)";
  run "t_tree_bad_root" (fun () -> nat (t_tree_bad_root ())) "1";
  run "t_rose" (fun () -> rose (t_rose ())) "1(2)";
  run "t_unk" (fun () -> nat (t_unk ())) "unk";
  run "t_unk_fun" (fun () -> nat (t_unk_fun ())) "unk";
  run "t_unk_dyn" (fun () -> nat (t_unk_dyn ())) "unk";
  run "t_unk_plus" (fun () -> nat (t_unk_plus ())) "S (S unk)";
  run "t_unk_elim" (fun () -> nat (t_unk_elim ())) "unk";
  run "t_err" (fun () -> nat (t_err ())) "raise";
  run "t_err_fun (cast)" (fun () -> let _ : nat -> nat = t_err_fun () in "<fun>") "<fun>";
  run "t_err_fun (call)" (fun () -> nat (t_err_fun () O)) "raise";
  run "t_sort_bad" (fun () -> nat (t_sort_bad ())) "raise";
  run "t_poly" (fun () -> nat (t_poly ())) "41";
  run "t_poly_bad" (fun () -> bool (t_poly_bad ())) "raise";
  run "t_poly_list" (fun () -> list nat (t_poly_list ())) "[1; 2]";
  run "t_poly_rec" (fun () -> list nat (t_poly_rec ())) "[1; 2]";
  run "t_poly_rec_bad" (fun () -> list bool (t_poly_rec_bad ())) "[raise; raise]";
  run "t_poly_local" (fun () -> list bool (t_poly_local ())) "[true]";
  run "t_poly_mutual" (fun () -> list nat (t_poly_mutual ())) "[1; 2; 3]";
  run "t_poly_fun" (fun () -> nat (t_poly_fun ())) "2";
  run "t_poly_fun_bad" (fun () -> nat (t_poly_fun_bad ())) "raise";
  (* t_omega loops *)
  Printf.printf "%d disagreements with the kernel\n" !disagreements
