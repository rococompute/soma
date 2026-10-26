(* Runs the code extracted from gradual_prog.v and compares each result with
   the value the kernel computes (the [Goal]s of gradual_prog.v, written here
   as this file prints values). The output is compared with main.out.

   The differences documented in GRADUAL.md ("Extraction differs from the
   kernel") are accepted and marked: a failed cast raises at once, also
   inside data where the kernel keeps [raise], and [unk] at an inductive
   type raises [Unknown_term] where the kernel keeps [unk]. Any other
   difference is reported as a disagreement. *)
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

let ints l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]"
let bools l = "[" ^ String.concat "; " (List.map string_of_bool l) ^ "]"
let rec tree (Node (x, f)) = string_of_int x ^ forest f
and forest = function Fnil -> "" | Fcons (t, f) -> "(" ^ tree t ^ ")" ^ forest f
let rec rose (Rnode (x, l)) = string_of_int x ^ String.concat "" (List.map (fun r -> "(" ^ rose r ^ ")") l)
let int = string_of_int

let () =
  run "t_ok" (fun () -> int (t_ok ())) "42";
  run "t_bad" (fun () -> int (t_bad ())) "raise";
  run "t_app" (fun () -> int (t_app ())) "4";
  run "t_app_bad" (fun () -> int (t_app_bad ())) "raise";
  run "t_list" (fun () -> ints (t_list ())) "[1; 2]";
  run "t_list_bad" (fun () -> ints (t_list_bad ())) "[1; raise]";
  run "t_pair" (fun () -> let (n, b) = t_pair () in Printf.sprintf "(%d, %b)" n b) "(1, true)";
  run "t_pair_bad" (fun () -> let (b, n) = t_pair_bad () in Printf.sprintf "(%b, %d)" b n)
    "(raise, raise)";
  run "t_option" (fun () -> match t_option () with
      | Some b -> "Some " ^ string_of_bool b | None -> "None") "Some false";
  run "t_fs (first)" (fun () -> int (List.nth (t_fs ()) 0 1)) "2";
  run "t_fs (second)" (fun () -> int (List.nth (t_fs ()) 1 1)) "raise";
  run "t_record" (fun () -> int (t_record ())) "1";
  run "t_record_bad" (fun () -> int (t_record_bad ())) "raise";
  run "t_sig" (fun () -> int (t_sig ())) "1";
  run "t_vec" (fun () -> int (t_vec ())) "1";
  run "t_vec_bad" (fun () -> int (vhead 1 (t_vec_bad ()))) "raise";
  run "t_dep" (fun () -> int (t_dep ())) "2";
  run "t_dep_bad" (fun () -> int (t_dep_bad ())) "raise";
  run "t_tree" (fun () -> tree (t_tree ())) "1(2)";
  run "t_tree_bad" (fun () -> tree (t_tree_bad ())) "1(raise)";
  run "t_rose" (fun () -> rose (t_rose ())) "1(2)";
  run "t_unk" (fun () -> int (t_unk ())) "unk";
  run "t_unk_fun" (fun () -> int (t_unk_fun ())) "unk";
  run "t_unk_dyn" (fun () -> int (t_unk_dyn ())) "unk";
  run "t_err" (fun () -> int (t_err ())) "raise";
  run "t_err_fun (cast)" (fun () -> let _ : int -> int = t_err_fun () in "<fun>") "<fun>";
  run "t_err_fun (call)" (fun () -> int (t_err_fun () 0)) "raise";
  run "t_sort_bad" (fun () -> int (t_sort_bad ())) "raise";
  run "t_poly" (fun () -> int (t_poly ())) "41";
  run "t_poly_bad" (fun () -> string_of_bool (t_poly_bad ())) "raise";
  run "t_poly_list" (fun () -> ints (t_poly_list ())) "[1; 2]";
  run "t_poly_rec" (fun () -> ints (t_poly_rec ())) "[1; 2]";
  run "t_poly_rec_bad" (fun () -> bools (t_poly_rec_bad ())) "[raise; raise]";
  run "t_poly_local" (fun () -> bools (t_poly_local ())) "[true]";
  run "t_poly_mutual" (fun () -> ints (t_poly_mutual ())) "[1; 2; 3]";
  run "t_poly_fun" (fun () -> int (t_poly_fun ())) "2";
  run "t_poly_fun_bad" (fun () -> int (t_poly_fun_bad ())) "raise";
  (* t_omega loops *)
  Printf.printf "%d disagreements with the kernel\n" !disagreements
