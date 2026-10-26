(* Runs the code extracted from gradual_prog.v; the output is compared with
   main.out. *)
open Gradual_prog

let run name f =
  match f () with
  | s -> Printf.printf "%s = %s\n" name s
  | exception Gradual_rt.Cast_error m -> Printf.printf "%s: Cast_error (%s)\n" name m
  | exception Gradual_rt.Unknown_term m -> Printf.printf "%s: Unknown_term (%s)\n" name m

let ints l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]"
let rec tree (Node (x, f)) = string_of_int x ^ forest f
and forest = function Fnil -> "" | Fcons (t, f) -> "(" ^ tree t ^ ")" ^ forest f
let rec rose (Rnode (x, l)) = string_of_int x ^ String.concat "" (List.map (fun r -> "(" ^ rose r ^ ")") l)

let () =
  run "t_ok" (fun () -> string_of_int (t_ok ()));
  run "t_bad" (fun () -> string_of_int (t_bad ()));
  run "t_app" (fun () -> string_of_int (t_app ()));
  run "t_app_bad" (fun () -> string_of_int (t_app_bad ()));
  run "t_list" (fun () -> ints (t_list ()));
  run "t_list_bad" (fun () -> ints (t_list_bad ()));
  run "t_pair" (fun () -> let (n, b) = t_pair () in Printf.sprintf "(%d, %b)" n b);
  run "t_pair_bad" (fun () -> let (b, n) = t_pair_bad () in Printf.sprintf "(%b, %d)" b n);
  run "t_option" (fun () -> match t_option () with Some b -> string_of_bool b | None -> "None");
  run "t_fs (cast)" (fun () -> string_of_int (List.length (t_fs ())));
  run "t_fs (first)" (fun () -> string_of_int (List.nth (t_fs ()) 0 1));
  run "t_fs (second)" (fun () -> string_of_int (List.nth (t_fs ()) 1 1));
  run "t_record" (fun () -> string_of_int (t_record ()));
  run "t_record_bad" (fun () -> string_of_int (t_record_bad ()));
  run "t_sig" (fun () -> string_of_int (t_sig ()));
  run "t_vec" (fun () -> string_of_int (t_vec ()));
  run "t_vec_bad" (fun () -> string_of_int (vhead 1 (t_vec_bad ())));
  run "t_dep" (fun () -> string_of_int (t_dep ()));
  run "t_dep_bad" (fun () -> string_of_int (t_dep_bad ()));
  run "t_tree" (fun () -> tree (t_tree ()));
  run "t_tree_bad" (fun () -> tree (t_tree_bad ()));
  run "t_rose" (fun () -> rose (t_rose ()));
  run "t_unk" (fun () -> string_of_int (t_unk ()));
  run "t_unk_fun" (fun () -> string_of_int (t_unk_fun ()));
  run "t_unk_dyn" (fun () -> string_of_int (t_unk_dyn ()));
  run "t_err" (fun () -> string_of_int (t_err ()));
  run "t_err_fun (cast)" (fun () -> let _ : int -> int = t_err_fun () in "<fun>");
  run "t_err_fun (call)" (fun () -> string_of_int (t_err_fun () 0));
  run "t_sort_bad" (fun () -> string_of_int (t_sort_bad ()));
  run "t_poly" (fun () -> string_of_int (t_poly ()));
  run "t_poly_bad" (fun () -> string_of_bool (t_poly_bad ()));
  run "t_poly_list" (fun () -> ints (t_poly_list ()));
  run "t_poly_rec" (fun () -> ints (t_poly_rec ()));
  run "t_poly_rec_bad" (fun () -> String.concat "; " (List.map string_of_bool (t_poly_rec_bad ())));
  run "t_poly_local" (fun () -> String.concat "; " (List.map string_of_bool (t_poly_local ())));
  run "t_poly_mutual" (fun () -> ints (t_poly_mutual ()));
  run "t_poly_fun" (fun () -> string_of_int (t_poly_fun ()));
  run "t_poly_fun_bad" (fun () -> string_of_int (t_poly_fun_bad ()))
  (* t_omega loops *)
