let () =
  if not (Functor.Gradual_rt.is_error (Functor.wrong_inside ())) then
    failwith "different functor applications were accepted as one runtime type";
  match Functor.Gradual_rt.force (Functor.roundtrip ()) with
  | Functor.N.B1 _ -> print_endline "application-aware type identity: ok"
  | _ -> failwith "roundtrip returned the wrong constructor"
