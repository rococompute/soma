let () =
  match Functor.Gradual_rt.force (Functor.roundtrip ()) with
  | Functor.N.B1 _ -> print_endline "application-aware type identity: ok"
  | _ -> failwith "roundtrip returned the wrong constructor"
