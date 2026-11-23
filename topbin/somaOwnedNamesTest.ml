(* Exercise collision handling independently of the digest's collision
   resistance. Native logical identities always keep their full names. *)
let () =
  let check=SomaOcamlBindings.check_owned_module_names in
  check ["Soma_owned_digest",("schema.A","item");"Soma_owned_other",("schema.B","item")];
  check ["Soma_owned_digest",("schema.A","item");"Soma_owned_digest",("schema.A","item")];
  let rejected=try
    check ["Soma_owned_digest",("schema.A__B","item");"soma_owned_digest",("schema.A.B","item")];false
    with e when CErrors.noncritical e->true in
  if not rejected then failwith "owned canonical declarations silently shared an emitted module";
  let record={SomaForeign.record_namespace=String.make 70 'n';record_name=String.make 60 'r';
    record_source="schema.definition";record_fields=[]}in
  if String.length(SomaForeign.native_record_filename record)>100 then failwith "unbounded owned filename";
  print_endline "owned emitted names: bounded filenames and explicit collision rejection passed"
