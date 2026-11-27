open SomaBuildPlan
module A = SomaArtifactUnits
module IO = SomaProjectBuild
let expect_error f = match f () with exception Error _ -> () | _ -> failwith "accepted unsafe artifact publication"
let write file contents = let oc=open_out_bin file in
  Fun.protect ~finally:(fun () -> close_out_noerr oc) (fun () -> output_string oc contents)
let () =
  let root=Filename.temp_file "soma-artifact-units-" "" in Sys.remove root; Unix.mkdir root 0o700;
  Fun.protect ~finally:(fun () -> IO.remove root) (fun () ->
      let file s=Filename.concat root s in
      let config=file "units.toml" and manifest=file "inventory.toml" in
      write (file "owner.soma") "checked source\n";
      write (file "types.exports") "type t = bool\n";
      write (file "values.exports") "let value = true\n";
      let recipe={|format=1
[units.public]
output="public.ml"
parts=[{owner="owner",product="types"},{whitespace="\n"},{owner="owner",product="values"}]
[units.second]
output="second.ml"
parts=[{owner="owner",product="values"}]
|} in
      write config recipe;
      let inventory ?(owner="owner") ?(types="types.exports") () =
        Printf.sprintf {|format=1
config-sha256=%S
[sources]
"owner.soma"=%S
[products.types]
owner=%S
path=%S
sha256=%S
[products.values]
owner="owner"
path="values.exports"
sha256=%S
|} (SomaMerkle.file_hash config) (SomaMerkle.file_hash (file "owner.soma")) owner types
          (SomaMerkle.file_hash (file "types.exports")) (SomaMerkle.file_hash (file "values.exports")) in
      let publish ?(selected=[]) ?(check=false) ()=A.execute ~config ~manifest ~selected ~check in
      write manifest (inventory ()); publish ();
      let expected="type t = bool\n\nlet value = true\n" in
      assert (IO.read (file "public.ml")=expected);
      let stamp=(Unix.stat (file "public.ml")).Unix.st_mtime in
      publish (); assert ((Unix.stat (file "public.ml")).Unix.st_mtime=stamp); publish ~check:true ();
      let intact ()=assert (IO.read (file "public.ml")=expected) in
      write (file "values.exports") "let value = false\n"; expect_error publish; intact ();
      write (file "values.exports") "let value = true\n";
      write manifest (inventory ~owner:"wrong" ()); expect_error publish; intact ();
      write manifest (inventory ~types:"../escape" ()); expect_error publish; intact ();
      write manifest (inventory ()); write (file "owner.soma") "changed source\n"; expect_error publish; intact ();
      write manifest (inventory ());
      write config (recipe ^ "extra=true\n"); expect_error publish; intact ();
      write config recipe; write manifest (inventory ());
      Unix.symlink (file "types.exports") (file "alias.exports");
      write manifest (inventory ~types:"alias.exports" ()); expect_error publish; intact ();
      write manifest (inventory ());
      expect_error (fun () -> publish ~selected:["missing"] ()); intact ();
      List.iter (fun bad -> expect_error (fun () -> A.layout bad)) [
        "format=1\n[units.u]\noutput='../escape.ml'\nparts=[{whitespace=' '}]";
        "format=1\n[units.u]\noutput='u.ml'\nparts=[{whitespace='let injected=()'}]";
        "format=1\n[units.u]\noutput='u.ml'\nparts=[{owner='o',product='x',slice='1:2'}]";
        "format=1\n[units.u]\noutput='u.ml'\nparts=[{owner='o',product='x'},{owner='o',product='x'}]";
        "format=1\n[units.a]\noutput='same.ml'\nparts=[{owner='o',product='x'}]\n[units.b]\noutput='same.ml'\nparts=[{owner='o',product='y'}]";
      ];
      (* A later selected failure must not publish an earlier valid output. *)
      Sys.remove (file "public.ml");
      write manifest (String.concat "" [inventory ();"\n[products.unused]\nowner='o'\npath='missing.exports'\nsha256='";String.make 64 '0';"'\n"]);
      (try publish () with Sys_error _ | Unix.Unix_error _ -> () | Error _ -> ());
      assert (not (Sys.file_exists (file "public.ml"))));
  print_endline "PASS: typed whole-unit order, unchanged publication, closed input hashes, schema/path/alias/owner checks and failed publication safety"
