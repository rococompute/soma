open SomaBuildPlan
let expect_error f =
  match f () with
  | exception Error _ -> ()
  | _ -> failwith "accepted an invalid build"
let parse s = match parse (SomaToml.parse s) with Some p -> p | None -> assert false
let graph = {|[build]
targets = ["public"]
[build.extract.source]
file = "main.soma"
[build.unit.prefix]
output = "prefix.ml"
parts = [{extract="source",kind="source-types",namespace="exports"}]
[build.unit.public]
output = "public.ml"
parts = [{unit="prefix"},{extract="source",kind="values",namespace="exports"}]
|}
let write file contents =
  let oc=open_out_bin file in Fun.protect ~finally:(fun () -> close_out_noerr oc) (fun () -> output_string oc contents)
let () =
  let special="héllo/quote\"\\\n\001.ml" in
  (match List.assoc "path" (SomaToml.parse ("path=" ^ SomaProjectBuild.toml_string special)) with
   | {value=SomaToml.String s;_} -> assert (s=special) | _ -> assert false);
  let p=parse graph in
  assert (List.map (fun n -> n.name) (order p p.targets) = ["source";"prefix";"public"]);
  List.iter (fun s -> expect_error (fun () -> parse s)) [
    graph ^ "unknown = true\n";
    "[build]\ntargets=[1]\n";
    "[build]\ndirectory='../escape'\n";
    "[build.extract.a]\nfile='main.soma'\noptions=['-o']\n";
    "[build.extract.a]\nfile='main.soma'\nverify='yes'\n";
    "[build.publish.a]\nextract='missing'\nfile='prog.ml'\noutput='a.ml'\n";
    "[build.extract.a]\nfile='main.soma'\n[build.publish.b]\nextract='a'\nfile='verification.toml'\noutput='b.ml'\n";
    "[build.extract.a]\nfile='main.soma'\n[build.publish.b]\nextract='a'\nfile='../escape.ml'\noutput='b.ml'\n";
    "[build.extract.a]\nfile='main.soma'\n[build.publish.b]\nextract='a'\nfile='prog.ml'\noutput='.extract/b.ml'\n";
    "[build.extract.a]\nfile='main.soma'\n[build.publish.b]\nextract='a'\nfile='prog.ml'\noutput='b.ml'\n[build.publish.c]\nextract='b'\nfile='prog.ml'\noutput='c.ml'\n";
    "[build.extract.a]\nfile='main.soma'\n[build.publish.b]\nextract='a'\nfile='prog.ml'\noutput='b.ml'\n[build.publish.c]\nextract='a'\nfile='prog.mli'\noutput='b.ml'\n";
    "[build.extract.a]\nfile='main.soma'\nneeds=['b']\n[build.extract.b]\nfile='b.soma'\nneeds=['a']\n";
    "[build.unit.a]\noutput='a.ml'\nparts=[{unit='missing'}]\n";
    "[build.unit.a]\noutput='a.ml'\nparts=[{whitespace='let x = 1'}]\n";
    "[build.unit.a]\noutput='.receipts/x.ml'\nparts=[{unit='a'}]\n";
    "[build.extract.a]\nfile='a.soma'\n[build.unit.a]\noutput='a.ml'\nparts=[{unit='a'}]\n";
    "[build.extract.e]\nfile='e.soma'\n[build.unit.a]\noutput='a.ml'\nparts=[{extract='e',kind='values',namespace='e'}]\n[build.unit.b]\noutput='a.ml'\nparts=[{unit='a'}]\n";
    "[build.extract.e]\nfile='e.soma'\n[build.unit.a]\noutput='a.ml'\nparts=[{extract='e',kind='raw-text',namespace='e'}]\n";
  ];
  let dir=Filename.temp_file "soma-build-test-" "" in
  Sys.remove dir; Unix.mkdir dir 0o700;
  Fun.protect ~finally:(fun () -> SomaProjectBuild.remove dir) (fun () ->
      let source=Filename.concat dir "source.definition" and file=Filename.concat dir "artifact.exports" in
      write source "checked Source\n"; write file "type t = bool\n";
      let manifest=Filename.concat dir "native_source_type_reexports.manifest" in
      let row ?(order="0") ?(scope="exports") ?(source_path="source.definition") ?(artifact="artifact.exports") () =
        Printf.sprintf "%S %S %S %S %S %S %S %S %s\n" "exports.t" scope source_path
          (SomaMerkle.file_hash source) artifact (SomaMerkle.file_hash file) "t" "bool" order in
      let put rows=write manifest ("soma-native-source-type-reexports-v1\n" ^ rows) in
      let select ()=SomaProjectBuild.artifact ~root:dir ~source_root:dir ~extract:"e" Source_types "exports" in
      put (row ()); assert ((select ()).contents="type t = bool\n");
      write file "type t = int\n"; expect_error select;
      put (row ()); write source "changed Source\n"; expect_error select;
      put (row ~order:"1" ()); expect_error select;
      put (row ~source_path:"../escape" ()); expect_error select;
      put (row () ^ row ~scope:"other" ()); expect_error select;
      put (row () ^ row ~order:"1" ~artifact:"second.exports" ()); expect_error select;
      Unix.symlink file (Filename.concat dir "linked.exports");
      put (row ~artifact:"linked.exports" ()); expect_error select;
      let binding name ordinal = Printf.sprintf "%S %S %S %S %S %S %S %S %d\n"
          ("exports." ^ name) "exports" "source.definition" (SomaMerkle.file_hash source)
          "artifact.exports" (SomaMerkle.file_hash file) name "target" ordinal in
      write (Filename.concat dir "native_value_reexports.manifest")
        ("soma-native-value-reexports-v1\n" ^ binding "value" 0);
      let projections=Filename.concat dir "native_binding_projections.manifest" in
      write projections ("soma-native-binding-projections-v1\n" ^ binding "projected" 1);
      let bindings ()=SomaProjectBuild.artifact ~root:dir ~source_root:dir ~extract:"e" Bindings "exports" in
      assert ((bindings ()).contents=SomaProjectBuild.read file);
      write projections ("soma-native-binding-projections-v1\n" ^ binding "projected" 0);
      expect_error bindings;
      let output=Filename.concat dir "public.ml" in
      write (Filename.concat dir ".soma-ocaml-files") ("artifact.exports " ^ SomaMerkle.file_hash file ^ "\n");
      let whole ()=SomaProjectBuild.whole_file ~root:dir ~extract:"e" "artifact.exports" in
      assert ((whole ()).contents=SomaProjectBuild.read file);
      write file "changed compiler output\n"; expect_error whole;
      write (Filename.concat dir ".soma-ocaml-files") ""; expect_error whole;
      expect_error (fun () -> SomaProjectBuild.whole_file ~root:dir ~extract:"e" "../outside");
      expect_error (fun () -> SomaProjectBuild.whole_file ~root:dir ~extract:"e" "linked.exports");
      assert (SomaProjectBuild.atomic output "previous checked output\n");
      let before=(Unix.stat output).Unix.st_mtime in
      assert (not (SomaProjectBuild.atomic output "previous checked output\n"));
      assert ((Unix.stat output).Unix.st_mtime=before));
  print_endline "project build: graph validation, whole-artifact/source hashes, order, containment and unchanged publication passed"
