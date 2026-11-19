#!/usr/bin/env bash
# Experimental E1 acceptance: one shared runtime must protect a cast-free
# consumer and dynamic casts, not just recognize another module's marker.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_EXPERIMENTAL_SHARED_EXTRACTION=1
export SOMA_OCAML_BUILD=0 SOMA_MIRAGE_BUILD=0
export SOMA_AUDIT_SOURCE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
python3 - <<'PY'
import os, pathlib, shutil, subprocess, tempfile

root = pathlib.Path(tempfile.mkdtemp(prefix="soma-shared-gradual-")).resolve()
env = dict(os.environ, SOMA_CACHE=str(root / "cache"))
def run(args, cwd, timeout=90):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            capture_output=True, timeout=timeout)
    assert result.returncode == 0, (str(cwd), args, result.returncode, result.stdout, result.stderr)
    return result

producer = '''From Corelib.Gradual Require Import Gradual.
Inductive Box (A : Type) : Type := B0 : Box A | B1 : A -> Box A.
Definition unknown_nat (_ : unit) : nat := unk.
Definition unknown_list (_ : unit) : list nat := unk.
Definition error_list (_ : unit) : list nat := raise.
Definition unknown_box (_ : unit) : Box nat := unk.
Definition error_box (_ : unit) : Box nat := raise.
Definition box_with_unknown (_ : unit) : Box nat := B1 nat unk.
Definition boxed_two (_ : unit) : Box nat := B1 nat 2.
Definition boxed_dynamic (_ : unit) : Box Any := B1 Any (cast nat Any 2).
Definition dynamic_two (_ : unit) : Any := cast nat Any 2.
Definition dynamic_bad (_ : unit) : Any := cast bool Any true.
Definition dynamic_box (_ : unit) : Any := cast (Box nat) Any (B1 nat 2).
Definition box_from_dynamic (b : Box Any) : Box nat := cast (Box Any) (Box nat) b.
'''
consumer = '''Require Import Producer Soma_gradual_rt.
Definition generic_head {A} (fallback : A) (xs : list A) : A :=
  match xs with nil => fallback | cons x _ => x end.
Definition generic_unbox {A} (fallback : A) (b : Box A) : A :=
  match b with B0 _ => fallback | B1 _ x => x end.
Definition reserved_zero := Soma_gradual_rt.zero.
'''
casts = '''Require Import Producer Consumer.
From Corelib.Gradual Require Import Gradual.
Definition from_dynamic_nat (x : Any) : nat := cast Any nat x.
Definition from_dynamic_box (x : Any) : Box nat := cast Any (Box nat) x.
Definition box_to_dynamic (b : Box nat) : Box Any := cast (Box nat) (Box Any) b.
'''
references = (
    ["Producer." + name for name in
     ["unknown_nat", "unknown_list", "error_list", "unknown_box", "error_box",
      "box_with_unknown", "boxed_two", "boxed_dynamic", "dynamic_two", "dynamic_bad",
      "dynamic_box", "box_from_dynamic"]] +
    ["Consumer.generic_head", "Consumer.generic_unbox", "Consumer.reserved_zero",
     "CastConsumer.from_dynamic_nat", "CastConsumer.from_dynamic_box", "CastConsumer.box_to_dynamic"])
harness = '''
let rec nat = function D.O -> 0 | D.S n -> 1 + nat n
let unknown f = try f (); failwith "missing Unknown_term" with R.Unknown_term _ -> ()
let error f = try f (); failwith "missing Cast_error" with R.Cast_error _ -> ()
let box_two = function P.B1 n -> assert (nat (R.force n) = 2) | P.B0 -> failwith "wrong box"
let () =
  (* Register the same canonical constructor cast from different modules in
     both orders, in separate fresh processes. *)
  if Sys.argv.(1) = "producer-first" then
    box_two (P.box_from_dynamic (P.boxed_dynamic ()))
  else ignore (X.box_to_dynamic (P.boxed_two ()));
  box_two (P.box_from_dynamic (X.box_to_dynamic (P.boxed_two ())));
  box_two (P.box_from_dynamic (P.boxed_dynamic ()));
  assert (R.is_unknown (P.unknown_nat ()));
  unknown (fun () -> ignore (C.generic_head D.O (P.unknown_list ())));
  error (fun () -> ignore (C.generic_head D.O (P.error_list ())));
  unknown (fun () -> ignore (C.generic_unbox D.O (P.unknown_box ())));
  error (fun () -> ignore (C.generic_unbox D.O (P.error_box ())));
  let nested = C.generic_unbox D.O (P.box_with_unknown ()) in
  assert (R.is_unknown nested);
  unknown (fun () -> ignore (R.force nested));
  assert (nat (R.force (X.from_dynamic_nat (P.dynamic_two ()))) = 2);
  error (fun () -> ignore (R.force (X.from_dynamic_nat (P.dynamic_bad ()))));
  box_two (X.from_dynamic_box (P.dynamic_box ()));
  assert (nat C.reserved_zero = 0);
  print_endline "unknown/error guards, nested data, casts, canonical registration and reserved names: ok"
'''

try:
    (root / "Producer.v").write_text(producer)
    (root / "Soma_gradual_rt.v").write_text("Definition zero := 0.\n")
    (root / "Consumer.v").write_text(consumer)
    (root / "CastConsumer.v").write_text(casts)
    for source in ["Producer.v", "Soma_gradual_rt.v", "Consumer.v", "CastConsumer.v"]:
        run(["rocq", "c", "-q", source], root)

    results = []
    for mode in ["separate", "library", "recursive", "monolithic"]:
        output = root / mode
        output.mkdir()
        prelude = ('Require Import Producer Consumer CastConsumer.\n'
                   'From Corelib Require Extraction.\n'
                   'Extract Inductive unit => "unit" [ "()" ].\n'
                   'Extract Inductive bool => "bool" [ "true" "false" ].\n'
                   'Set Extraction Output Directory "%s".\n' % output)
        if mode == "separate":
            command = "Separate Extraction " + " ".join(references) + ".\n"
        elif mode == "library":
            command = ("Separate Extraction " + " ".join(references) + ".\n" +
                       "Extraction Library Producer.\nExtraction Library Consumer.\n"
                       "Extraction Library CastConsumer.\n")
        elif mode == "recursive":
            command = "Recursive Extraction Library CastConsumer.\n"
        else:
            command = 'Extraction "Mono" ' + " ".join(references) + ".\n"
        request = root / ("Request_" + mode + ".v")
        request.write_text(prelude + command)
        run(["rocq", "c", "-q", request.name], root)
        if mode == "monolithic":
            aliases = "module P = Mono\nmodule C = Mono\nmodule X = Mono\nmodule D = Mono\nmodule R = Mono.Gradual_rt\n"
            assert not (output / "soma_gradual_rt.ml").exists()
        else:
            assert (output / "soma_gradual_rt.ml").is_file()
            assert "module Gradual_rt = Soma_gradual_rt" in (output / "Consumer.ml").read_text()
            assert "Gradual_rt.check" in (output / "Consumer.ml").read_text()
            aliases = "module P = Producer\nmodule C = Consumer\nmodule X = CastConsumer\nmodule D = Datatypes\nmodule R = Soma_gradual_rt\n"
        sources = sorted(path.name for path in output.glob("*.ml"))
        order = run(["ocamldep", "-sort"] + sources, output).stdout.split()
        for source in order:
            interface = pathlib.Path(source).with_suffix(".mli")
            if (output / interface).exists():
                run(["ocamlc", "-w", "-a", "-c", str(interface)], output)
            run(["ocamlc", "-w", "-a", "-c", source], output)
        (output / "main.ml").write_text(aliases + harness)
        run(["ocamlc", "-w", "-a"] + [str(pathlib.Path(s).with_suffix(".cmo")) for s in order] +
            ["main.ml", "-o", "main.exe"], output)
        for registration in ["producer-first", "consumer-first"]:
            results.append(run(["./main.exe", registration], output).stdout)
    assert len(set(results)) == 1, results

    # The shared helper is subject to the same Soma project confinement.
    project = root / "project"
    project.mkdir()
    caller = root / "caller"
    caller.mkdir()
    (project / "soma.toml").write_text('[project]\nname = "shared_gradual"\nversion = "0.1.0"\n')
    (project / "main.soma").write_text(
        'From Corelib.Gradual Require Import Gradual.\nFrom Corelib Require Extraction.\n'
        'Definition value (_ : unit) : nat := unk.\nSeparate Extraction value.\n')
    run(["soma", "build", str(project / "main.soma")], caller)
    assert (project / "soma_gradual_rt.ml").is_file()
    assert not list(caller.glob("*.ml*")), list(caller.iterdir())
    # A helper cannot overwrite an unrelated source or escape via a symlink.
    for linked in [False, True]:
        protected = root / ("protected_link" if linked else "protected_file")
        protected.mkdir()
        (protected / "soma.toml").write_text('[project]\nname = "protected"\nversion = "0.1.0"\n')
        shutil.copy(project / "main.soma", protected / "main.soma")
        target = protected / "soma_gradual_rt.ml"
        victim = root / "outside-runtime.ml"
        victim.write_text("outside sentinel\n")
        if linked:
            target.symlink_to(victim)
        else:
            target.write_text("unrelated source\n")
        result = subprocess.run(["soma", "build", str(protected / "main.soma")],
                                cwd=caller, env=env, text=True, capture_output=True, timeout=60)
        assert result.returncode != 0, (result.stdout, result.stderr)
        diagnostic = " ".join(result.stderr.split())
        assert ("inside the project" if linked else "not generated by Soma") in diagnostic, diagnostic
        assert victim.read_text() == "outside sentinel\n"
        if not linked:
            assert target.read_text() == "unrelated source\n"
        assert not (protected / "main.ml").exists()
    # Ordinary runtime-free modular extraction does not acquire a runtime ABI
    # dependency merely because the experimental backend is available.
    plain = root / "plain"
    plain.mkdir()
    (plain / "Plain.v").write_text('From Corelib Require Extraction.\n'
        'Definition identity (A : Type) (x : A) := x.\nSeparate Extraction identity.\n')
    run(["rocq", "c", "-q", "Plain.v"], plain)
    assert not (plain / "soma_gradual_rt.ml").exists()
    assert "Gradual_rt" not in (plain / "Plain.ml").read_text()
    # Module result brands must agree inside/outside one application,
    # propagate through aliases, and differ across separate applications.
    fixture = pathlib.Path(os.environ["SOMA_AUDIT_SOURCE_ROOT"]) / \
        "test-suite/misc/soma_audit_shared_gradual/functor_identity.v"
    functor = root / "functor"
    functor.mkdir()
    body = fixture.read_text()
    body = body[:body.rindex('Extraction "Functor"')]
    (functor / "BrandFunctor.v").write_text(body)
    run(["rocq", "c", "-q", "BrandFunctor.v"], functor)
    names = ["roundtrip", "wrong", "wrong_inside", "aliased", "second_wrong",
             "wrapped_roundtrip", "wrapped_roundtrip2", "argument_roundtrip",
             "argument_alias", "argument_reexport", "argument_wrong"]
    refs = " ".join("BrandFunctor." + name for name in names)
    functor_harness = r'''
let rec nat = function D.O -> 0 | D.S n -> 1 + nat n
let err value = assert (R.is_error value)
let () =
  if Sys.argv.(1) = "first" then begin
    (match F.wrapped_roundtrip () with F.N.W1 n -> assert (nat n = 2) | _ -> assert false);
    (match F.wrapped_roundtrip2 () with F.N2.W1 n -> assert (nat n = 2) | _ -> assert false)
  end else begin
    (match F.wrapped_roundtrip2 () with F.N2.W1 n -> assert (nat n = 2) | _ -> assert false);
    (match F.wrapped_roundtrip () with F.N.W1 n -> assert (nat n = 2) | _ -> assert false)
  end;
  (match R.force (F.roundtrip ()) with F.N.B1 n -> assert (nat n = 2) | _ -> assert false);
  (match R.force (F.aliased ()) with F.Alias.B1 n -> assert (nat n = 2) | _ -> assert false);
  err (F.wrong ()); err (F.wrong_inside ()); err (F.second_wrong ());
  (match R.force (F.argument_roundtrip ()) with F.Input.T1 n -> assert (nat n = 2) | _ -> assert false);
  (match R.force (F.argument_alias ()) with F.InputAlias.T1 n -> assert (nat n = 2) | _ -> assert false);
  (match R.force (F.argument_reexport ()) with F.InputReexport.T1 n -> assert (nat n = 2) | _ -> assert false);
  err (F.argument_wrong ());
  print_endline "functor applications, aliases, constructor brands and kernel cast parity: ok"
'''
    for mode in ["monolithic", "separate", "library", "recursive"]:
        output = functor / mode
        output.mkdir()
        if mode == "monolithic":
            command = 'Extraction "Functor" ' + refs + '.\n'
        elif mode == "separate":
            command = 'Separate Extraction ' + refs + '.\n'
        elif mode == "library":
            command = 'Separate Extraction ' + refs + '.\nExtraction Library BrandFunctor.\n'
        else:
            command = 'Recursive Extraction Library BrandFunctor.\n'
        request = functor / ("Request_" + mode + ".v")
        request.write_text('Require Import BrandFunctor.\nFrom Corelib Require Extraction.\n'
            'Extract Inductive unit => "unit" [ "()" ].\n'
            'Set Extraction Output Directory "%s".\n' % output + command)
        run(["rocq", "c", "-q", request.name], functor)
        unit = "Functor" if mode == "monolithic" else "BrandFunctor"
        datatype = "Functor" if mode == "monolithic" else "Datatypes"
        aliases = "module F = %s\nmodule R = %s.Gradual_rt\nmodule D = %s\n" % (unit, unit, datatype)
        sources = sorted(path.name for path in output.glob("*.ml"))
        order = run(["ocamldep", "-sort"] + sources, output).stdout.split()
        for source in order:
            interface = pathlib.Path(source).with_suffix(".mli")
            if (output / interface).exists():
                run(["ocamlc", "-w", "-a", "-c", str(interface)], output)
            run(["ocamlc", "-w", "-a", "-c", source], output)
        (output / "main.ml").write_text(aliases + functor_harness)
        run(["ocamlc", "-w", "-a"] + [str(pathlib.Path(s).with_suffix(".cmo")) for s in order] +
            ["main.ml", "-o", "main.exe"], output)
        for registration in ["first", "second"]:
            run(["./main.exe", registration], output)
    print("shared gradual execution parity for Separate/Library/Recursive/monolithic and project confinement: ok")
except BaseException:
    print("Preserved failing shared-runtime fixtures at", root, flush=True)
    raise
else:
    shutil.rmtree(root)
PY
