#!/usr/bin/env bash
# Production test selector/receipt code with a controlled compiler callback.
# The callback supplies real trace shape; it never replaces receipt certainty.
set -euo pipefail
export SOMA_AUDIT_SOURCE="${SOMA_AUDIT_SOURCE:-$(cd "$(dirname "$0")/../.." && pwd -P)}"
python3 - <<'PY'
import os,pathlib,shutil,subprocess,tempfile
source=pathlib.Path(os.environ['SOMA_AUDIT_SOURCE'])
with tempfile.TemporaryDirectory(prefix='soma-negative-probes-') as tmp:
    outer=pathlib.Path(tmp);build=outer/'build';build.mkdir()
    for name in ['somaMerkle.ml','somaCache.ml','somaToml.ml','somaRuleInputs.ml']:shutil.copyfile(source/'clib'/name,build/name)
    shutil.copyfile(source/'topbin/somaTest.ml',build/'somaTest.ml')
    (build/'driver.ml').write_text(r'''
let build ~source ~trace ~no_image:_ =
  let root = Sys.getcwd () in
  let dependency = match Sys.getenv_opt "PROBE_DEPENDENCY" with Some p -> p | None -> "lib/item.soma" in
  Out_channel.with_open_bin trace (fun oc ->
      Printf.fprintf oc "soma-test-dependencies 2\nsource %S\nsource %S\n" source (Filename.concat root dependency));
  (match Sys.getenv_opt "PROBE_DURING" with
   | Some path -> Out_channel.with_open_bin path (fun oc -> output_string oc "(* created after simulated compilation *)\n")
   | None -> ());
  0
let () = SomaTest.run ~identity:(fun _ -> "controlled-compiler") ~build (List.tl (Array.to_list Sys.argv))
''')
    env=dict(os.environ,XDG_CACHE_HOME=str(outer/'xdg'),SOMA_CACHE_ID='negative-receipt-test')
    subprocess.run(['ocamlfind','ocamlc','-package','digestif.c,unix','-linkpkg','somaMerkle.ml','somaCache.ml','somaToml.ml','somaRuleInputs.ml','somaTest.ml','driver.ml','-o','driver'],cwd=build,env=env,check=True)
    def fixture(mode,ignored_config=False):
        root=outer/mode;root.mkdir();(root/'lib').mkdir();(root/'tests').mkdir();(root/'unrelated').mkdir()
        (root/'soma.toml').write_text('[project]\nname="probe"\nversion="0.1.0"\n')
        (root/'tests/main.soma').write_text('Import lib.item.\n')
        (root/'lib/item.soma').write_text('flag : bool := true.\n')
        (root/'unrelated/source.soma').write_text('unused : nat := 1.\n')
        (root/'.gitignore').write_text('.soma-cache/\n*.ext\n*.exp\n*.lang\n*.proof\nsoma.toml\nlib/lib.soma\n')
        for args in [['init','-q'],['add','.']]+([] if ignored_config else [['add','-f','soma.toml']])+[['-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','fixture']]:subprocess.run(['git',*args],cwd=root,check=True)
        return root
    def run(root,args,extra=None):
        p=subprocess.run([str(build/'driver'),*args],cwd=root,env=dict(env,**(extra or {})),text=True,capture_output=True,timeout=20)
        assert p.returncode==0,(root,args,p.stdout,p.stderr)
        return p
    for mode,path in [('paired','tests/main.exp'),('rule','lib/lib.ext'),('legacy','lib/lib.lang')]:
        root=fixture(mode)
        run(root,['--full']);assert run(root,['--changedSince','HEAD','--listTests']).stdout==''
        (root/path).write_text('new ignored compiler input\n')
        assert run(root,['--changedSince','HEAD','--listTests']).stdout=='tests/main.soma\n',mode
    root=fixture('priority');(root/'lib/lib.ext').write_text('source ext\n')
    subprocess.run(['git','add','-f','lib/lib.ext'],cwd=root,check=True);subprocess.run(['git','-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','ext source'],cwd=root,check=True)
    extra={'PROBE_DEPENDENCY':'lib/lib.ext'}
    run(root,['--full'],extra);assert run(root,['--changedSince','HEAD','--listTests'],extra).stdout==''
    (root/'lib/lib.soma').write_text('new preferred kind\n')
    assert run(root,['--changedSince','HEAD','--listTests'],extra).stdout=='tests/main.soma\n'
    root=fixture('config',True);seed=run(root,['--full']);assert 'next run will include' in seed.stderr
    (root/'soma.toml').write_text('[project]\nname="changed"\nversion="0.1.0"\n')
    assert run(root,['--changedSince','HEAD','--listTests']).stdout=='tests/main.soma\n'
    root=fixture('during');late='lib/lib.ext';seed=run(root,['--full'],{'PROBE_DURING':late});assert 'next run will include' in seed.stderr
    (root/late).unlink()
    assert run(root,['--changedSince','HEAD','--listTests']).stdout=='tests/main.soma\n','during-build input was certified posthoc'
    root=fixture('unrelated');(root/'unrelated/unrelated.ext').write_text('ignored, unrelated to recorded graph\n')
    run(root,['--full']);assert run(root,['--changedSince','HEAD','--listTests']).stdout==''
    (root/'unrelated/unrelated.ext').write_text('unrelated body edit\n')
    assert run(root,['--changedSince','HEAD','--listTests']).stdout==''
    print('Known ignored rule/companion/kind/config inputs invalidate receipts; during-build changes refuse certification; unrelated resources remain skippable: passed')
PY
