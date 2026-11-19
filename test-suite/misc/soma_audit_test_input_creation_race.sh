#!/usr/bin/env bash
# An ignored rule appears after an imported module is read, while the real
# compiler checks a bounded proof. No completed receipt may bless that race.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0 SOMA_PROOF_JOBS=0
python3 - <<'PY'
import os,pathlib,signal,subprocess,tempfile,time
with tempfile.TemporaryDirectory(prefix='soma-real-input-race-') as tmp:
    outer=pathlib.Path(tmp).resolve();root=outer/'app';root.mkdir();(root/'lib').mkdir();(root/'tests').mkdir()
    (root/'soma.toml').write_text('[project]\nname="race"\nversion="0.1.0"\n')
    (root/'.gitignore').write_text('.soma-cache/\n*.ext\nready*\n')
    (root/'lib/item.soma').write_text('flag : bool := true.\n')
    main=root/'tests/main.soma';main.write_text('Import lib.item.\nvalue : bool := flag.\n')
    def git(*args):return subprocess.run(['git',*args],cwd=root,check=True)
    git('init','-q');git('add','.');git('-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','fixture')
    env=dict(os.environ,SOMA_CACHE=str(outer/'store'),XDG_CACHE_HOME=str(outer/'xdg'))
    seed=subprocess.run(['soma','test','--full'],cwd=root,env=env,text=True,capture_output=True,timeout=90)
    assert seed.returncode==0,(seed.stdout,seed.stderr)
    main.write_text('Import lib.item.\nRedirect "ready" Check nat.\nGoal True. Proof. do 500000 idtac. exact I. Qed.\nvalue : bool := flag.\n')
    git('add','tests/main.soma');git('-c','user.name=Audit','-c','user.email=audit@example.invalid','commit','-qm','bounded proof fixture')
    stdout=outer/'race.stdout';stderr=outer/'race.stderr'
    with stdout.open('w') as out,stderr.open('w') as err:
        process=subprocess.Popen(['soma','test','--full'],cwd=root,env=env,text=True,stdout=out,stderr=err,start_new_session=True)
        try:
            deadline=time.monotonic()+60
            while not any(p.exists() for p in [root/'ready',root/'ready.out']):
                assert process.poll() is None,(stdout.read_text(),stderr.read_text())
                assert time.monotonic()<deadline,'compiler did not reach controlled proof'
                time.sleep(.005)
            assert process.poll() is None,'proof ended before the membership edit'
            late=root/'lib/lib.ext';late.write_text('Notation "\'true\'" := false.\n')
            process.wait(timeout=90)
        finally:
            if process.poll() is None:os.killpg(process.pid,signal.SIGTERM);process.wait(timeout=10)
    assert process.returncode!=0 or 'next run will include' in stderr.read_text(),(stdout.read_text(),stderr.read_text())
    late.unlink()
    listed=subprocess.run(['soma','test','--changedSince','HEAD','--listTests'],cwd=root,env=env,text=True,capture_output=True,timeout=90)
    assert listed.returncode==0 and listed.stdout=='tests/main.soma\n',(listed.stdout,listed.stderr,stderr.read_text())
print('Real during-build ignored rule creation never publishes a completed test receipt: passed')
PY
