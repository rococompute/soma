#!/usr/bin/env bash
# Root no-op checks must not skip a default rc that appeared outside the
# project. Real rc execution remains enabled; imports/check traces stay
# uncertified while rc is loaded, and removal permits a fresh normal build.
set -euo pipefail
export PATH="$BIN:$PATH"
python3 - <<'PY'
import json,os,pathlib,subprocess,tempfile
observe=os.environ.get('SOMA_RC_AUDIT_OBSERVE')=='1'
records=[];failures=[]
def expect(ok,label):
    if not ok:
        failures.append(label)
        if not observe:raise AssertionError(label)
with tempfile.TemporaryDirectory(prefix='soma-rc-freshness-') as tmp:
    work=pathlib.Path(tmp).resolve();root=work/'app';root.mkdir()
    home=work/'home';home.mkdir();config=work/'config';(config/'coq').mkdir(parents=True)
    (root/'soma.toml').write_text('[project]\nname="rc_audit"\nversion="0.1.0"\n')
    source=root/'main.soma';source.write_text('Import part.\nvalue : nat := part.value.\n')
    (root/'part.soma').write_text('value : nat := 1.\n')
    env=dict(os.environ,HOME=str(home),XDG_CONFIG_HOME=str(config),XDG_CACHE_HOME=str(work/'cache'),
             SOMA_CACHE=str(work/'shared'),SOMA_MIRAGE_BUILD='0',SOMA_OCAML_BUILD='0')
    for key in ['SOMA_PROJECT_ROOT','SOMA_PROJECT_CACHE','SOMA_BUILD_ROOT','ROCQPATH','COQPATH']:
        env.pop(key,None)
    def run(stage,args,success=True,extra=None):
        p=subprocess.run(['soma']+args,cwd=root,env=dict(env,**(extra or {})),text=True,
                         capture_output=True,timeout=90)
        records.append(dict(stage=stage,args=args,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))
        expect((p.returncode==0)==success,stage+': unexpected exit '+str(p.returncode))
        return p
    def fresh(stage,success):return run(stage,['build','--check-fresh','main.soma'],success)
    run('absent-build',['build','main.soma']);fresh('absent-fresh',True)
    rc=config/'coq/coqrc';rc.write_text('Set Printing All.\n')
    fresh('appeared-rc-stale',False)
    p=run('appeared-rc-build',['build','main.soma'])
    expect('unchanged since its last build' not in p.stdout,'new rc was skipped')
    stamp=root/'.soma-cache/part.stamp'
    expect(stamp.exists() and stamp.read_text().splitlines()[0]=='soma-stamp incomplete',
           'rc build reused/certified import stamp')
    trace=work/'trace'
    run('rc-trace',['check','main.soma'],extra={'SOMA_TEST_SOURCE':str(source),'SOMA_TEST_DEPENDENCIES':str(trace)})
    expect(trace.exists() and trace.read_text().splitlines()[0]=='incomplete','rc trace was certified')
    rc.write_text('ThisRcMustBeExecuted.\n')
    fresh('edited-rc-stale',False)
    p=run('edited-rc-is-executed',['build','main.soma'],False)
    expect('ThisRcMustBeExecuted' in p.stderr,'edited invalid rc was not executed')
    rc.write_text('Set Printing All.\n');run('valid-rc-again',['build','main.soma'])
    rc.unlink();fresh('removed-rc-needs-check',False)
    run('removed-rc-build',['build','main.soma']);fresh('removed-rc-fresh',True)
    expect(stamp.exists() and stamp.read_text().splitlines()[0]!='soma-stamp incomplete',
           'normal import stayed uncertified after rc removal')
    # Cover the legacy home fallback through the same shared candidate policy.
    legacy=home/'.coqrc';legacy.write_text('Set Printing All.\n')
    fresh('home-rc-stale',False);run('home-rc-build',['build','main.soma'])
    legacy.unlink();run('home-rc-removed-build',['build','main.soma']);fresh('home-rc-removed-fresh',True)
    companion=root/'part.ext';companion.write_text('Set Printing All.\n')
    rc.symlink_to(companion)
    run('rc-companion-alias-build',['build','main.soma'])
    expect(stamp.read_text().splitlines()[0]=='soma-stamp incomplete',
           'rc alias to known companion was certified')
    rc.unlink();companion.unlink()
    run('rc-alias-removed-build',['build','main.soma']);fresh('rc-alias-removed-fresh',True)
report=os.environ.get('SOMA_RC_AUDIT_REPORT')
if report:pathlib.Path(report).write_text(json.dumps(dict(records=records,failures=failures),indent=2)+'\n')
if observe:
    print('observed rc audit mismatches:',json.dumps(failures))
else:
    print('default rc appearance/edit/removal, execution, import stamps and traces: passed')
PY
