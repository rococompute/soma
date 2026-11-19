#!/usr/bin/env bash
# A dependency owns every source path, including the former .soma-source
# completion-marker name. Fetching must neither change it nor follow its links.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
export SOMA_TEST_SOURCE_NAMES="$TMP"
python3 - <<'PY'
from pathlib import Path
import os, subprocess
root=Path(os.environ['SOMA_TEST_SOURCE_NAMES']).resolve()
for kind in ['regular','symlink','directory']:
    base=root/kind; work=base/'work'; remote=base/'remote/github.com/owner/maps.git'; app=base/'app'
    work.mkdir(parents=True); remote.parent.mkdir(parents=True); app.mkdir()
    def git(*args):
        return subprocess.run(['git','-c','core.hooksPath=/dev/null','-c','user.name=test',
            '-c','user.email=test@invalid','-c','commit.gpgsign=false',*map(str,args)],
            check=True,capture_output=True,text=True).stdout.strip()
    git('init','--quiet',work); git('init','--quiet','--bare',remote)
    (work/'soma.toml').write_text('[project]\nname="maps"\nversion="1.0.0"\n')
    (work/'gmap.soma').write_text('v : nat := 7.\n')
    victim=base/'outside-source'; victim.write_text('must stay unchanged\n')
    marker=work/'.soma-source'
    if kind=='regular': marker.write_text('dependency-owned bytes\n')
    elif kind=='symlink': marker.symlink_to(victim)
    else:
        marker.mkdir(); (marker/'data').write_text('dependency-owned directory\n')
    git('-C',work,'add','.'); git('-C',work,'commit','--quiet','-m','fixture')
    git('-C',work,'tag','v1.0.0'); commit=git('-C',work,'rev-parse','HEAD')
    git('-C',work,'push','--quiet',remote,'HEAD','refs/tags/v1.0.0')
    (app/'soma.toml').write_text('[project]\nname="app"\nversion="0.1.0"\n[dependencies]\n"owner/maps"="1.0.0"\n')
    (app/'main.soma').write_text('Import maps.gmap.\nv.\n')
    env=dict(os.environ,XDG_CACHE_HOME=str(base/'cache'),SOMA_CACHE=str(base/'store'),
        SOMA_OCAML_BUILD='0',SOMA_MIRAGE_BUILD='0',GIT_CONFIG_NOSYSTEM='1',GIT_CONFIG_GLOBAL='/dev/null',
        GIT_CONFIG_COUNT='1',GIT_CONFIG_KEY_0='url.file://'+str(base/'remote')+'/.insteadOf',GIT_CONFIG_VALUE_0='https://')
    for attempt in range(2):
        result=subprocess.run(['soma','build','main.soma'],cwd=app,env=env,capture_output=True,text=True,timeout=90)
        assert result.returncode==0,(kind,result.stdout,result.stderr)
        entries=list((base/'cache/soma/src').rglob('maps@1.0.0-'+commit))
        assert len(entries)==1,(kind,entries)
        source=entries[0]
        assert not (source/'.git').exists()
        for line in git('-C',work,'ls-tree','-r',commit).splitlines():
            metadata,path=line.split('\t',1); mode=metadata.split()[0]
            actual=source/path; original=work/path
            if mode=='120000':
                assert actual.is_symlink() and os.readlink(actual)==os.readlink(original),(kind,path)
            else: assert actual.read_bytes()==original.read_bytes(),(kind,path)
        assert victim.read_text()=='must stay unchanged\n',kind
    print('source name preserved:',kind)
PY
