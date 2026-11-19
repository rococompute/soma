#!/bin/sh
# Exercise the generated production Host module and its actual C primitives,
# without rebuilding the compiler. OCAMLC may select the prepared switch.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
python3 - "$here" <<'PY'
import errno, os, pathlib, subprocess, sys, tempfile, threading
source=pathlib.Path(sys.argv[1])/'toplevel/somaHost.ml'
text=source.read_text()
with tempfile.TemporaryDirectory(prefix='soma-host-io-') as tmp:
    root=pathlib.Path(tmp)
    (root/'soma_host.ml').write_text(text.split('let ml = {soma|',1)[1].split('|soma}',1)[0])
    c_source=text.split('let io_c = {soma|',1)[1].split('|soma}',1)[0]
    # Test-only syscall interposition observes the actual requested creation
    # mode before fchmod; inspecting only the final mode misses a leak window.
    hook=r'''#include <stdarg.h>
static int audit_openat(int dir, const char *name, int flags, ...)
{
    if (flags & O_CREAT) {
        va_list args; va_start(args, flags); mode_t mode = va_arg(args, int); va_end(args);
        const char *want = getenv("SOMA_AUDIT_CREATE_MODE");
        if (want && mode != (mode_t)strtol(want, NULL, 8)) { errno = EPERM; return -1; }
        return openat(dir, name, flags, mode);
    }
    return openat(dir, name, flags);
}
#define openat audit_openat
'''
    c_source=c_source.replace('static int host_parent(',hook+'\nstatic int host_parent(',1)
    (root/'soma_host_io.c').write_text(c_source)
    (root/'probe.ml').write_text('''
let () =
  let args = Sys.argv in
  let result = match args.(1) with
  | "tempdir" -> Soma_host.temp_dir args.(2)
  | "kill" -> Soma_host.kill_pid args.(2)
  | "file" -> Soma_host.file_replace args.(2) args.(3) "true"
  | "path" -> Soma_host.path_replace args.(2) args.(3) args.(4)
  | "remove" -> Soma_host.path_remove args.(2) args.(3)
  | "race" ->
      for _ = 1 to 2000 do ignore (Soma_host.path_replace args.(2) "sub/file" "inside") done;
      (true, (0., []))
  | _ -> failwith "mode" in
  let ok, (_, detail) = result in
  print_endline (String.concat "\\n" detail);
  exit (if ok then 0 else 1)
''')
    compiler=os.environ.get('OCAMLC','ocamlc')
    subprocess.run([compiler,'-I','+unix','-custom','-ccopt','-Wall','-ccopt','-Wextra','-ccopt','-Werror',
                    'unix.cma','soma_host_io.c','soma_host.ml','probe.ml','-o','probe'],cwd=root,check=True)
    def run(*args,ok=True,env=None):
        p=subprocess.run([str(root/'probe'),*map(str,args)],capture_output=True,text=True,env=env)
        assert (p.returncode==0)==ok,(args,p.returncode,p.stdout,p.stderr)
    failed_temp=subprocess.run([str(root/'probe'),'tempdir','audit'],capture_output=True,text=True,
                               env=dict(os.environ,TMPDIR=str(root/'missing-parent')))
    assert failed_temp.returncode==1,(failed_temp.stdout,failed_temp.stderr)
    assert 'Fatal error' not in failed_temp.stderr
    run('kill','0',ok=False)
    run('kill','not-a-pid',ok=False)
    child=subprocess.Popen(['sleep','30'])
    try:
        run('kill',child.pid)
        assert child.wait(timeout=5)<0
        run('kill',child.pid)  # already gone, no fake permission failure
    finally:
        if child.poll() is None:child.kill();child.wait()
    outside=root/'outside';outside.mkdir();victim=outside/'file';victim.write_text('outside')
    checkout=root/'checkout';checkout.mkdir()
    dest=checkout/'state';dest.write_text('old');dest.chmod(0o600)
    # Predictable old save temp cannot clobber a separate file.
    (checkout/'state.pantheon-tmp').symlink_to(victim)
    run('file',dest,'new',env=dict(os.environ,SOMA_AUDIT_CREATE_MODE='600'))
    assert dest.read_text()=='new' and victim.read_text()=='outside'
    assert dest.stat().st_mode&0o777==0o600
    run('file',checkout/'state.pantheon-tmp','bad',ok=False)
    assert victim.read_text()=='outside'
    run('path',checkout,'a/b/file','nested')
    assert (checkout/'a/b/file').read_text()=='nested'
    for rel in ['../outside/file','a/../../outside/file','/absolute','a//file','a/./file','a/../file','']:
        run('path',checkout,rel,'bad',ok=False)
    (checkout/'link').symlink_to(outside,target_is_directory=True)
    run('path',checkout,'link/file','bad',ok=False)
    run('remove',checkout,'link/file',ok=False)
    (checkout/'final').symlink_to(victim)
    run('path',checkout,'final','bad',ok=False)
    run('remove',checkout,'final',ok=False)
    assert victim.read_text()=='outside'
    run('remove',checkout,'a/b/file')
    assert not (checkout/'a/b/file').exists()
    # Replace an ancestor with a symlink concurrently with real writes.
    # Open directory descriptors may keep writing the original object, but
    # no operation may follow the substitute into outside/file.
    (checkout/'sub').mkdir();stop=threading.Event();errors=[]
    swaps=[0]
    def swap():
        extra=0
        try:
            while not stop.is_set():
                (checkout/'sub').rename(checkout/'saved')
                try:
                    (checkout/'sub').symlink_to(outside,target_is_directory=True)
                    swaps[0]+=1
                except FileExistsError:
                    # A concurrent legitimate mkdir won the gap; keep its
                    # directory inside the fixture, then restore ours.
                    pass
                while True:
                    try:
                        if (checkout/'sub').is_symlink():
                            (checkout/'sub').unlink()
                        elif (checkout/'sub').exists():
                            extra+=1
                            (checkout/'sub').rename(checkout/('extra-%d'%extra))
                        (checkout/'saved').rename(checkout/'sub')
                        break
                    except OSError as error:
                        if error.errno not in (errno.EEXIST, errno.ENOTEMPTY):raise
                        continue
        except BaseException as e:errors.append(repr(e))
    thread=threading.Thread(target=swap);thread.start()
    try:run('race',checkout)
    finally:stop.set();thread.join()
    assert not errors,errors
    assert swaps[0]>0, "swapper did not install a symlink"
    assert victim.read_text()=='outside'
    assert not list(checkout.rglob('.soma-write-*'))
print('PASS production Host atomic replacement, permissions, symlink refusal and concurrent descriptor-relative confinement')
PY
