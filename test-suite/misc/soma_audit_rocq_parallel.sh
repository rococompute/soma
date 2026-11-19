#!/usr/bin/env bash

# F3: one [Import left right.] compiles the two imports as two processes.
# When both name the same local Rocq Library, both evaluate its [Rocq
# Library] and compile it into the same directory of the project's cache:
# one must compile it, the other must wait and use what it published, and
# one that is killed while compiling must leave it to be compiled again.
# (plugins/soma_rocq takes a lock beside that directory, which it removes.)

set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_MIRAGE_BUILD=0 SOMA_OCAML_BUILD=0
export SOMA_CACHE="$(mktemp -d)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP" "$SOMA_CACHE"' EXIT
export SOMA_TEST_FIXTURE="$TMP"

python3 - <<'PY'
import os
import pathlib
import shutil
import signal
import subprocess
import time

outer = pathlib.Path(os.environ["SOMA_TEST_FIXTURE"]).resolve()
N = 30  # files: long enough that a compilation is still running when killed


def new_project(root, libraries, use_library=True, dirs=None):
    """[Import left right.] where left and right each name one library.

    [use_library] has each side import a file of its library, so loading the
    side needs the library's load path; without it the sides only make the
    libraries be compiled. [dirs] names the source directories, when the two
    sides name one package from two sources."""
    root.mkdir(parents=True)
    (root / "soma.toml").write_text('[project]\nname = "parallel_rocq"\nversion = "0.1.0"\n')
    sides = ["left", "right"]
    dirs = dirs or libraries
    for index, (side, name, directory) in enumerate(zip(sides, libraries, dirs)):
        lib = root / "vendor" / directory
        lib.mkdir(parents=True, exist_ok=True)
        (lib / "_RocqProject").write_text("-Q . %s\n" % name)
        for i in range(1, N + 1):
            (lib / ("f%d.v" % i)).write_text(
                "Definition f%d := %d.\nLemma f%d_is : f%d = %d. Proof. reflexivity. Qed.\n"
                % (i, i, i, i, i))
        (root / (side + ".soma")).write_text(
            'Rocq Library "%s" in "vendor/%s".\n'
            '%s' % (name, directory,
                    ('From %s Require Import f%d.\n%s_v := f%d.\n' % (name, N, side, N))
                    if use_library else
                    ('%s_v := %d.\n' % (side, index + 1))))
    # one sentence: the two imports are compiled at once
    (root / "main.soma").write_text(
        "Import left right.\nmain_v := left_v + right_v.\nmain_v.\n")


def env_with(store):
    env = dict(os.environ)
    env["SOMA_CACHE"] = str(store)
    return env


def build(root, store):
    return subprocess.run(["soma", "build", "-v", "main.soma"], cwd=root,
                          env=env_with(store), text=True, capture_output=True,
                          timeout=300)


def compiled(stderr):
    return stderr.count("Rocq: compiling ")


def starts(stderr):
    return stderr.count(": 1/%d " % N)


def markers(root):
    return sorted((root / ".soma-cache" / "rocq").glob("*/theories"))


def check(result, root, expected_value, expect_compiled, label):
    assert result.returncode == 0, (label, result.stdout, result.stderr)
    assert ("= %d" % expected_value) in result.stdout, (label, result.stdout)
    assert "rocq dep failed" not in result.stderr, (label, result.stderr)
    assert compiled(result.stderr) == expect_compiled, (label, result.stderr)
    assert len(markers(root)) == 1, (label, markers(root))
    # the lock is beside the directory, and the directory outlives it
    locks = list((root / ".soma-cache" / "rocq").glob("*.lock"))
    assert len(locks) == 1, (label, locks)


# 1. The regression: the same library imported by both sides, from scratch,
#    three times. One compilation, and the other import waits for it.
root = outer / "parallel"
new_project(root, ["mylib", "mylib"])
for i in range(3):
    shutil.rmtree(root / ".soma-cache", ignore_errors=True)
    result = build(root, outer / ("store-%d" % i))
    assert result.returncode == 0, ("run %d" % i, result.stdout, result.stderr)
    assert starts(result.stderr) == 1, ("run %d: two compilations" % i, result.stderr)
    check(result, root, 2 * N, N, "run %d" % i)
    # once: a second build compiles neither the library nor the imports
    result = build(root, outer / ("store-%d" % i))
    check(result, root, 2 * N, 0, "second build %d" % i)
print("parallel import of one Rocq Library: ok")

# 2. Failure and retry: a compilation killed halfway leaves no [theories],
#    and the lock it held does not outlive it. A build that waited for it
#    takes the library over and compiles it again.
root = outer / "retry"
new_project(root, ["mylib", "mylib"])
store = outer / "store-retry"
first_err = outer / "first.err"
first_out = outer / "first.out"
with open(first_err, "w") as err, open(first_out, "w") as out:
    first = subprocess.Popen(["soma", "build", "-v", "main.soma"], cwd=root,
                             env=env_with(store), stdout=out, stderr=err,
                             start_new_session=True)
    deadline = time.time() + 60
    while "Rocq: compiling " not in first_err.read_text(errors="replace"):
        assert time.time() < deadline, "the library did not start compiling"
        assert first.poll() is None, first_err.read_text(errors="replace")
        time.sleep(0.01)
    # a second build, which waits for the lock the first holds
    second_err = outer / "second.err"
    second_out = outer / "second.out"
    with open(second_err, "w") as serr, open(second_out, "w") as sout:
        second = subprocess.Popen(["soma", "build", "-v", "main.soma"], cwd=root,
                                  env=env_with(store), stdout=sout, stderr=serr)
        # it is in the cache: its imports compile, and its library must wait
        deadline = time.time() + 60
        while "Compiling " not in second_err.read_text(errors="replace"):
            assert time.time() < deadline, "the second build did not start"
            assert second.poll() is None, second_err.read_text(errors="replace")
            time.sleep(0.01)
        time.sleep(0.3)
        assert "Rocq: compiling " not in second_err.read_text(errors="replace"), \
            "the second build did not wait for the first one's lock"
        # kill the compilation the second one waits for
        os.killpg(first.pid, signal.SIGKILL)
        first.wait(timeout=60)
        assert first.returncode != 0, first.returncode
        # killed before it wrote [theories]: no later build may take it for done
        assert markers(root) == [], markers(root)
        assert second.wait(timeout=300) == 0, second_err.read_text(errors="replace")
    out = second_out.read_text(errors="replace")
    err = second_err.read_text(errors="replace")
    assert ("= %d" % (2 * N)) in out, out
    assert compiled(err) == N, err
    assert markers(root) != [], "the waiter did not compile the library"
print("killed compilation retried by a waiting build: ok")

# 3. Independent keys still have independent locks: two different libraries
#    in one [Import] are both compiled, and neither is taken for the other.
#    The sides do not import from their library: what their .vo names is
#    not it, so this does not depend on the load path they record.
root = outer / "independent"
new_project(root, ["alpha", "beta"], use_library=False)
result = build(root, outer / "store-independent")
assert result.returncode == 0, (result.stdout, result.stderr)
assert "= 3" in result.stdout, result.stdout  # left_v + right_v = 1 + 2
assert starts(result.stderr) == 2, result.stderr
assert compiled(result.stderr) == 2 * N, result.stderr
found = markers(root)
assert len(found) == 2, found
assert len(list((root / ".soma-cache" / "rocq").glob("*.lock"))) == 2
print("independent libraries: ok")

# 4. Independent keys of one package: the two sides name the same package
#    from two sources, so they compile two directories whose names share the
#    package's prefix. Each removes a directory of the package compiled
#    before, but neither may remove the other's while it is being built.
root = outer / "two_keys"
new_project(root, ["mylib", "mylib"], use_library=False, dirs=["a", "b"])
result = build(root, outer / "store-two-keys")
assert result.returncode == 0, (result.stdout, result.stderr)
assert "= 3" in result.stdout, result.stdout  # left_v + right_v = 1 + 2
assert starts(result.stderr) == 2, result.stderr
assert compiled(result.stderr) == 2 * N, result.stderr
assert markers(root) != [], markers(root)
print("independent keys of one package: ok")
PY

echo "soma audit: parallel Rocq Library: passed"
