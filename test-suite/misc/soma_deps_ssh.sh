#!/usr/bin/env bash
# SSH dependencies use the same selection and lock identities as HTTPS,
# but retain their transport for initial and locked fetches. No SSH server
# or credentials needed: Git rewrites just the test host to a bare repo.
set -euo pipefail
export PATH="$BIN:$PATH"
TMP=$(mktemp -d)
trap 'chmod -R u+w "$TMP"; rm -rf "$TMP"' EXIT
cd "$TMP"
TMP=$(pwd -P)
export XDG_CACHE_HOME="$TMP/cache"
export GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null
export GIT_CONFIG_COUNT=2
export GIT_CONFIG_KEY_0="url.file://$TMP/remote/.insteadOf" GIT_CONFIG_VALUE_0=git@packages.test:
export GIT_CONFIG_KEY_1="url.file://$TMP/remote/.insteadOf" GIT_CONFIG_VALUE_1=ssh://git@packages.test/
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
mkdir -p remote/owner work app
git init -q --bare remote/owner/maths.git
git -C work init -q
printf '[project]\nname = "ssh_maths"\nversion = "1.0.0"\n' > work/soma.toml
printf 'twice (n : nat) : nat := n + n.\n' > work/counts.soma
git -C work add .
git -C work commit -qm first
git -C work tag v1.0.0
git -C work push -q "$TMP/remote/owner/maths.git" HEAD refs/tags/v1.0.0
first=$(git -C work rev-parse HEAD)
printf '[project]\nname = "ssh_maths"\nversion = "2.0.0"\n' > work/soma.toml
git -C work add .
git -C work commit -qm second
git -C work tag v2.0.0
git -C work push -q "$TMP/remote/owner/maths.git" HEAD refs/tags/v2.0.0
cd app
manifest() { printf '[project]\nname = "app"\nversion = "0.1.0"\n%s\n' "${1-}" > soma.toml; }
check() {
  soma build -v main.soma > out.log 2>&1 || { cat out.log; exit 1; }
  grep -q '= 14' out.log || { cat out.log; exit 1; }
}
printf 'Import ssh_maths.counts.\ntwice 7.\n' > main.soma
manifest
soma get 'git@packages.test:owner/maths.git@1.0.0' > get.log 2>&1 || { cat get.log; exit 1; }
grep -q '"git@packages.test:owner/maths.git" = "1.0.0"' soma.toml
grep -q 'path = "packages.test/owner/maths"' soma.lock
grep -q "commit = \"$first\"" soma.lock
check
# A lock can refetch over SSH; no HTTPS mapping exists in this test.
chmod -R u+w "$XDG_CACHE_HOME/soma/src"
rm -rf "$XDG_CACHE_HOME/soma/src" .soma-cache
check
# Same canonical lock identity after changing only the transport spelling.
manifest '[dependencies]
"ssh://git@packages.test/owner/maths.git" = "1.0.0"'
check
grep -q "commit = \"$first\"" soma.lock
# The SSH user@host separator is not a version, even with no @VERSION.
manifest
soma get 'ssh://git@packages.test/owner/maths.git' > get.log 2>&1 || { cat get.log; exit 1; }
check
# Major suffixes select the tag, but are not part of the Git repository URL.
manifest
soma get 'git@packages.test:owner/maths.git/v2@2.0.0' > get.log 2>&1 || { cat get.log; exit 1; }
grep -q 'path = "packages.test/owner/maths/v2"' soma.lock
check
# SSH and HTTPS cannot smuggle two versions of the same repository into a build.
manifest '[dependencies]
"packages.test/owner/maths" = "1.0.0"
"git@packages.test:owner/maths.git" = "1.0.0"'
if soma build main.soma > out.log 2>&1; then echo 'accepted duplicate SSH/HTTPS identity'; exit 1; fi
grep -q 'one path, written twice' out.log
echo 'PASS SSH dependencies: SCP and URI URLs, soma get, canonical identity, locked refetch, major versions'
