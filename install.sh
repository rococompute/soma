#!/bin/sh
# Installs Soma: builds it from source and puts `soma` on your PATH.
#
#   curl -fsSL https://raw.githubusercontent.com/yevbar/soma/gradual/install.sh | sh
#   ./install.sh                      (from a checkout: builds that checkout)
#
# Run it again to update: it fetches SOMA_REF and rebuilds what changed. The
# first run takes about 30 minutes (an OCaml compiler, then Soma and its
# standard library) and about 3 GB.
#
# SOMA_REPO    where to fetch Soma from (default: https://github.com/yevbar/soma.git)
# SOMA_REF     the branch, tag or commit to build (default: gradual)
# SOMA_DIR     where Soma's source is kept and built (default: ~/.soma; ignored
#              when run from a checkout, which is built in place and never fetched)
# SOMA_SWITCH  the opam switch to build in (default: soma, or the checkout's
#              local switch if it has one)
# SOMA_BIN     where the `soma` command goes (default: ~/.local/bin)
#
# It needs git, make, a C compiler and opam (2.1 or later). opam installs the
# system libraries the build needs (gmp, ...) through your package manager.
set -eu

SOMA_REPO=${SOMA_REPO:-https://github.com/yevbar/soma.git}
SOMA_REF=${SOMA_REF:-gradual}
SOMA_BIN=${SOMA_BIN:-$HOME/.local/bin}
say() { printf 'soma-install: %s\n' "$*"; }
die() { printf 'soma-install: %s\n' "$*" >&2; exit 1; }

# 1. The tools. opam, git, make and cc come from the system's package manager
# when it's apt or Homebrew; otherwise the script says what to install.
missing=""
for c in git make cc opam; do command -v "$c" >/dev/null 2>&1 || missing="$missing $c"; done
if [ -n "$missing" ]; then
  if command -v brew >/dev/null 2>&1 && [ "$(uname -s)" = Darwin ]; then
    command -v cc >/dev/null 2>&1 || die "no C compiler: run xcode-select --install, then run this again"
    say "installing with Homebrew:$missing"
    brew install $(echo "$missing" | sed 's/ cc//; s/ make//')
  elif command -v apt-get >/dev/null 2>&1; then
    say "installing with apt-get (sudo):$missing"
    sudo apt-get update -q && sudo apt-get install -y -q git build-essential opam
  else
    die "missing:$missing. Install them with your package manager (opam: https://opam.ocaml.org/doc/Install.html), then run this again"
  fi
fi
opam_version=$(opam --version)
case $opam_version in
  1.*|2.0.*) die "opam $opam_version is too old: Soma needs 2.1 or later, which installs system libraries itself" ;;
esac

# 2. opam's root. Linux sandboxing needs bubblewrap; without it opam can't
# build anything sandboxed, so it's turned off there.
if ! opam switch list >/dev/null 2>&1; then
  say "initializing opam"
  if [ "$(uname -s)" = Linux ] && ! command -v bwrap >/dev/null 2>&1; then
    opam init --bare -y -q --disable-sandboxing
  else
    opam init --bare -y -q
  fi
fi

# 3. The source: this checkout if the script is in one, otherwise SOMA_DIR,
# fetched at SOMA_REF (shallow: Rocq's history is long).
# Piped into sh, $0 is the shell, not this file, so there's no checkout.
here=""
case $0 in *install.sh) here=$(cd "$(dirname "$0")" && pwd) ;; esac
if [ -n "$here" ] && [ -f "$here/soma-runtime.opam" ] && [ -f "$here/dune-project" ]; then
  SOMA_DIR=$here
  say "building the checkout at $SOMA_DIR"
else
  SOMA_DIR=${SOMA_DIR:-$HOME/.soma}
  mkdir -p "$SOMA_DIR"
  [ -d "$SOMA_DIR/.git" ] || git -C "$SOMA_DIR" init -q
  git -C "$SOMA_DIR" remote remove origin 2>/dev/null || true
  git -C "$SOMA_DIR" remote add origin "$SOMA_REPO"
  say "fetching $SOMA_REF from $SOMA_REPO into $SOMA_DIR"
  git -C "$SOMA_DIR" fetch -q --depth 1 origin "$SOMA_REF" \
    || die "fetching $SOMA_REF from $SOMA_REPO failed. While yevbar/soma is private, use SSH: SOMA_REPO=git@github.com:yevbar/soma.git"
  git -C "$SOMA_DIR" checkout -q --force --detach FETCH_HEAD
fi
cd "$SOMA_DIR"
say "Soma $(git log -1 --format='%h %s' 2>/dev/null || echo '(not a git checkout)')"

# 4. The build switch: a named one, not a local one, because the wasm
# package's build fails inside Soma's tree (GRADUAL.md, Quick start). A
# checkout that already has a local switch keeps it.
if [ -z "${SOMA_SWITCH:-}" ]; then
  if [ -d "$SOMA_DIR/_opam" ]; then SOMA_SWITCH=$SOMA_DIR; else SOMA_SWITCH=soma; fi
fi
if ! opam switch list --short 2>/dev/null | grep -qxF "$SOMA_SWITCH"; then
  say "making the opam switch $SOMA_SWITCH, OCaml 4.14.2 (several minutes)"
  opam switch create "$SOMA_SWITCH" ocaml-base-compiler.4.14.2 --no-install -y -q
fi
say "installing Soma's dependencies into $SOMA_SWITCH"
opam install --switch="$SOMA_SWITCH" -y -q --deps-only ./soma-runtime.opam
eval "$(opam env --switch="$SOMA_SWITCH" --set-switch)"

# 5. The build. make dunestrap writes the theories' dune files, which are
# generated; without them there's no standard library.
log=$SOMA_DIR/install.log
: > "$log"
say "building Soma (the first build takes a while; log: $log)"
make dunestrap >> "$log" 2>&1 || { tail -30 "$log"; die "make dunestrap failed: see $log"; }
dune build soma-runtime.install soma-core.install >> "$log" 2>&1 || { tail -40 "$log"; die "the build failed: see $log"; }
bin=$SOMA_DIR/_build/install/default/bin
[ -f "$SOMA_DIR/_build/install/default/lib/coq/theories/Init/Prelude.vo" ] \
  || die "Soma built without its standard library (no Prelude.vo): see $log"

# 6. The command: a two-line wrapper rather than a symlink, because Soma
# finds its library from the path it's run by.
mkdir -p "$SOMA_BIN"
printf '#!/bin/sh\nexec "%s/soma" "$@"\n' "$bin" > "$SOMA_BIN/soma"
chmod +x "$SOMA_BIN/soma"
"$SOMA_BIN/soma" help > /dev/null 2>&1 || die "$SOMA_BIN/soma doesn't run: see $log"
say "done: $SOMA_BIN/soma (Soma's tools, rocq included, are in $bin)"
case :$PATH: in
  *":$SOMA_BIN:"*) say "try: soma help" ;;
  *) say "$SOMA_BIN isn't on your PATH. Add it: export PATH=\"$SOMA_BIN:\$PATH\"" ;;
esac
