#!/usr/bin/env bash

# A project's soma.toml (vernac/somaProject.ml, vernac/somaToml.ml): its
# folder is the project's root, from which any of its files imports, and
# its [project] (name, version, description) is checked.

set -euo pipefail

export PATH=$BIN:$PATH

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cd "$TMP"

manifest() { printf '[project]\nname = "shop"\nversion = "0.1.0"\n%s\n' "${1-}" > soma.toml; }

mkdir models
manifest 'description = """
A test project, \
with "quotes" and é"""  # a comment'
echo 'double (n : nat) : nat := n + n.' > util.soma
printf 'Import util.\nquad (n : nat) : nat := double (double n).\nquad 3.\n' > models/calc.soma
printf 'Import models.calc.\nquad 5.\n' > main.soma

soma run main.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q "= 20" out.log
# a file in a folder imports from the root, as the folder of soma.toml
soma run models/calc.soma > out.log 2>&1 || { cat out.log; exit 1; }
grep -q "= 12" out.log
[ -f .soma-cache/util.vo ]

# soma build checks soma.toml: [error] [what soma.toml says]
refused() {
  if soma run main.soma > out.log 2>&1; then echo "soma.toml was taken: $2"; cat soma.toml; exit 1; fi
  grep -q -- "$1" out.log || { echo "expected: $1"; cat out.log; exit 1; }
}
printf '[project]\nname = "My-shop"\nversion = "0.1.0"\n' > soma.toml
refused 'soma.toml:2: "My-shop" is no project name' 'a name with - and capitals'
grep -q 'name = "my_shop"' out.log
printf '[project]\nname = "shop"\nversion = "1.0"\n' > soma.toml
refused 'soma.toml:3: "1.0" is no semantic version' 'two numbers'
printf '[project]\nname = "shop"\nversion = "01.0.0"\n' > soma.toml
refused 'its numbers do not begin with 0' 'a leading zero'
printf '[project]\nname = "shop"\n' > soma.toml
refused '\[project\] has no version' 'no version'
printf 'name = "shop"\n' > soma.toml
refused 'name is a key of \[project\]' 'a key above [project]'
manifest 'nmae = "x"'
refused 'soma.toml:4: nmae is not a key of \[project\]' 'an unknown key'
manifest '[docs]'
refused 'soma.toml:4: docs is not something soma.toml says' 'an unknown table'

# [opam]: versions of opam packages, checked without opam
manifest '[opam]
cryptokit = "1.20"
ocaml-base-compiler = "4.14.2"
"zarith+x" = "v1.14~rc1"'
soma run main.soma > out.log 2>&1 || { cat out.log; exit 1; }
manifest '[opam]
cryptokit = 1'
refused 'soma.toml:5: cryptokit is an integer; a package.s version is a string' 'a version out of quotes'
manifest '[opam]
cryptokit = "1 20"'
refused 'soma.toml:5: "1 20" is no opam version' 'a space in a version'
manifest '[opam]
"crypto kit" = "1.20"'
refused 'soma.toml:5: "crypto kit" is no opam package.s name' 'a space in a name'
manifest 'opam = "cryptokit"'
refused 'soma.toml:4: opam is not a key of \[project\]' 'opam under [project]'
manifest 'version = "0.2.0"'
refused 'soma.toml:4: version is already defined, on line 3' 'a key defined twice'
manifest 'description = "unterminated'
refused 'soma.toml:4: unterminated string' 'a TOML error'
manifest 'description = 1979-05-27'
refused 'dates and times are not supported' 'a date'

# [dependencies] is read without the network: each key a path, each value a
# version or a checkout
deps() { printf '[project]\nname = "shop"\nversion = "0.1.0"\n[dependencies]\n%s\n' "$1" > soma.toml; }
deps 'owner/repo = "1.2.3"'
refused "soma.toml:5: expected = after the key owner, found '/'" 'a path out of quotes'
deps 'owner.repo = "1.2.3"'
refused 'soma.toml:5: owner is no path. A dependency path is in quotes' 'a dotted key'
deps 'owner = "1.2.3"'
refused 'soma.toml:5: owner is no path' 'one segment'
deps '"https://github.com/owner/repo" = "1.2.3"'
refused 'is a URL. A dependency is a path: "owner/repo" = "1.2.3"' 'a URL'
deps '"owner/repo/" = "1.2.3"'
refused 'is no path. A path is segments separated by /' 'an empty segment'
deps '"../repo" = "1.2.3"'
refused 'is no path. A path is segments separated by /' 'a folder'
deps '"owner/bad seg" = "1.2.3"'
refused '"bad seg" is no path segment' 'a space'
deps '"owner/repo/sub" = "1.2.3"'
refused 'a subdirectory of a repository is not supported yet' 'a subdirectory'
deps '"owner/repo" = "1.0"'
refused 'soma.toml:5: "1.0" is no semantic version' 'two numbers'
deps '"owner/repo" = "1.2.3+build.5"'
refused 'has build metadata. A dependency version is a tag: "owner/repo" = "1.2.3"' 'build metadata'
deps '"owner/repo" = "2.0.0"'
refused 'Major 2 and above is "owner/repo/v2" = "2.0.0"' 'major 2 at no suffix'
deps '"owner/repo/v2" = "1.4.0"'
refused '"owner/repo/v2" is major 2, and "1.4.0" is major 1' 'a major that disagrees'
deps '"owner/repo/v1" = "1.4.0"'
refused 'Major 0 and 1 have no suffix: "owner/repo"' 'a suffix v1'
deps '"owner/repo" = 1'
refused '"owner/repo" is an integer. A dependency is a version' 'an integer'
deps '"owner/wip" = { path = "../wip", version = "1.0.0" }'
refused 'has path and version' 'a checkout with a version'
deps '"owner/wip" = { version = "1.0.0" }'
refused '"owner/wip" has no path' 'a table with no path'
deps '"owner/wip" = { path = "../no-such-folder" }'
refused '"../no-such-folder" has no soma.toml' 'a folder that is no project'
deps '"owner/wip" = { path = "..", name = "other" }'
refused 'name is not a key of a checkout' 'an unknown key in a checkout'
printf '[project]\nname = "shop"\nversion = "0.1.0"\n[dependencies]\n"owner/repo" = "1.0.0"\n"github.com/owner/repo" = "1.0.0"\n' > soma.toml
refused 'one path, written twice' 'one path two ways'
# none, or an empty table, is no dependency
manifest '[dependencies]'
soma run main.soma > out.log 2>&1 || { cat out.log; exit 1; }

# a pre-release and build metadata are a version
printf '[project]\nname = "shop"\nversion = "1.0.0-rc.1+build.5"\n' > soma.toml
soma run main.soma > out.log 2>&1 || { cat out.log; exit 1; }

# without soma.toml, the root is the program's folder, as before
rm soma.toml
soma run main.soma > out.log 2>&1 || { cat out.log; exit 1; }
if soma run models/calc.soma > out.log 2>&1; then echo "models/calc.soma imported util without a root"; exit 1; fi
