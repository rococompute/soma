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
manifest '[ocaml]'
refused 'soma.toml:4: ocaml is not something soma.toml says' 'an unknown table'
manifest 'version = "0.2.0"'
refused 'soma.toml:4: version is already defined, on line 3' 'a key defined twice'
manifest 'description = "unterminated'
refused 'soma.toml:4: unterminated string' 'a TOML error'
manifest 'description = 1979-05-27'
refused 'dates and times are not supported' 'a date'

# a pre-release and build metadata are a version
printf '[project]\nname = "shop"\nversion = "1.0.0-rc.1+build.5"\n' > soma.toml
soma run main.soma > out.log 2>&1 || { cat out.log; exit 1; }

# without soma.toml, the root is the program's folder, as before
rm soma.toml
soma run main.soma > out.log 2>&1 || { cat out.log; exit 1; }
if soma run models/calc.soma > out.log 2>&1; then echo "models/calc.soma imported util without a root"; exit 1; fi
