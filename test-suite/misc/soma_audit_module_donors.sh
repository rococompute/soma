#!/usr/bin/env bash
# Real compiler compile counts are the performance acceptance, not a mock.
set -euo pipefail
export PATH="$BIN:$PATH"
export SOMA_OCAML_BUILD=0 SOMA_MIRAGE_BUILD=0
python3 -B "$(dirname "$0")/soma_module_donors.py" --soma "$(command -v soma)"
