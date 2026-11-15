#!/bin/sh
# Requires access to git@github.com:yevbar/soma-owl.git and Owl's native dependencies.
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
output=$(soma run main.soma)
printf '%s\n' "$output"
printf '%s\n' "$output" | grep -q '^PASS training improves loss and learns the two tactical examples$'
if printf '%s\n' "$output" | grep -q '^FAIL'; then exit 1; fi
