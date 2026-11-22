#!/usr/bin/env bash
# The link cleanup cases now use the generated Wire adapter and real Lwt;
# soma_tcp_errors.sh also checks error/EOF distinctions and write failures.
set -euo pipefail
exec bash "$(dirname "$0")/soma_tcp_errors.sh"
