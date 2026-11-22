#!/usr/bin/env bash
# Stop every job in the verification slice without killing terminals/agents.
set -euo pipefail
exec systemctl --user stop leanem-build.slice
