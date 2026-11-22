#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
scripts/run_restricted.sh lake build
scripts/run_restricted.sh lake env lean Audit.lean
scripts/run_restricted.sh python3 scripts/audit_sources.py
