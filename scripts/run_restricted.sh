#!/usr/bin/env bash
# Fail closed: every verification command and its descendants must be in
# the shared CPU/memory-limited slice. Never fall back to an unrestricted run.
set -euo pipefail
if [ "$#" -eq 0 ]; then
  echo "Usage: scripts/run_restricted.sh COMMAND [ARGUMENT ...]" >&2
  exit 2
fi
if ! systemctl --user is-active --quiet leanem-build.slice; then
  systemctl --user start leanem-build.slice
fi
# Verify effective aggregate limits, not merely the presence of a unit file.
for setting in CPUQuotaPerSecUSec=2s MemoryHigh=8589934592 MemoryMax=12884901888 MemorySwapMax=0 TasksMax=128; do
  key="${setting%%=*}"
  expected="${setting#*=}"
  actual="$(systemctl --user show leanem-build.slice --property="$key" --value)"
  if [ "$actual" != "$expected" ]; then
    echo "Refusing unrestricted execution: $key is '$actual', expected '$expected'." >&2
    exit 1
  fi
done
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
mkdir -p "$repo_root/.lake"
# CPU cap by affinity, because the slice's CPUQuota is inert on this host.
#
# The `cpu` cgroup controller is not delegated to the user manager here:
# user@1001.service carries Delegate=yes but DelegateControllers=memory pids,
# so no cpu.max file exists anywhere below user.slice and systemd's CPUQuota
# has nothing to enforce.  Measured on this machine: four busy loops inside
# the slice consumed 32 CPU-seconds in 8 wall-seconds, i.e. four cores, with
# the "200%" quota in force.  The memory, swap and task limits ARE enforced
# (those controllers are delegated), so only the CPU cap needs a workaround.
#
# `taskset` caps the whole process tree by CPU affinity, which needs no
# cgroup controller and no root.  Two logical CPUs match the slice's
# intended 200%.  Override with LEANEM_CPU_LIST.
if ! command -v taskset >/dev/null 2>&1; then
  echo "Refusing unrestricted execution: taskset is missing, so the CPU cap cannot be applied." >&2
  exit 1
fi
CPU_LIST="${LEANEM_CPU_LIST:-0-1}"
# One shared lock prevents agents from queuing overlapping verification jobs.
exec flock --nonblock --conflict-exit-code 75 --close \
  "$repo_root/.lake/verification.lock" systemd-run --user --quiet --wait --collect --pipe \
  --unit="leanem-job-$(date +%s)-$$" --slice=leanem-build.slice \
  --service-type=exec --working-directory="$PWD" --setenv="PATH=$PATH" \
  --property=Nice=15 --property=OOMPolicy=kill \
  --property=RuntimeMaxSec=1200 \
  --property=TimeoutStopSec=10 --property=KillMode=control-group \
  -- taskset -c "$CPU_LIST" python3 "$repo_root/scripts/restricted_exec.py" "$@"
