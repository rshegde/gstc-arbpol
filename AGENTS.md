# LeanEM resource containment

All agents must run every Lean/Lake build, elaboration, gate, numerical
verification, and potentially expensive diagnostic using:

    scripts/run_restricted.sh COMMAND [ARGUMENT ...]

This wrapper fails closed unless the persistent shared systemd slice has
its verified aggregate CPU, memory, swap and task limits. Never bypass it
with direct `lake`, `lean`, `timeout lake`, a background job, or another
shell. If systemd access is denied in a sandbox, request execution of the
wrapper outside that sandbox; do not fall back to unrestricted execution.
Run one verification job at a time. Read-only text/git inspection is exempt.

Emergency stop: `scripts/stop_verification.sh`.

The slice's `CPUQuota` does not bind on this host: the `cpu` cgroup
controller is not delegated to the user manager (`user@1001.service` has
`Delegate=yes` but `DelegateControllers=memory pids`), so no `cpu.max`
exists below `user.slice` and systemd's quota is silently unenforced. The
wrapper therefore caps CPU by affinity instead — `taskset -c 0-1`, two
logical CPUs, matching the slice's intended 200%. Measured with four busy
loops: 32 CPU-seconds in 8 wall-seconds before the cap, 16 after. The
memory, swap and task limits are real, because those controllers are
delegated. `LEANEM_CPU_LIST` may select at most two logical CPUs; the
wrapper verifies actual kernel limits and rejects broader affinity before
launching a command.

The slice definition is `scripts/systemd/leanem-build.slice`; its limits
must not be increased without the user's explicit permission. Commands
expire after 20 minutes. A killed job is a failed/incomplete check, never
a successful verification. Investigate one module at a time after a limit
is hit. Never disable heartbeats, recursion limits or other Lean limits to
force a stuck proof through without diagnosing its cost first.
