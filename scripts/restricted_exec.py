#!/usr/bin/env python3
"""Fail closed unless actual kernel limits protect this verification process."""
import os
from pathlib import Path
import sys


def check_limits():
    cpus = sorted(os.sched_getaffinity(0))
    if not 1 <= len(cpus) <= 2:
        raise RuntimeError(f'CPU affinity allows {len(cpus)} CPUs; at most two are permitted')
    entry = next((line[3:] for line in Path('/proc/self/cgroup').read_text().splitlines()
                  if line.startswith('0::')), None)
    if entry is None:
        raise RuntimeError('unified cgroup membership unavailable')
    group = Path('/sys/fs/cgroup') / entry.lstrip('/')
    shared = next((p for p in (group, *group.parents) if p.name == 'leanem-build.slice'), None)
    if shared is None:
        raise RuntimeError('process is outside the shared LeanEM verification slice')
    expected = {'memory.high': 8 * 1024**3, 'memory.max': 12 * 1024**3,
                'memory.swap.max': 0, 'pids.max': 128}
    for name, maximum in expected.items():
        raw = (shared / name).read_text().strip()
        if raw == 'max' or int(raw) > maximum:
            raise RuntimeError(f'{name} is {raw}; permitted maximum is {maximum}')
    return cpus, shared


def main():
    try:
        cpus, shared = check_limits()
    except (OSError, ValueError, RuntimeError) as error:
        print(f'Refusing unrestricted execution: {error}', file=sys.stderr)
        return 1
    if sys.argv[1:] == ['--check-only']:
        print(f'Kernel limits verified: affinity={cpus}; shared group={shared.name}')
        for name in ('memory.high', 'memory.max', 'memory.swap.max', 'pids.max',
                     'memory.events', 'pids.events'):
            path = shared / name
            if path.exists():
                print(f'{name}: {path.read_text().strip()}')
        return 0
    if len(sys.argv) < 2:
        print('Expected a command', file=sys.stderr)
        return 2
    os.execvp(sys.argv[1], sys.argv[1:])


if __name__ == '__main__':
    sys.exit(main())
