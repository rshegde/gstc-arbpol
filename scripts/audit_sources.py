#!/usr/bin/env python3
"""Fail closed on private imports, proof placeholders, or manifest drift."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
assert not (root / 'LeanEM').exists(), 'Old source namespace directory remains'
assert not (root / 'LeanEM.lean').exists(), 'Old library entry point remains'
manifest = json.loads((root / 'docs/source-manifest.json').read_text())
entries = {entry['module']: entry for entry in manifest['modules']}
files = {'.'.join(p.relative_to(root).with_suffix('').parts): p
         for p in (root / 'GSTC').rglob('*.lean')}
assert set(files) == set(entries), 'Source/manifest module mismatch'

def code_only(text):
    # Lean block comments nest. Preserve code tokens while skipping comments
    # and quoted strings; do not mistake doc prose for proof placeholders.
    out = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
        elif text.startswith('/-', i): depth = 1; i += 2; out.append(' ')
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1; out.append(' ')
        else: out.append(text[i]); i += 1
    assert depth == 0, 'Unclosed comment'
    return ''.join(out)

graph = {}
for module, path in files.items():
    assert not any(word in module for word in
                   ('Interface', 'Mathematics', 'Multipolar', 'Maxwell', 'Idemen', 'Legacy')), module
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entries[module]['public_sha256'], module
    text = code_only(path.read_text())
    assert 'LeanEM' not in text, f'Old namespace reference: {module}'
    assert not re.search(r'\b(sorry|admit|axiom)\b', text), f'Proof placeholder/axiom: {module}'
    imports = re.findall(r'^(?:public\s+|private\s+)?import\s+([\w.]+)', text, re.M)
    for imported in imports:
        assert imported.startswith('Mathlib.') or imported in files, (module, imported)
    graph[module] = [m for m in imports if m in files]

seen = set()
todo = list(manifest['roots'])
while todo:
    module = todo.pop()
    if module not in seen:
        seen.add(module); todo.extend(graph[module])
assert seen == set(files), 'Unreachable extra source in companion'
root_imports = re.findall(r'^public import ([\w.]+)', (root/'GSTC.lean').read_text(), re.M)
assert root_imports == manifest['roots'], 'Root import/manifest mismatch'
assert (root/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0'
print(f'PASS: {len(files)} dependency-reachable modules; manifest hashes match; no private imports, legacy modules, axioms, or proof placeholders.')
