# Companion verification

Verified on 2026-11-22 with Lean 4.35.0 and the pinned Mathlib dependency set.

| Check | Result |
|---|---|
| Full `lake build` | Passed, 3,146 build jobs including cached external dependencies |
| Public namespace/library | `GSTC`; no `LeanEM` source directory, entry point, or imports |
| Library sources | 73 dependency-reachable modules, plus `GSTC.lean` |
| Source reduction | 33,517 → 13,563 lines; unused declarations, obsolete comments, duplicate helpers, and redundant imports removed |
| Transitive axiom audit | Passed for 1,538 retained theorems, compared with 2,479 in the initial extraction |
| Paper result coverage | All 53 documented theorem roots present |
| Statement comparison | All 53 preserve their original assumptions and conclusions after namespace renaming |
| Allowed proof axioms | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Source/manifest hashes | All matched |
| Proof placeholders/additional axioms | None |
| Excluded source | No interface, distributional mathematics, Maxwell, Idemen, multipolar, ambient geometry/basis, Fresnel, or legacy-minimum modules |

The minimized source set is the closure of the 53 documented paper results under the existing compiled proof/type dependencies and required source-elaboration support. Whole structure/instance commands remain indivisible; this does not assert shortest possible alternative proofs. Electric and magnetic support developments are reduced to the identities used in those proofs.

Statement comparison used Lean expressions from the reference source snapshot and the renamed build, with namespaces normalized and binder names/nonsemantic metadata erased. Definitional equality was checked where expressions were not syntactically identical. The [scope audit](paper-scope-audit.json) records all 53 results and canonical signature hashes. This comparison is an extraction check, not an additional assumption of the library.

All builds, dependency inspections, and audits ran one job at a time through the shared resource-restricted wrapper. Only the external Mathlib/package cache was reused; the renamed source library compiled in its own build directory. The public library and routine verification require no original LeanEM checkout or artifacts.

The build emits only informational tactic suggestions, with no compilation errors or linter warnings. Source and theorem audits passed. No manuscript or original LeanEM working-tree files were modified.

Run `scripts/verify.sh` to repeat the library build, theorem-coverage/axiom audit, and source-boundary checks.
