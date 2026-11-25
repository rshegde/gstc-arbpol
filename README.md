# gstc-arbpol

Lean 4 proofs accompanying the [arbitrary-polarization GSTC paper](https://github.com/rshegde/paper-gstc_arbpol_bounds).

**Starting assumption:** the Achouri dipolar generalized sheet transition conditions (GSTCs), together with the stated constitutive and plane-wave model. This repository verifies their scattering and optimization consequences. It does **not** derive GSTCs from Maxwell equations.

The paper's main specialization is a homogeneous tangential sheet, normal incidence, and identical lossless exterior media. Individual theorem statements carry their precise hypotheses. Some supporting scattering results allow more general incidence or media; this does not remove the hypotheses of the paper's specialized results.

The canonical budget is `B = k₀ max(‖A‖₂, ‖D‖₂, ‖G‖₂)`, using tensor spectral norms throughout.

## Included proofs

- Ten-real-coordinate reciprocal, lossless **BI** material parameterization; **NB** means zero magnetoelectric coupling.
- Finite-sheet scattering, reciprocity, power balance, and unitary power-normalized response.
- Pole-free inverse-Cayley recovery, uniqueness, and rank-one scattering-completion completeness, including the reflectionless endpoint.
- Exact two-state polynomial feasibility and the **spectral**, rotation-invariant susceptibility budget.
- Attainment of class minima, closed feasible-cap rays, BI/NB comparison, and simultaneous-rotation covariance.
- BI and NB completion-space/material-space minimum equivalence.
- Attained nondegenerate NB peak efficiency and unitary orthonormal-frame spectral minima, including Jones-frame correspondence.
- Sharp linear-rotation and linear-to-circular spectral material minima, with finite-sheet attainment.
- Sharp unitary-rotation material budget for nonorthogonal input pairs, angle monotonicity, half-wave capacity, and explicit orthonormal/degenerate-task caveats.
- Rotated rank-one separation: completion completeness on the prescribed transmission fiber, finite-sheet recovery, exact physical spectral-resource image, and centered-arc Pareto optimality when `m ≤ 2`.

See [the theorem map](docs/THEOREMS.md) for entry points and scope limits, and [the extraction plan](docs/EXTRACTION.md) for the publication boundary. No distributional, Maxwell-to-GSTC, multipolar, or archived componentwise-minimum library is included. Electric-only/magnetic-only support identities and older coarse parameter-cap predicates remain dependencies of some feasibility proofs; the paper-facing minima use BI/NB and the spectral budget above.

The public namespace and library are **`GSTC`**. This is a standalone extraction: it has no dependency on the original LeanEM repository or its private history. The [manifest](docs/source-manifest.json) lists the 80 paper-facing theorem roots, original source hashes, and exported hashes. The initial extraction retains the proof/type dependency closure and elaboration support. The November 25 update adds the corresponding paper-specific application and frontier modules, including their mathematical support declarations. See the extraction notes for the precise boundary.

The November 25 update uses source snapshot `96b0e2f` and manuscript snapshot `ad620bd`. The S6 scalar-minimum formula, right-angle noncentered optimum, phase-global USD certificate, and algebraicity of general minimum endpoints remain outside this release's verified claims. The S6 Pareto theorem concerns the complete prescribed rotated transmission family; it does not supply the separate general BI peak-efficiency classification.

## Reproduce

Pinned versions: Lean **4.35.0** and Mathlib **v4.35.0**, with exact dependency revisions in `lake-manifest.json`. Install the matching Lean toolchain through Elan and provide Python 3, `flock`, `taskset`, and a Linux user systemd manager.

The supplied workflow fails closed unless the shared resource limits are active. The wrapper keeps the shared `leanem-build.slice` resource-control name so simultaneous projects remain subject to aggregate limits. This is not a LeanEM library dependency.

Install the supplied unit once, without increasing its limits:

```sh
mkdir -p ~/.config/systemd/user
cp scripts/systemd/leanem-build.slice ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user start leanem-build.slice
```

Then, from this repository:

```sh
scripts/run_restricted.sh lake exe cache get
scripts/verify.sh
```

Verification runs one job at a time: full library build, checks for every documented theorem root, transitive axiom audit of the companion theorems, and source/import-boundary audit. The wrapper limits the whole process tree to at most two logical CPUs, 12 GiB memory (8 GiB high watermark), zero swap, and 128 tasks, with a 20-minute command lifetime. On a machine without logical CPUs 0–1, set `LEANEM_CPU_LIST` to one or two valid CPU IDs. A terminated command is an incomplete check.

Emergency stop: `scripts/stop_verification.sh`. Read [AGENTS.md](AGENTS.md) before agent-assisted builds. On other platforms, provide equivalent external resource containment; the bundled Linux wrapper deliberately refuses to run uncontained.

The kernel audit permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. GSTCs are expressed as definitions and explicit hypotheses, not additional global axioms. No `sorry`, `admit`, or new axioms are permitted.

## License

Apache-2.0. Copyright 2026 Ravi Hegde. See [LICENSE](LICENSE) and [NOTICE](NOTICE). Dependencies retain their own licenses.
