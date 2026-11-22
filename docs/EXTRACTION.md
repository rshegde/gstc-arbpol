# Extraction and publication boundary

## Plan

1. Freeze the selected paper-facing source snapshot without altering the original working tree.
2. Retain the definitions of dipolar GSTCs and their constitutive, wave, Jones, and scattering model.
3. List the 53 paper-facing theorem statements in `source-manifest.json`; extract their elaborated proof/type dependencies and source declaration ranges.
4. Separate optional multipolar bridges from dipolar parameterization and generic boundary-operator solvability.
5. Remove declarations outside that dependency closure, retaining source-elaboration support; consolidate identical helpers, reduce imports, and rename the public library and namespace to `GSTC`.
6. Build the exported source independently, audit its axioms and import boundary, and publish with a fresh initial history.

## Assumptions versus conclusions

`gstcSatisfied` in `Boundary.lean` and `gstcSatisfied4` in `Unitarity.lean` state the assumed dipolar boundary equations for one-sided and two-sided illumination. They are the model input. Constitutive reciprocity and losslessness are specified by the corresponding dipolar predicates. Theorems establish consequences under those predicates; the library does not assert them for arbitrary materials.

The normal-incidence, tangential-sheet, equal-media conditions appear where required. Finite inverse-Cayley recovery explicitly excludes its poles. NB peak theorems preserve nonzero bilinear-cross and independent-frame hypotheses. Rotation covariance rotates the sheet and the prescribed Jones states together: it is not optimization over a physically rotated sheet with fixed laboratory target states.

## Excluded material

- Maxwell equations and their distributional/interface derivation.
- Idemen boundary-condition machinery, harmonic realization, and Maxwell-to-GSTC bridges.
- Multipolar constitutive tensors, quadrupoles, spatial-dispersion closure, and generalized boundary frameworks.
- Archived componentwise susceptibility objectives and their optimization.
- Research notes, agent transcripts, private development history, manuscript sources, figure-generation code, and unrelated LeanEM theorems.

No ambient geometry, vector-calculus, or Fresnel library is exported. `GSTC/Prelude.lean` supplies public Mathlib imports; `GSTC/Scattering/` contains the required transverse matrix/Jones model and proofs.

## Source adaptations

The manifest records every included module, source hash, exported hash, and adaptation. The extraction starts with the documented paper theorem roots, closes over actual compiled type/proof dependencies, and retains explicitly referenced source helpers required to elaborate those proofs. Removed declarations include optional bridges, unrelated synthesis/classification/example results, and unused general support. Source comments are trimmed to the copyright/license headers; the theorem map documents the public claims.

The selected snapshot includes the Jones-frame correspondence and spectral-minimum modules and their Pauli/phase support. Source and exported-file hashes identify the extraction. The public repository contains the source itself and has no private-repository dependency.

The minimality criterion is the dependency closure of these fixed paper results and their existing proofs, including indivisible structure/instance declarations and necessary elaboration support. It does not mean shortest possible alternative proofs. For example, the old electric-only and magnetic-only developments are reduced to the handful of identities used by NB synthesis, rather than exported wholesale. The canonical minima remain spectral and the physical hypotheses are preserved.

## History and publication

The companion is initialized as a new repository, rather than exposing a branch or fork containing LeanEM ancestors. Only the allowlisted companion source, license, manifests, documentation, and verification scripts enter its initial commit. Dependency caches, build artifacts, and local execution logs are ignored.
