# Paper-to-Lean entry points

Names below are relative to `GSTC.Scattering` unless otherwise stated. Lean source statements are authoritative for hypotheses and normalization. The companion covers selected results, not every equation in the paper.

| Paper claim | Module / theorem entry point | Scope |
|---|---|---|
| Dipolar GSTCs | `gstcSatisfied` in `Boundary.lean`; `gstcSatisfied4` in `Unitarity.lean` | Starting model definitions; no Maxwell derivation |
| Exact ten-real BI representation | `BIParameterization`: `encode_decode`, `decode_encode`, `existsUnique_encoding` | Reciprocal, lossless, tangential susceptibilities |
| Finite forward scattering | `BIScattering`; `BICompletionMinimum.response_symmetric_unitary` | Configuration and normalization hypotheses are explicit |
| Inverse-Cayley completeness and uniqueness | `BIInverse.bi_inverse_complete`, `BIInverse.parametersForResponse_unique_gstc` | Symmetric-unitary response, pole-free Cayley denominator |
| Six real conversion equations | `BIAmplitudeFree.physicalFeasible_iff_amplitudeFreePolynomialFeasible` and following polynomial-system equivalences | Existing physical feasibility predicates, including zero efficiency |
| Section 3A material-space minimum | `ClassMinimumBudget.minimumBudget_attained`, `feasibleCaps_eq_Ici`, `minimumBudget_BI_le_NB`, `capFeasible_polynomial` | Nonempty loci attain; empty locus has `⊤`; cap polynomial theorem assumes nonnegative cap |
| Spectral-cap polynomial construction | `SusceptibilityBudgetPolynomials.spectralTotalBudget_polynomial` | The existing nine cap inequalities, not a new feasibility encoding |
| Rotation covariance | `FeasibilityRotation.classMaterials_rotate_iff`, `minimumBudget_rotate` | Simultaneous sheet/state rotation, including empty feasible sets |
| BI completion minimum | `BICompletionMinimum.minimum_eq_completionMinimum`, `completion_minimum_attained`, `minimum_at_nonsingular_class_peak` | General pole-free completion family; stated peak/frame assumptions retained |
| Complete BI rank-one frontier coordinates | `BIRankOneTheorem.rank_one_completion_iff_explicit`, `endpoint_unique`; `BIFrontierCompletion.admissible_has_rankOne` | Invertible transmission and normalized rank-one defect; reflectionless endpoint separate; admissibility includes pole exclusion |
| NB completion minimum | `NBCompletionMinimum.minimum_eq_completionMinimum`, `completion_minimum_attained`, `minimum_eq_phaseCompletionMinimum_at_peak`, `phaseCompletion_minimum_attained_at_peak`, `minimum_at_nonsingular_forced_peak` | Phase-inclusive general construction plus forced-phase specialization; no unjustified fixed phase in the zero-cross case |
| NB symmetry/reachability | `NBFeasibilityClassification.nb_unitary_feasible_iff_symmetric`, `two_state_nb_feasibility`; `NBPhaseConstraints.nb_two_state_phase_forced` | Full Jones-frame/bilinear restrictions, not overlap magnitudes alone |
| NB peak efficiency (Eq. 25) | `NBPeakEfficiency.eq25_nb_peak`, `nb_contraction_attained` | Nondegenerate cross/frame assumptions for Eq. 25; realization permits overall transmission phase |
| Unitary spectral cost and common-phase optimum (Eqs. 28–30) | `phaseSheetBudget` in `OrthogonalSpectralMinimum.lean`; `OrthogonalSpectralOptimum.fixedPhase_spectral_optimum`; `OrthogonalSpectralPhase.biMinimum_eq_phaseFamily`, `nbMinimum_eq_phaseFamily` | Finite sheet, spectral norm, and explicit pole exclusion |
| Connection to arbitrary orthonormal Jones frames | `JonesFrameCorrespondence.frameFamily_iff_columns`; `JonesFrameSpectralMinimum.frame_minima_attained` | Orthonormal input/output frames; equal unit efficiencies; attained BI/NB material minima |

## Scope limits

The general minimum-attainment and completion-equivalence theorems do not alone supply a compact closed formula for every nonunitary instance. The rank-one theorem is complete under its defect/invertibility assumptions; it does not silently discharge the phase-admissibility or Cayley-pole conditions.

The conventional analytical algorithms in Supplement Appendix C, the specialized Section 3C rotated-frame sharp bounds/Pareto frontiers, and the real-algebraic endpoint assertion are **not** claimed as Lean-verified here. Neither are arbitrary passive-frontier realizability or the derivation of the assumed GSTCs. The paper's numerical plots are not part of this proof companion.

The frame-minimum theorem strengthens the paper verification note's conservative description: the equality to an attained phase-family minimum is proved in Lean. This does not certify the separate explicit finite-candidate evaluation algorithm.
