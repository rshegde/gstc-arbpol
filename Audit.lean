import GSTC
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Check every imported companion theorem, rather than a handpicked sample.
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let localModule := (env.getModuleIdxFor? name).any (fun i =>
      env.header.moduleNames[i]!.toString.startsWith "GSTC.")
    if localModule then
      if info.isAxiom then
        throwError "Unexpected companion axiom: {name}"
      if info.isTheorem then
        let axioms ← collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "{name} depends on forbidden axiom {ax}"
        count := count + 1
  if count == 0 then
    throwError "No companion theorems audited"
  logInfo m!"PASS: {count} companion theorems; only propext, Classical.choice, Quot.sound permitted."
  let source ← liftIO <| IO.FS.readFile "docs/source-manifest.json"
  let json ← match Json.parse source with
    | .ok j => pure j
    | .error e => throwError "Invalid source manifest: {e}"
  let roots ← match json.getObjValAs? (Array String) "paper_theorems" with
    | .ok names => pure names
    | .error e => throwError "Missing paper theorem roots: {e}"
  for text in roots do
    let name := (text.splitOn ".").foldl Name.str Name.anonymous
    unless (env.find? name).any ConstantInfo.isTheorem do
      throwError "Missing paper theorem: {name}"
  logInfo m!"PASS: all {roots.size} documented paper theorem roots are present."

#print axioms GSTC.Scattering.BIInverse.bi_inverse_complete
#print axioms GSTC.Scattering.ClassMinimumBudget.minimumBudget_attained
#print axioms GSTC.Scattering.ClassMinimumBudget.capFeasible_polynomial
#print axioms GSTC.Scattering.FeasibilityRotation.minimumBudget_rotate
#print axioms GSTC.Scattering.BICompletionMinimum.minimum_eq_completionMinimum
#print axioms GSTC.Scattering.NBCompletionMinimum.minimum_eq_phaseCompletionMinimum_at_peak
#print axioms GSTC.Scattering.BIRankOneTheorem.rank_one_completion_iff_explicit
#print axioms GSTC.Scattering.BIRankOneTheorem.endpoint_unique
#print axioms GSTC.Scattering.NBPeakEfficiency.eq25_nb_peak
#print axioms GSTC.Scattering.JonesFrameSpectralMinimum.frame_minima_attained
