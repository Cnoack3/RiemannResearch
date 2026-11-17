import RiemannResearch.RH.ExactHeadAtomMoment
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.Analysis.FiniteProfileEnergy
import RiemannResearch.RH.ExactHeadOccurrenceProjection
import Mathlib.Tactic.Ring

/-!
# Signed Green moment through the occurrence relaxation

Source: the 16 November 2026 exact-head Green and occurrence-block agendas.
The two-stage residual decomposition is applied to the affine signed probe.
An occurrence-specific correction is allowed only in the channel it annihilates.
No cofinal bound on either channel is assumed or asserted.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

/-- An arbitrary occurrence fit may be removed from the occurrence channel,
while the reuse channel keeps its exact signed contribution. -/
theorem fitted_moment_gap_eq_occurrence_reuse (P x : ℕ) (alpha : ℝ)
    (v c : ℕ → ℝ) (hv : v ∈ upperSpan P x (atom P)) :
    atomFittedMoment P x - alpha * atomEnergy P x =
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (occurrenceResidual P x)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r - fit P x c r) +
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (reuseResidual P x)
        (fun r => fittedMomentProbe x r - alpha * target P r - v r) := by
  let g : ℕ → ℝ := fun r => fittedMomentProbe x r - alpha * target P r - v r
  rw [fitted_moment_gap_eq_pairing P x alpha v hv]
  change pairing _ _ (atomResidual P x) g =
    pairing _ _ (occurrenceResidual P x) (fun r => g r - fit P x c r) +
      pairing _ _ (reuseResidual P x) g
  calc
    _ = pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (occurrenceResidual P x) (fun r => g r - fit P x c r) +
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (reuseResidual P x) g +
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (occurrenceResidual P x) (fit P x c) := by
      simp only [pairing, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [reuseResidual, Pi.sub_apply]
      ring
    _ = _ := by rw [occurrence_normal_fit P x c, add_zero]

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
