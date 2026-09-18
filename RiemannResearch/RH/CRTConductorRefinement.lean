import RiemannResearch.RH.CRTExactDigamma
import RiemannResearch.RH.CRTPeriodicEnergy

/-!
# Exact progression refinement under conductor enlargement
Source: user-provided CRT handoff, with the index decomposition k=a*q+j.
These equalities retain the ordered arithmetic residue weights.
-/
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
noncomputable section

theorem progressionL_conductor_refinement {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r)
    (a : ℕ) (ha : 0 < a) :
    progressionL Q r =
      ∑ j : Fin a, progressionL (Q*(a : ℝ)) (r+Q*(j.val : ℝ)) := by
  cases a with
  | zero => omega
  | succ a =>
    change (∑' k : ℕ, lKernel (Q*(k : ℝ)+r)) = _
    rw [Nat.sumByResidueClasses (progressionL_summable hQ hr) (a+1)]
    apply Finset.sum_congr rfl
    intro j hj
    unfold progressionL
    apply tsum_congr
    intro k
    change lKernel (Q*((j.val+(a+1)*k : ℕ) : ℝ)+r) =
      lKernel (Q*((a+1 : ℕ) : ℝ)*(k : ℝ)+(r+Q*(j.val : ℝ)))
    congr 1
    push_cast
    ring

theorem progressionM_conductor_refinement {Q r : ℝ} (hQ : 0 < Q) (hr : 0 < r)
    (a : ℕ) (ha : 0 < a) :
    progressionM Q r =
      ∑ j : Fin a, progressionM (Q*(a : ℝ)) (r+Q*(j.val : ℝ)) := by
  cases a with
  | zero => omega
  | succ a =>
    change (∑' k : ℕ, lKernel (Q*(k : ℝ)+r)/(Q*(k : ℝ)+r)) = _
    rw [Nat.sumByResidueClasses (progressionM_summable hQ hr) (a+1)]
    apply Finset.sum_congr rfl
    intro j hj
    unfold progressionM
    apply tsum_congr
    intro k
    have he : Q*((j.val+(a+1)*k : ℕ) : ℝ)+r =
        Q*((a+1 : ℕ) : ℝ)*(k : ℝ)+(r+Q*(j.val : ℝ)) := by
      push_cast
      ring
    rw [he]
    rfl

end
end RiemannResearch.RH.CRTBlock
