import RiemannResearch.RH.DyadicFiniteCriticalNorm
import RiemannResearch.RH.DyadicStepMeanIdentity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact physical boundaries of dyadic step refinement

Source: user-provided `DyadicRegularizedVerificationContinuation20260910.md`,
September 10, 2026, first next proof target. The statements and proofs below
derive the actual weighted step-boundary data required for the diagonal bound.
Even steps have zero kernel defect. Odd steps have a two-coordinate detail of
squared norm 1/2 and projected squared norm 1/4. The full odd-step recurrence
retains this detail exactly. No boundary or arithmetic provider is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem hilbertDilation_one_sequence (m : ℕ) (hm : 0 < m) :
    hilbertSequence (hilbertDilation m hm hilbertOne) =
      fun n => if m ≤ n then (m : ℝ) else 0 := by
  rw [hilbertDilation_sequence, hilbertOne_sequence]
  funext n
  unfold dilation zeroAnchor
  by_cases h : m ≤ n
  · have hn : n / m ≠ 0 := Nat.ne_of_gt (Nat.div_pos_iff.mpr ⟨hm, h⟩)
    simp [h, hn]
  · have hn : n / m = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge h)
    simp [h, hn]

theorem hilbertDilationAdjoint_two_even_step (l : ℕ) (hl : 0 < l) :
    hilbertDilationAdjoint 2 (by norm_num)
        (hilbertDilation (2*l) (by positivity) hilbertOne) =
      (2 : ℝ) • hilbertDilation l hl hilbertOne := by
  rw [← hilbertDilation_comp 2 l (by norm_num) hl, hilbertDilationAdjoint_dilation]
  norm_num

theorem hilbertDilationAdjoint_two_odd_step (l : ℕ) (hl : 0 < l) :
    hilbertDilationAdjoint 2 (by norm_num)
        (hilbertDilation (2*l+1) (by positivity) hilbertOne) =
      hilbertDilation l hl hilbertOne +
        hilbertDilation (l+1) (by positivity) hilbertOne := by
  apply hilbertSequence_injective
  funext k
  by_cases hk : k = 0
  · subst k; simp
  have hkp : 0 < k := Nat.pos_of_ne_zero hk
  rw [hilbertDilationAdjoint_coordinate 2 k (by norm_num) hkp,
    hilbertSequence_add, hilbertDilation_one_sequence,
    hilbertDilation_one_sequence, hilbertDilation_one_sequence]
  have hs : Finset.Ico (2*k) (2*(k+1)) = {2*k, 2*k+1} := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hs]
  rw [Finset.sum_pair (by omega : 2*k ≠ 2*k+1)]
  simp only [Pi.add_apply]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  have hk2 : 2*(k : ℝ)+1 ≠ 0 := by positivity
  rcases lt_trichotomy k l with h | h | h
  · have h1 : ¬2*l+1 ≤ 2*k := by omega
    have h2 : ¬2*l+1 ≤ 2*k+1 := by omega
    have h3 : ¬l ≤ k := by omega
    have h4 : ¬l+1 ≤ k := by omega
    simp [h1, h2, h3, h4]
  · subst k
    simp only [show ¬2*l+1 ≤ 2*l by omega, show 2*l+1 ≤ 2*l+1 by omega,
      show l ≤ l by omega, show ¬l+1 ≤ l by omega,
      if_false, if_true, mul_zero, zero_add, add_zero]
    unfold positiveWeight
    push_cast
    field_simp
    ring
  · have h1 : 2*l+1 ≤ 2*k := by omega
    have h2 : 2*l+1 ≤ 2*k+1 := by omega
    have h3 : l ≤ k := by omega
    have h4 : l+1 ≤ k := by omega
    simp only [h1, h2, h3, h4, if_true]
    unfold positiveWeight
    push_cast
    field_simp
    ring

/-- A single physical weighted Haar detail at the odd step boundary. -/
def dyadicStepBoundary (l : ℕ) (hl : 0 < l) : ThresholdHilbert :=
  -(l : ℝ) • hilbertAtom (2*l) (by positivity) +
    ((l : ℝ)+1) • hilbertAtom (2*l+1) (by positivity)

theorem dyadicKernelDefect_even_step (l : ℕ) (hl : 0 < l) :
    dyadicKernelDefect (hilbertDilation (2*l) (by positivity) hilbertOne) = 0 := by
  rw [dyadicKernelDefect_apply,
    ← hilbertDilation_comp 2 l (by norm_num) hl,
    hilbertBlockProjection_dilation, sub_self]

theorem dyadicKernelDefect_odd_step (l : ℕ) (hl : 0 < l) :
    dyadicKernelDefect (hilbertDilation (2*l+1) (by positivity) hilbertOne) =
      dyadicStepBoundary l hl := by
  rw [dyadicKernelDefect_apply, hilbertBlockProjection_apply,
    hilbertDilationAdjoint_two_odd_step l hl]
  have hadd := (hilbertDilationLinear 2 (by norm_num)).map_add
    (hilbertDilation l hl hilbertOne)
    (hilbertDilation (l+1) (by positivity) hilbertOne)
  change hilbertDilation 2 (by norm_num)
      (hilbertDilation l hl hilbertOne +
        hilbertDilation (l+1) (by positivity) hilbertOne) =
    hilbertDilation 2 (by norm_num) (hilbertDilation l hl hilbertOne) +
      hilbertDilation 2 (by norm_num)
        (hilbertDilation (l+1) (by positivity) hilbertOne) at hadd
  rw [hadd, hilbertDilation_comp 2 l (by norm_num) hl,
    hilbertDilation_comp 2 (l+1) (by norm_num) (by positivity)]
  apply hilbertSequence_injective
  funext k
  simp only [dyadicStepBoundary, hilbertSequence_sub, hilbertSequence_smul,
    hilbertDilation_one_sequence, hilbertSequence_add,
    hilbertAtom_sequence, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring_nf <;> omega

theorem dyadicStepBoundary_norm_sq (l : ℕ) (hl : 0 < l) :
    ‖dyadicStepBoundary l hl‖^2 = (1/2 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  unfold dyadicStepBoundary
  rw [inner_add_left, inner_add_right, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right,
    hilbertAtom_inner, hilbertAtom_sequence]
  simp only [show 2*l ≠ 2*l+1 by omega, show 2*l+1 ≠ 2*l by omega,
    if_false, if_true, mul_zero, add_zero, zero_add]
  unfold positiveWeight
  push_cast
  have h0 : (l : ℝ) ≠ 0 := by positivity
  have h1 : 2*(l : ℝ)+1 ≠ 0 := by positivity
  have h2 : (l : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem dyadicStepBoundary_adjoint_zero (l : ℕ) (hl : 0 < l) :
    hilbertDilationAdjoint 2 (by norm_num) (dyadicStepBoundary l hl) = 0 := by
  rw [← dyadicKernelDefect_odd_step l hl]
  exact dyadicKernelDefect_adjoint_zero _

theorem dyadicProjectedBoundary_norm_sq (l : ℕ) (hl : 0 < l) :
    ‖dyadicQuotientProjection (dyadicStepBoundary l hl)‖^2 = (1/4 : ℝ) := by
  rw [dyadicQuotientProjection_kernel_norm_sq _ (dyadicStepBoundary_adjoint_zero l hl),
    dyadicStepBoundary_norm_sq]
  norm_num

/-- The complete odd-step recurrence, with its physical boundary detail retained. -/
theorem dyadicProjectedStep_odd_recurrence (l : ℕ) (hl : 0 < l) :
    dyadicProjectedStep (2*l+1) (by positivity) =
      dyadicQuotientProjection (dyadicStepBoundary l hl) +
        (1/2 : ℝ) • (dyadicProjectedStep l hl +
          dyadicProjectedStep (l+1) (by positivity)) := by
  have h := dyadicQuotientProjection_kernelDefect
    (hilbertDilation (2*l+1) (by positivity) hilbertOne)
  rw [dyadicKernelDefect_odd_step l hl, hilbertDilationAdjoint_two_odd_step l hl,
    map_add] at h
  change _ = dyadicProjectedStep (2*l+1) _ -
    (1/2 : ℝ) • (dyadicProjectedStep l _ + dyadicProjectedStep (l+1) _) at h
  rw [h]
  abel

end
end RiemannResearch.RH.Pareto
