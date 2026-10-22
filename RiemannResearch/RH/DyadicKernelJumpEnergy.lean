import RiemannResearch.RH.DyadicBoundaryParseval
import RiemannResearch.RH.DyadicCriticalResolvent

/-!
# Exact physical jump energies of the dyadic kernel and critical resolvent

Source: user-provided DyadicGramPrefixVerification20260910(1).md and its
September 10 continuation toward arithmetic-series convergence. The formulas
follow from the established complete boundary Parseval and physical adjoint.
The nonnegative jump series is proved summable. Actual residue block growth
and all-positive-damping arithmetic convergence remain separate obligations.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem dyadicKernelDefect_inner (f g : ThresholdHilbert) :
    inner ℝ (dyadicKernelDefect f) g = inner ℝ f (dyadicKernelDefect g) := by
  have h (u v : ThresholdHilbert) :
      inner ℝ u (hilbertDilationAdjoint 2 (by norm_num) v) =
        inner ℝ (hilbertDilation 2 (by norm_num) u) v := by
    exact ContinuousLinearMap.adjoint_inner_right
      (hilbertDilationContinuous 2 (by norm_num)) u v
  rw [dyadicKernelDefect_apply, dyadicKernelDefect_apply,
    inner_sub_left, inner_sub_right, hilbertBlockProjection_apply,
    hilbertBlockProjection_apply, real_inner_smul_left, real_inner_smul_right]
  congr 1
  rw [← h]
  have he :
      inner ℝ f (hilbertDilation 2 (by norm_num)
        (hilbertDilationAdjoint 2 (by norm_num) g)) =
      inner ℝ (hilbertDilationAdjoint 2 (by norm_num) f)
        (hilbertDilationAdjoint 2 (by norm_num) g) := by
    calc
      _ = inner ℝ (hilbertDilation 2 (by norm_num)
          (hilbertDilationAdjoint 2 (by norm_num) g)) f := real_inner_comm _ _
      _ = inner ℝ (hilbertDilationAdjoint 2 (by norm_num) g)
          (hilbertDilationAdjoint 2 (by norm_num) f) :=
        (h (hilbertDilationAdjoint 2 (by norm_num) g) f).symm
      _ = _ := real_inner_comm _ _
  rw [he]

theorem dyadicKernelDefect_eq_self_of_adjoint_zero (f : ThresholdHilbert)
    (hf : hilbertDilationAdjoint 2 (by norm_num) f = 0) :
    dyadicKernelDefect f = f := by
  have hz : hilbertDilation 2 (by norm_num) (0 : ThresholdHilbert) = 0 := by
    change (hilbertDilationContinuous 2 (by norm_num)) 0 = 0
    exact map_zero _
  simp [dyadicKernelDefect_apply, hilbertBlockProjection_apply, hf, hz]

theorem dyadicKernelDefect_one_eq_atom :
    dyadicKernelDefect hilbertOne = hilbertAtom 1 (by norm_num) := by
  rw [dyadicKernelDefect_apply, hilbertBlockProjection_apply,
    hilbertDilationAdjoint_one]
  simp [hilbertAtom, hilbertTail, hilbertDilation_one]

theorem dyadicKernelDefect_mean (f : ThresholdHilbert) :
    inner ℝ hilbertOne (dyadicKernelDefect f) = hilbertSequence f 1 / 2 := by
  rw [← dyadicKernelDefect_inner, dyadicKernelDefect_one_eq_atom, hilbertAtom_inner]
  norm_num [positiveWeight] <;> ring

theorem dyadicStepBoundary_inner_coordinates (l : ℕ) (hl : 0 < l)
    (f : ThresholdHilbert) :
    inner ℝ (dyadicStepBoundary l hl) f =
      (hilbertSequence f (2*l+1) - hilbertSequence f (2*l)) /
        (2 * (2*(l : ℝ)+1)) := by
  rw [dyadicStepBoundary, inner_add_left,
    real_inner_smul_left, real_inner_smul_left,
    hilbertAtom_inner, hilbertAtom_inner]
  unfold positiveWeight
  push_cast
  have h0 : (l : ℝ) ≠ 0 := by positivity
  have h1 : 2*(l : ℝ)+1 ≠ 0 := by positivity
  have h2 : (l : ℝ)+1 ≠ 0 := by positivity
  field_simp <;> ring

theorem dyadicProjectedBoundary_inner_kernelDefect
    (l : ℕ) (hl : 0 < l) (f : ThresholdHilbert) :
    inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl))
      (dyadicKernelDefect f) =
      (1/2 : ℝ) * inner ℝ (dyadicStepBoundary l hl) f := by
  have h := dyadicQuotientProjection_kernel_inner
    (dyadicStepBoundary l hl) (dyadicKernelDefect f)
    (dyadicStepBoundary_adjoint_zero l hl) (dyadicKernelDefect_adjoint_zero f)
  rw [← dyadicQuotientProjection_inner,
    dyadicQuotientProjection_idempotent] at h
  have hk : inner ℝ (dyadicStepBoundary l hl) (dyadicKernelDefect f) =
      inner ℝ (dyadicStepBoundary l hl) f := by
    rw [← dyadicKernelDefect_inner,
      dyadicKernelDefect_eq_self_of_adjoint_zero _
        (dyadicStepBoundary_adjoint_zero l hl)]
  rw [hk] at h
  exact h

theorem dyadicKernelDefect_norm_sq_boundary (f : ThresholdHilbert) :
    ‖dyadicKernelDefect f‖^2 = (hilbertSequence f 1)^2 / 2 +
      2 * ∑' n : ℕ, (inner ℝ (dyadicStepBoundary (n+1) (by positivity)) f)^2 := by
  have h := dyadicBoundary_parseval_norm_sq (dyadicKernelDefect f)
  rw [dyadicQuotientProjection_kernel_norm_sq _
    (dyadicKernelDefect_adjoint_zero f), dyadicKernelDefect_mean] at h
  simp_rw [dyadicProjectedBoundary_inner_kernelDefect] at h
  have hs : (∑' n : ℕ, 4 * ((1/2 : ℝ) *
      inner ℝ (dyadicStepBoundary (n+1) (by positivity)) f)^2) =
      ∑' n : ℕ, (inner ℝ (dyadicStepBoundary (n+1) (by positivity)) f)^2 := by
    apply tsum_congr
    intro n
    ring
  rw [hs] at h
  nlinarith

theorem dyadicKernelDefect_jump_energy_summable (f : ThresholdHilbert) :
    Summable (fun n : ℕ =>
      (hilbertSequence f (2*(n+1)+1) - hilbertSequence f (2*(n+1)))^2 /
        (2 * (2*((n : ℝ)+1)+1)^2)) := by
  have hs := (dyadicBoundary_mixed_pairings_summable
    (dyadicKernelDefect f) (dyadicKernelDefect f)).mul_left (2 : ℝ)
  apply hs.congr
  intro n
  rw [dyadicProjectedBoundary_inner_kernelDefect,
    dyadicStepBoundary_inner_coordinates]
  push_cast
  field_simp <;> ring

theorem dyadicKernelDefect_norm_sq_jumps (f : ThresholdHilbert) :
    ‖dyadicKernelDefect f‖^2 = (hilbertSequence f 1)^2 / 2 +
      ∑' n : ℕ,
        (hilbertSequence f (2*(n+1)+1) - hilbertSequence f (2*(n+1)))^2 /
          (2 * (2*((n : ℝ)+1)+1)^2) := by
  rw [dyadicKernelDefect_norm_sq_boundary, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  rw [dyadicStepBoundary_inner_coordinates]
  push_cast
  field_simp <;> ring

theorem dyadicQuotientProjection_norm_sq_resolvent_jumps (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection f‖^2 =
      (hilbertSequence (dyadicCriticalResolvent f) 1)^2 / 4 +
      (1/2 : ℝ) * ∑' n : ℕ,
        (hilbertSequence (dyadicCriticalResolvent f) (2*(n+1)+1) -
          hilbertSequence (dyadicCriticalResolvent f) (2*(n+1)))^2 /
          (2 * (2*((n : ℝ)+1)+1)^2) := by
  rw [dyadicQuotientProjection_norm_sq_eq_criticalResolvent,
    dyadicKernelDefect_norm_sq_jumps]
  ring

end
end RiemannResearch.RH.Pareto
