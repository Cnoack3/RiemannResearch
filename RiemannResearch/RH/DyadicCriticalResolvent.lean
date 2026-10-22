import RiemannResearch.RH.DyadicFiniteCriticalNorm

/-!
# Complete operator realization of the critical dyadic quotient norm

Source: the user-provided September 10, 2026 dyadic-regularization ledger,
critical quotient norm provider (N5). This operator realization supplies exact
norm and Gram identities while leaving the boundary identification separate.

For the actual T = T₂ and D = I - T T* / 2, the series
H f = Σ_j (T*/2)^j f converges in the physical Hilbert norm for every f.
We prove Q D H f = Q f and hence ‖Q f‖² = ‖D H f‖² / 2, with the
corresponding complete mixed Gram identity. No orbit growth, convergence,
projection, or arithmetic provider is assumed. This is an operator norm
realization; the dyadic boundary identification and uniform arithmetic
estimates needed for the regularized family remain separate obligations.
-/

namespace RiemannResearch.RH.Pareto

open RiemannResearch.Analysis.AbelCoboundary
noncomputable section

def dyadicHalfAdjoint : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / 2 : ℝ) • hilbertDilationAdjoint 2 (by norm_num)

@[simp] theorem dyadicHalfAdjoint_apply (f : ThresholdHilbert) :
    dyadicHalfAdjoint f = (1 / 2 : ℝ) • hilbertDilationAdjoint 2 (by norm_num) f := rfl

theorem dyadicHalfAdjoint_norm_sq_le (f : ThresholdHilbert) :
    ‖dyadicHalfAdjoint f‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  have hp : ‖hilbertBlockProjection 2 (by norm_num) f‖ ^ 2 =
      (1 / 2 : ℝ) * ‖hilbertDilationAdjoint 2 (by norm_num) f‖ ^ 2 := by
    rw [hilbertBlockProjection_apply, norm_smul, Real.norm_eq_abs, mul_pow,
      hilbertDilation_norm_sq]
    norm_num
    ring
  have he := hilbertBlockProjection_pythagoras 2 (by norm_num) f
  rw [hp] at he
  rw [dyadicHalfAdjoint_apply, norm_smul, Real.norm_eq_abs, mul_pow]
  norm_num
  nlinarith [sq_nonneg ‖f - hilbertBlockProjection 2 (by norm_num) f‖]

theorem dyadicHalfAdjoint_norm_le (f : ThresholdHilbert) :
    ‖dyadicHalfAdjoint f‖ ≤ (3 / 4 : ℝ) * ‖f‖ := by
  nlinarith [dyadicHalfAdjoint_norm_sq_le f, norm_nonneg (dyadicHalfAdjoint f),
    norm_nonneg f, sq_nonneg ‖f‖]

theorem dyadicHalfAdjoint_orbit_norm_le (f : ThresholdHilbert) (j : ℕ) :
    ‖orbit dyadicHalfAdjoint f j‖ ≤ (3 / 4 : ℝ) ^ j * ‖f‖ := by
  induction j with
  | zero => simp only [orbit_zero, pow_zero, one_mul, le_refl]
  | succ j ih =>
      calc
        _ ≤ (3 / 4 : ℝ) * ‖orbit dyadicHalfAdjoint f j‖ := dyadicHalfAdjoint_norm_le _
        _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ j * ‖f‖) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (3 / 4 : ℝ) ^ (j + 1) * ‖f‖ := by rw [pow_succ]; ring

/-- Actual absolute norm convergence for every physical vector. -/
theorem dyadicCriticalResolvent_summable (f : ThresholdHilbert) :
    Summable (orbit dyadicHalfAdjoint f) := by
  have hg := (summable_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).mul_right ‖f‖
  exact (Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => dyadicHalfAdjoint_orbit_norm_le f j) hg).of_norm

def dyadicCriticalResolvent (f : ThresholdHilbert) : ThresholdHilbert :=
  ∑' j : ℕ, orbit dyadicHalfAdjoint f j

theorem dyadicCriticalResolvent_eq (f : ThresholdHilbert) :
    dyadicCriticalResolvent f = f + dyadicHalfAdjoint (dyadicCriticalResolvent f) := by
  calc
    _ = orbit dyadicHalfAdjoint f 0 + ∑' j : ℕ, orbit dyadicHalfAdjoint f (j + 1) :=
      (dyadicCriticalResolvent_summable f).tsum_eq_zero_add
    _ = f + dyadicHalfAdjoint (dyadicCriticalResolvent f) := by
      rw [dyadicCriticalResolvent,
        dyadicHalfAdjoint.map_tsum (dyadicCriticalResolvent_summable f)]
      rfl

/-- The complete resolvent cancels the dyadic quotient defect exactly. -/
theorem dyadicQuotientProjection_kernelDefect_resolvent (f : ThresholdHilbert) :
    dyadicQuotientProjection (dyadicKernelDefect (dyadicCriticalResolvent f)) =
      dyadicQuotientProjection f := by
  have h := congrArg dyadicQuotientProjection (dyadicCriticalResolvent_eq f)
  rw [map_add, dyadicHalfAdjoint_apply, map_smul] at h
  rw [dyadicQuotientProjection_kernelDefect]
  exact sub_eq_iff_eq_add.mpr h

/-- Exact reconstruction of Qf using two convergent physical operator series. -/
theorem dyadicQuotientProjection_eq_kernelLift_resolvent (f : ThresholdHilbert) :
    dyadicQuotientProjection f = (1 / 2 : ℝ) •
      dyadicKernelLift (dyadicKernelDefect (dyadicCriticalResolvent f)) := by
  rw [← dyadicQuotientProjection_kernelDefect_resolvent f]
  exact dyadicQuotientProjection_eq_half_kernelLift _ (dyadicKernelDefect_adjoint_zero _)

/-- The critical quotient norm is now realized for every actual Hilbert vector. -/
theorem dyadicQuotientProjection_norm_sq_eq_criticalResolvent (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection f‖ ^ 2 =
      (1 / 2 : ℝ) * ‖dyadicKernelDefect (dyadicCriticalResolvent f)‖ ^ 2 := by
  rw [← dyadicQuotientProjection_kernelDefect_resolvent f]
  exact dyadicQuotientProjection_kernel_norm_sq _ (dyadicKernelDefect_adjoint_zero _)

/-- Every mixed Gram term is retained in the complete critical realization. -/
theorem dyadicQuotientProjection_inner_eq_criticalResolvent (f g : ThresholdHilbert) :
    inner ℝ (dyadicQuotientProjection f) (dyadicQuotientProjection g) =
      (1 / 2 : ℝ) * inner ℝ (dyadicKernelDefect (dyadicCriticalResolvent f))
        (dyadicKernelDefect (dyadicCriticalResolvent g)) := by
  rw [← dyadicQuotientProjection_kernelDefect_resolvent f,
    ← dyadicQuotientProjection_kernelDefect_resolvent g]
  exact dyadicQuotientProjection_kernel_inner _ _
    (dyadicKernelDefect_adjoint_zero _) (dyadicKernelDefect_adjoint_zero _)

end
end RiemannResearch.RH.Pareto
