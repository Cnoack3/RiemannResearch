import RiemannResearch.RH.DyadicStepBoundary

/-!
# Proved logarithmic diagonal growth of the actual projected steps

Source: user-provided `DyadicRegularizedVerificationContinuation20260910.md`,
September 10, 2026, first next proof target. This discharges its concrete
diagonal-growth provider via exact physical refinement and orthogonality.

For V_m = Q T_m 1, m ≤ 2^N implies ‖V_m‖² ≤ 1 + N/4. In particular the
triadic orbit satisfies the assembly's diagonal hypothesis with D = 3/2.
The exact recurrence retains the negative adjacent-step difference energy.
The actual damped step series is summable for every positive damping.
The off-diagonal majorant and prefix estimate, the product-index Möbius series,
the arithmetic remainder, and full two-seed completion are not proved here.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- On the adjoint kernel, projection satisfies an actual physical refinement law. -/
theorem dyadicQuotientProjection_kernel_refinement (u : ThresholdHilbert)
    (hu : hilbertDilationAdjoint 2 (by norm_num) u = 0) :
    dyadicQuotientProjection u = (1/2 : ℝ) • u +
      dyadicHalfDilation (dyadicQuotientProjection u) := by
  calc
    dyadicQuotientProjection u = (1/2 : ℝ) • dyadicKernelLift u :=
      dyadicQuotientProjection_eq_half_kernelLift u hu
    _ = (1/2 : ℝ) • (u + dyadicHalfDilation (dyadicKernelLift u)) :=
      congrArg (fun z : ThresholdHilbert => (1/2 : ℝ) • z) (dyadicKernelLift_eq u)
    _ = (1/2 : ℝ) • u + dyadicHalfDilation ((1/2 : ℝ) • dyadicKernelLift u) := by
      rw [smul_add, map_smul]
    _ = (1/2 : ℝ) • u + dyadicHalfDilation (dyadicQuotientProjection u) := by
      rw [dyadicQuotientProjection_eq_half_kernelLift u hu]

/-- Projection of a kernel vector preserves any zero initial segment. -/
theorem dyadicQuotientProjection_kernel_head_zero (u : ThresholdHilbert)
    (hu : hilbertDilationAdjoint 2 (by norm_num) u = 0)
    (m : ℕ) (hm : ∀ k < m, hilbertSequence u k = 0) :
    ∀ k < m, hilbertSequence (dyadicQuotientProjection u) k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkm
    by_cases hk : k = 0
    · subst k; simp
    have hkdiv : k / 2 < k := Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by norm_num)
    have hi := ih (k / 2) hkdiv (lt_trans hkdiv hkm)
    have he := congrArg (fun z : ThresholdHilbert => hilbertSequence z k)
      (dyadicQuotientProjection_kernel_refinement u hu)
    simp only [hilbertSequence_add, hilbertSequence_smul, dyadicHalfDilation_apply,
      hilbertDilation_sequence, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      dilation] at he
    simpa only [hm k hkm, hi, mul_zero, add_zero] using he

/-- A step pairs with a vector supported on its tail by its exact mean. -/
theorem hilbert_inner_step_of_head_zero (f : ThresholdHilbert)
    (m : ℕ) (hm : 0 < m) (hf : ∀ k < m, hilbertSequence f k = 0) :
    inner ℝ f (hilbertDilation m hm hilbertOne) =
      (m : ℝ) * inner ℝ f hilbertOne := by
  rw [hilbert_inner_weighted, hilbert_inner_weighted,
    hilbertDilation_one_sequence, hilbertOne_sequence]
  unfold paretoInner
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  by_cases hkm : m ≤ k
  · have hk : k ≠ 0 := by omega
    simp [hkm, zeroAnchor, hk]
    ring
  · have hz := hf k (Nat.lt_of_not_ge hkm)
    simp [hkm, hz]

theorem dyadicStepBoundary_head_zero (l : ℕ) (hl : 0 < l) :
    ∀ k < 2*l, hilbertSequence (dyadicStepBoundary l hl) k = 0 := by
  intro k hk
  simp only [dyadicStepBoundary, hilbertSequence_add, hilbertSequence_smul,
    hilbertAtom_sequence, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    if_neg (show k ≠ 2*l by omega), if_neg (show k ≠ 2*l+1 by omega),
    mul_zero, add_zero]

theorem dyadicProjectedBoundary_inner_one (l : ℕ) (hl : 0 < l) :
    inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl)) hilbertOne = 0 := by
  have h := congrArg (fun z : ThresholdHilbert => inner ℝ z hilbertOne)
    (dyadicProjectedStep_odd_recurrence l hl)
  simp only [inner_add_left, real_inner_smul_left,
    dyadicProjectedStep_inner_one] at h
  linarith

/-- The new odd boundary is orthogonal to every earlier projected step. -/
theorem dyadicProjectedBoundary_inner_step (l : ℕ) (hl : 0 < l)
    (m : ℕ) (hm : 0 < m) (hml : m ≤ 2*l) :
    inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl))
      (dyadicProjectedStep m hm) = 0 := by
  unfold dyadicProjectedStep
  rw [← dyadicQuotientProjection_inner, dyadicQuotientProjection_idempotent]
  have hz := dyadicQuotientProjection_kernel_head_zero (dyadicStepBoundary l hl)
    (dyadicStepBoundary_adjoint_zero l hl) (2*l) (dyadicStepBoundary_head_zero l hl)
  rw [hilbert_inner_step_of_head_zero _ m hm
    (fun k hk => hz k (lt_of_lt_of_le hk hml)), dyadicProjectedBoundary_inner_one]
  ring

/-- Exact odd-step energy. The average contains its full mixed inner product. -/
theorem dyadicProjectedStep_odd_norm_sq (l : ℕ) (hl : 0 < l) :
    ‖dyadicProjectedStep (2*l+1) (by positivity)‖^2 =
      (1/4 : ℝ) + (1/4 : ℝ) *
        ‖dyadicProjectedStep l hl + dyadicProjectedStep (l+1) (by positivity)‖^2 := by
  rw [dyadicProjectedStep_odd_recurrence l hl, norm_add_sq_real,
    real_inner_smul_right, inner_add_right,
    dyadicProjectedBoundary_inner_step l hl l hl (by omega),
    dyadicProjectedBoundary_inner_step l hl (l+1) (by positivity) (by omega),
    dyadicProjectedBoundary_norm_sq l hl, norm_smul, Real.norm_eq_abs, mul_pow]
  norm_num

theorem dyadicProjectedStep_odd_norm_sq_le (l : ℕ) (hl : 0 < l) :
    ‖dyadicProjectedStep (2*l+1) (by positivity)‖^2 ≤
      (1/4 : ℝ) + (1/2 : ℝ) * ‖dyadicProjectedStep l hl‖^2 +
        (1/2 : ℝ) * ‖dyadicProjectedStep (l+1) (by positivity)‖^2 := by
  rw [dyadicProjectedStep_odd_norm_sq l hl]
  have h := norm_add_le (dyadicProjectedStep l hl)
    (dyadicProjectedStep (l+1) (by positivity))
  have hn := norm_nonneg (dyadicProjectedStep l hl +
    dyadicProjectedStep (l+1) (by positivity))
  have hs := mul_self_le_mul_self hn h
  nlinarith [sq_nonneg (‖dyadicProjectedStep l hl‖ -
    ‖dyadicProjectedStep (l+1) (by positivity)‖)]

/-- The precise cancellation lost in the diagonal upper estimate. -/
theorem dyadicProjectedStep_odd_norm_sq_signed (l : ℕ) (hl : 0 < l) :
    ‖dyadicProjectedStep (2*l+1) (by positivity)‖^2 =
      (1/4 : ℝ) + (1/2 : ℝ) * ‖dyadicProjectedStep l hl‖^2 +
        (1/2 : ℝ) * ‖dyadicProjectedStep (l+1) (by positivity)‖^2 -
        (1/4 : ℝ) * ‖dyadicProjectedStep l hl -
          dyadicProjectedStep (l+1) (by positivity)‖^2 := by
  rw [dyadicProjectedStep_odd_norm_sq l hl]
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

/-- An unconditional logarithmic diagonal bound, stated without logarithm conventions. -/
theorem dyadicProjectedStep_norm_sq_le_depth (N m : ℕ) (hm : 0 < m)
    (hmN : m ≤ 2^N) : ‖dyadicProjectedStep m hm‖^2 ≤ 1 + (N : ℝ)/4 := by
  induction N generalizing m with
  | zero =>
    have he : m = 1 := by simpa only [pow_zero] using Nat.le_antisymm hmN hm
    subst m
    simp [dyadicProjectedStep_one, hilbertOne_norm_sq]
  | succ N ih =>
    by_cases h1 : m = 1
    · subst m
      simp only [dyadicProjectedStep_one, hilbertOne_norm_sq]
      have hc : 0 ≤ ((N+1 : ℕ) : ℝ)/4 := by positivity
      linarith
    have hm2 : 2 ≤ m := by omega
    have hl : 0 < m/2 := Nat.div_pos_iff.mpr ⟨by norm_num, hm2⟩
    have hpow := hmN
    rw [pow_succ'] at hpow
    have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div m 2
    by_cases he : m % 2 = 0
    · have hmform : m = 2*(m/2) := by omega
      have hb : m/2 ≤ 2^N := by omega
      have h := ih (m/2) hl hb
      have hv : dyadicProjectedStep m hm = dyadicProjectedStep (m/2) hl := by
        simpa only [← hmform] using dyadicProjectedStep_double (m/2) hl
      rw [hv]
      push_cast
      linarith
    · have hmform : m = 2*(m/2)+1 := by omega
      have hb : m/2 ≤ 2^N := by omega
      have hc : m/2+1 ≤ 2^N := by omega
      have h := ih (m/2) hl hb
      have h' := ih (m/2+1) (by positivity) hc
      have hr := dyadicProjectedStep_odd_norm_sq_le (m/2) hl
      have hv : dyadicProjectedStep (2*(m/2)+1) (by positivity) =
          dyadicProjectedStep m hm := by
        congr 1
        exact hmform.symm
      rw [hv] at hr
      push_cast
      linarith

theorem dyadicProjectedStep_triadic_norm_sq_le (j : ℕ) :
    ‖dyadicProjectedStep (3^(j+1)) (by positivity)‖^2 ≤ 1 + ((j : ℝ)+1)/2 := by
  have hb : 3^(j+1) ≤ 2^(2*(j+1)) := by
    calc
      3^(j+1) ≤ 4^(j+1) := Nat.pow_le_pow_left (by norm_num : (3 : ℕ) ≤ 4) (j + 1)
      _ = 2^(2*(j+1)) := by rw [pow_mul]; norm_num
  have h := dyadicProjectedStep_norm_sq_le_depth (2*(j+1)) (3^(j+1))
    (by positivity) hb
  push_cast at h
  linarith

/-- The actual triadic orbit satisfies the linear diagonal provider with D=3/2. -/
theorem dyadicProjectedStep_triadic_diagonal (j : ℕ) :
    ‖dyadicProjectedStep (3^(j+1)) (by positivity)‖^2 ≤
      (3/2 : ℝ) * ((j : ℝ)+1) := by
  have h := dyadicProjectedStep_triadic_norm_sq_le j
  have hj := (show (0 : ℝ) ≤ j from Nat.cast_nonneg j)
  nlinarith


/-- Concrete square-root growth for the triadic orbit; no arithmetic provider. -/
theorem dyadicProjectedStep_triadic_norm_le (j : ℕ) :
    ‖dyadicProjectedStep (3 ^ (j + 1)) (by positivity)‖ ≤
      Real.sqrt (3 / 2 : ℝ) * Real.sqrt ((j : ℝ) + 1) := by
  have hb := dyadicProjectedStep_triadic_diagonal j
  have hs : (Real.sqrt (3 / 2 : ℝ) * Real.sqrt ((j : ℝ) + 1)) ^ 2 =
      (3 / 2 : ℝ) * ((j : ℝ) + 1) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  have hp : 0 ≤ Real.sqrt (3 / 2 : ℝ) * Real.sqrt ((j : ℝ) + 1) := by positivity
  nlinarith [norm_nonneg (dyadicProjectedStep (3 ^ (j + 1)) (by positivity))]

/-- The actual discounted step series converges for every positive damping.
This is distinct from the still-open product-index Möbius series. -/
theorem dyadicStepAbelOrbit_series_summable (ε : ℝ) (hε : 0 < ε) :
    Summable (fun j : ℕ => triadicDampingRatio ε ^ j •
      dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne)) :=
  RiemannResearch.Analysis.AbelCoboundary.summable_geometric_of_sqrt_growth
    (triadicDampingRatio ε) (Real.sqrt (3 / 2 : ℝ))
    (triadicDampingRatio_pos ε).le (triadicDampingRatio_lt_one hε)
    (Real.sqrt_nonneg _) _ dyadicProjectedStep_triadic_norm_le


end
end RiemannResearch.RH.Pareto
