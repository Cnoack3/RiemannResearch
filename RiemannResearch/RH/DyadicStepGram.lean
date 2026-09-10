import RiemannResearch.RH.DyadicStepLogBound
import Mathlib.Tactic.Module

/-!
# Exact off-diagonal dyadic Gram refinement and adjacent-step energies

Source: user-provided `DyadicRegularizedVerificationContinuation20260910.md`,
September 10, 2026; exact Gram and signed energy continuation.

These identities are consequences of the actual weighted step boundary and
its proved orthogonality. They assume no arithmetic cancellation or Gram
majorant. They do not establish the remaining uniform Abel prefix estimate.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Off the diagonal, the odd boundary contributes exactly zero. -/
theorem dyadicProjectedStep_odd_inner_step (l : ℕ) (hl : 0 < l)
    (m : ℕ) (hm : 0 < m) (hml : m ≤ 2*l) :
    inner ℝ (dyadicProjectedStep (2*l+1) (by positivity))
        (dyadicProjectedStep m hm) =
      (1/2 : ℝ) * (inner ℝ (dyadicProjectedStep l hl)
        (dyadicProjectedStep m hm) +
        inner ℝ (dyadicProjectedStep (l+1) (by positivity))
          (dyadicProjectedStep m hm)) := by
  rw [dyadicProjectedStep_odd_recurrence l hl, inner_add_left,
    real_inner_smul_left, inner_add_left,
    dyadicProjectedBoundary_inner_step l hl m hm hml, zero_add]

/-- The refinement details at distinct physical boundaries are orthogonal. -/
theorem dyadicProjectedBoundary_inner_boundary_of_lt (l k : ℕ)
    (hl : 0 < l) (hk : 0 < k) (hlk : l < k) :
    inner ℝ (dyadicQuotientProjection (dyadicStepBoundary k hk))
      (dyadicQuotientProjection (dyadicStepBoundary l hl)) = 0 := by
  have h := congrArg
    (fun z : ThresholdHilbert =>
      inner ℝ (dyadicQuotientProjection (dyadicStepBoundary k hk)) z)
    (dyadicProjectedStep_odd_recurrence l hl)
  rw [inner_add_right, real_inner_smul_right, inner_add_right,
    dyadicProjectedBoundary_inner_step k hk (2*l+1) (by positivity) (by omega),
    dyadicProjectedBoundary_inner_step k hk l hl (by omega),
    dyadicProjectedBoundary_inner_step k hk (l+1) (by positivity) (by omega)] at h
  linarith

theorem dyadicProjectedBoundary_inner_boundary (l k : ℕ)
    (hl : 0 < l) (hk : 0 < k) (hlk : l ≠ k) :
    inner ℝ (dyadicQuotientProjection (dyadicStepBoundary l hl))
      (dyadicQuotientProjection (dyadicStepBoundary k hk)) = 0 := by
  rcases lt_or_gt_of_ne hlk with h | h
  · rw [real_inner_comm]
    exact dyadicProjectedBoundary_inner_boundary_of_lt l k hl hk h
  · exact dyadicProjectedBoundary_inner_boundary_of_lt k l hk hl h

/-- The left half of an adjacent difference retains the signed boundary. -/
theorem dyadicProjectedStep_even_adjacent_difference (l : ℕ) (hl : 0 < l) :
    dyadicProjectedStep (2*l) (by positivity) -
        dyadicProjectedStep (2*l+1) (by positivity) =
      -dyadicQuotientProjection (dyadicStepBoundary l hl) +
        (1/2 : ℝ) • (dyadicProjectedStep l hl -
          dyadicProjectedStep (l+1) (by positivity)) := by
  rw [dyadicProjectedStep_double l hl, dyadicProjectedStep_odd_recurrence l hl]
  module

/-- The right half has the opposite boundary sign. -/
theorem dyadicProjectedStep_odd_adjacent_difference (l : ℕ) (hl : 0 < l) :
    dyadicProjectedStep (2*l+1) (by positivity) -
        dyadicProjectedStep (2*l+2) (by positivity) =
      dyadicQuotientProjection (dyadicStepBoundary l hl) +
        (1/2 : ℝ) • (dyadicProjectedStep l hl -
          dyadicProjectedStep (l+1) (by positivity)) := by
  have hd : dyadicProjectedStep (2*l+2) (by positivity) =
      dyadicProjectedStep (l+1) (by positivity) := by
    have he : 2*l+2 = 2*(l+1) := by omega
    simpa only [he] using dyadicProjectedStep_double (l+1) (by positivity)
  rw [hd, dyadicProjectedStep_odd_recurrence l hl]
  module

theorem dyadicProjectedStep_even_adjacent_norm_sq (l : ℕ) (hl : 0 < l) :
    ‖dyadicProjectedStep (2*l) (by positivity) -
        dyadicProjectedStep (2*l+1) (by positivity)‖^2 =
      (1/4 : ℝ) + (1/4 : ℝ) *
        ‖dyadicProjectedStep l hl - dyadicProjectedStep (l+1) (by positivity)‖^2 := by
  rw [dyadicProjectedStep_even_adjacent_difference l hl, norm_add_sq_real, norm_neg,
    inner_neg_left, real_inner_smul_right, inner_sub_right,
    dyadicProjectedBoundary_inner_step l hl l hl (by omega),
    dyadicProjectedBoundary_inner_step l hl (l+1) (by positivity) (by omega),
    dyadicProjectedBoundary_norm_sq l hl, norm_smul, Real.norm_eq_abs, mul_pow]
  norm_num

theorem dyadicProjectedStep_odd_adjacent_norm_sq (l : ℕ) (hl : 0 < l) :
    ‖dyadicProjectedStep (2*l+1) (by positivity) -
        dyadicProjectedStep (2*l+2) (by positivity)‖^2 =
      (1/4 : ℝ) + (1/4 : ℝ) *
        ‖dyadicProjectedStep l hl - dyadicProjectedStep (l+1) (by positivity)‖^2 := by
  rw [dyadicProjectedStep_odd_adjacent_difference l hl, norm_add_sq_real,
    real_inner_smul_right, inner_sub_right,
    dyadicProjectedBoundary_inner_step l hl l hl (by omega),
    dyadicProjectedBoundary_inner_step l hl (l+1) (by positivity) (by omega),
    dyadicProjectedBoundary_norm_sq l hl, norm_smul, Real.norm_eq_abs, mul_pow]
  norm_num

/-- Every adjacent difference has an exact energy depending only on its dyadic annulus. -/
theorem dyadicProjectedStep_adjacent_norm_sq_on_annulus (N m : ℕ)
    (hm : 0 < m) (hlo : 2^N ≤ m) (hhi : m < 2^(N+1)) :
    ‖dyadicProjectedStep m hm - dyadicProjectedStep (m+1) (by positivity)‖^2 =
      (1 - (1/4 : ℝ)^N) / 3 := by
  induction N generalizing m with
  | zero =>
    have hm1 : m = 1 := by norm_num at hlo hhi; omega
    subst m
    have hd : dyadicProjectedStep 2 (by norm_num) =
        dyadicProjectedStep 1 (by norm_num) := by
      simpa using dyadicProjectedStep_double 1 (by norm_num)
    rw [hd, sub_self, norm_zero]
    norm_num
  | succ N ih =>
    have hp : 0 < (2 : ℕ)^N := by positivity
    have hlo' := hlo
    have hhi' := hhi
    rw [pow_succ'] at hlo'
    rw [pow_succ'] at hhi'
    have hl : 0 < m/2 := by omega
    have hlower : 2^N ≤ m/2 := by omega
    have hupper : m/2 < 2^(N+1) := by omega
    have hi := ih (m/2) hl hlower hupper
    have hmod := Nat.mod_lt m (by norm_num : 0 < 2)
    have hdecomp := Nat.mod_add_div m 2
    have hr : ‖dyadicProjectedStep m hm -
          dyadicProjectedStep (m+1) (by positivity)‖^2 =
        (1/4 : ℝ) + (1/4 : ℝ) *
          ‖dyadicProjectedStep (m/2) hl -
            dyadicProjectedStep (m/2+1) (by positivity)‖^2 := by
      by_cases he : m % 2 = 0
      · have hmform : m = 2*(m/2) := by omega
        simpa only [← hmform] using dyadicProjectedStep_even_adjacent_norm_sq (m/2) hl
      · have hmform : m = 2*(m/2)+1 := by omega
        have hmnext : m+1 = 2*(m/2)+2 := by omega
        simpa only [← hmform, ← hmnext] using
          dyadicProjectedStep_odd_adjacent_norm_sq (m/2) hl
    rw [hr, hi, pow_succ]
    ring

end
end RiemannResearch.RH.Pareto


/-!
Source: the user-supplied DyadicRegularizedVerificationContinuation20260910
(1).md, September 10, 2026. These are exact finite signed energy identities
for the physical refinement boundaries; no arithmetic estimate is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Complete Gram pairing for finite signed combinations of distinct boundaries. -/
theorem dyadicProjectedBoundary_finite_inner
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hinj : Function.Injective m) :
    inner ℝ (∑ i ∈ s, a i • dyadicQuotientProjection (dyadicStepBoundary (m i) (hm i)))
      (∑ i ∈ s, b i • dyadicQuotientProjection (dyadicStepBoundary (m i) (hm i))) =
        (1/4 : ℝ) * ∑ i ∈ s, a i * b i := by
  classical
  rw [sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, dyadicProjectedBoundary_norm_sq (m i) (hm i)]
    ring
  · intro j hj hji
    have hij : m i ≠ m j := by
      intro h
      exact hji (hinj h).symm
    rw [real_inner_smul_left, real_inner_smul_right,
      dyadicProjectedBoundary_inner_boundary (m i) (m j) (hm i) (hm j) hij]
    ring
  · intro h
    exact False.elim (h hi)

/-- The exact energy is diagonal, with no positivity restriction on coefficients. -/
theorem dyadicProjectedBoundary_finite_norm_sq
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hinj : Function.Injective m) :
    ‖∑ i ∈ s, a i • dyadicQuotientProjection (dyadicStepBoundary (m i) (hm i))‖^2 =
      (1/4 : ℝ) * ∑ i ∈ s, (a i)^2 := by
  rw [← real_inner_self_eq_norm_sq,
    dyadicProjectedBoundary_finite_inner s a a m hm hinj]
  simp only [pow_two]

/-- Adding the mean coordinate preserves the exact orthogonal decomposition. -/
theorem dyadicProjectedBoundary_finite_mean_energy
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hinj : Function.Injective m) (t : ℝ) :
    ‖t • hilbertOne +
        ∑ i ∈ s, a i • dyadicQuotientProjection (dyadicStepBoundary (m i) (hm i))‖^2 =
      t^2 + (1/4 : ℝ) * ∑ i ∈ s, (a i)^2 := by
  have hz : inner ℝ hilbertOne
      (∑ i ∈ s, a i • dyadicQuotientProjection (dyadicStepBoundary (m i) (hm i))) = 0 := by
    rw [real_inner_comm, sum_inner]
    simp only [real_inner_smul_left, dyadicProjectedBoundary_inner_one,
      mul_zero, Finset.sum_const_zero]
  rw [norm_add_sq_real, real_inner_smul_left, hz,
    dyadicProjectedBoundary_finite_norm_sq s a m hm hinj,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hilbertOne_norm_sq]
  ring

end
end RiemannResearch.RH.Pareto
