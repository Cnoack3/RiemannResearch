import RiemannResearch.RH.ArgumentDoublingGenerators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel

/-!
# Odd-carry jumps, exact finite Mellin sums, and decay

Source: user-provided RH_DPP_Odd_Carry_Lean_2026-09-20(1).md and
RH_Doubling_Generators_and_Hurwitz_Obstruction_2026-09-20(1).md,
Sections 2 and 4, for the carry formula and Mellin proof strategy.
The finite telescope retains its terminal boundary term.
The adjacent-even approximation follows from the established even-generator
identity. Its surviving coordinate gives a bound for this particular
approximation, not for the optimum over the closed residue span.
Odd-carry membership and the resulting unconditional RH proof remain open.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- Exact jump formula. It also holds for every even modulus at least two. -/
theorem doublingCarry_succ_sub (d n : ℕ) (hd : 2 ≤ d) :
    doublingCarry d (n + 1) - doublingCarry d n =
      (if (n + 1) % d = (d + 1) / 2 then (1 : ℝ) else 0) -
      (if (n + 1) % d = 0 then (1 : ℝ) else 0) := by
  have hr : n % d < d := Nat.mod_lt n (by omega)
  have hm : (n + 1) % d = (n % d + 1) % d := by
    simpa only [Nat.mod_eq_of_lt (show 1 < d by omega)] using Nat.add_mod n 1 d
  by_cases hw : n % d + 1 = d
  · have hnext : (n + 1) % d = 0 := by
      rw [hm, hw, Nat.mod_self]
    simp only [doublingCarry, hnext]
    split_ifs <;> norm_num <;> omega
  · have hnext : (n + 1) % d = n % d + 1 := by
      rw [hm, Nat.mod_eq_of_lt (show n % d + 1 < d by omega)]
    simp only [doublingCarry, hnext]
    split_ifs <;> norm_num <;> omega

/-- Summation by parts for the actual carry. No infinite series is split,
and the boundary at the finite truncation is retained. -/
theorem doublingCarry_finite_mellin_telescope
    (d N : ℕ) (hd : 2 ≤ d) (z : ℕ → ℂ) :
    (∑ n ∈ Finset.range N,
      (doublingCarry d (n + 1) : ℂ) * (z (n + 1) - z (n + 2))) =
    (∑ n ∈ Finset.range N,
      ((if (n + 1) % d = (d + 1) / 2 then (1 : ℂ) else 0) -
        (if (n + 1) % d = 0 then (1 : ℂ) else 0)) * z (n + 1)) -
      (doublingCarry d N : ℂ) * z (N + 1) := by
  induction N with
  | zero =>
      simp [doublingCarry, show ¬ d ≤ 0 by omega]
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hstep : (doublingCarry d (N + 1) : ℂ) - (doublingCarry d N : ℂ) =
          (if (N + 1) % d = (d + 1) / 2 then (1 : ℂ) else 0) -
          (if (N + 1) % d = 0 then (1 : ℂ) else 0) := by
        have h := congrArg (fun r : ℝ => (r : ℂ)) (doublingCarry_succ_sub d N hd)
        split_ifs at h ⊢ <;>
          simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_zero] using h
      linear_combination z (N + 1) * hstep

/-- The precise finite identity underlying the proposed Hurwitz formula.
It is valid before making any convergence or analytic-continuation argument. -/
theorem doublingCarry_finite_cpow_telescope
    (d N : ℕ) (hd : 2 ≤ d) (s : ℂ) :
    (∑ n ∈ Finset.range N,
      (doublingCarry d (n + 1) : ℂ) *
        (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))) =
    (∑ n ∈ Finset.range N,
      ((if (n + 1) % d = (d + 1) / 2 then (1 : ℂ) else 0) -
        (if (n + 1) % d = 0 then (1 : ℂ) else 0)) *
          ((n + 1 : ℕ) : ℂ) ^ (-s)) -
      (doublingCarry d N : ℂ) * ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  exact doublingCarry_finite_mellin_telescope d N hd (fun n => (n : ℂ) ^ (-s))

/-- The carries tend to zero in the actual Hilbert norm without assuming RH.
This is not a closed-span membership theorem. -/
theorem doublingCarryHilbert_tendsto_zero :
    Tendsto (fun k : ℕ => doublingCarryHilbert (k + 1) (by omega))
      atTop (𝓝 (0 : ThresholdHilbert)) := by
  let v : ℕ → ThresholdHilbert := fun k =>
    hilbertOne - doublingCarryHilbert (k + 1) (by omega)
  have hseq (k n : ℕ) :
      hilbertSequence (v k) n =
        hilbertSequence hilbertOne n - doublingCarry (k + 1) n := by
    change (hilbertSequenceLinear (hilbertOne -
      doublingCarryHilbert (k + 1) (by omega))) n = _
    rw [map_sub]
    change hilbertSequence hilbertOne n -
      hilbertSequence (doublingCarryHilbert (k + 1) (by omega)) n = _
    rw [doublingCarryHilbert_sequence]
  have hb (k n : ℕ) :
      0 ≤ hilbertSequence (v k) n ∧ hilbertSequence (v k) n ≤ 1 := by
    rw [hseq]
    cases n with
    | zero => simp [doublingCarry]
    | succ n =>
        have h1 : hilbertSequence hilbertOne (n + 1) = 1 := by
          rw [hilbertOne_sequence]
          simp [zeroAnchor]
        rw [h1]
        have hc : 0 ≤ doublingCarry (k + 1) (n + 1) ∧
            doublingCarry (k + 1) (n + 1) ≤ 1 := by
          unfold doublingCarry
          split_ifs <;> norm_num
        constructor <;> linarith
  have hp (n : ℕ) (hn : 0 < n) :
      Tendsto (fun k => hilbertSequence (v k) n) atTop (𝓝 1) := by
    have he : (fun k => hilbertSequence (v k) n) =ᶠ[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (2 * n)] with k hk
      rw [hseq]
      have hc : doublingCarry (k + 1) n = 0 := by
        simp [doublingCarry, Nat.mod_eq_of_lt (show n < k + 1 by omega),
          show ¬ k + 1 ≤ 2 * n by omega]
      rw [hc, sub_zero, hilbertOne_sequence]
      simp [zeroAnchor, Nat.ne_of_gt hn]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  have hv : Tendsto v atTop (𝓝 hilbertOne) :=
    hilbert_tendsto_one_of_bounded_coordinates v hb hp
  have h := (tendsto_const_nhds (x := hilbertOne)).sub hv
  simpa only [v, sub_sub_cancel, sub_self] using h

/-- A concrete legal approximation obtained from the adjacent even modulus. -/
def oddCarryAdjacentApprox (m : ℕ) : ThresholdHilbert :=
  (2 : ℝ) • normalizedResidueHilbert (2 * m + 1) (by omega) -
    normalizedResidueHilbert (m + 1) (by omega)

theorem oddCarryAdjacentApprox_mem (m : ℕ) :
    oddCarryAdjacentApprox m ∈ CoefficientStabilization.closedSpace := by
  exact CoefficientStabilization.closedSpace.sub_mem
    (CoefficientStabilization.closedSpace.smul_mem 2
      (CoefficientStabilization.normalizedResidue_mem_closedSpace _ _))
    (CoefficientStabilization.normalizedResidue_mem_closedSpace _ _)

/-- Exact signed error of the adjacent-even approximation. -/
theorem oddCarryAdjacentApprox_error (m : ℕ) :
    doublingCarryHilbert (2 * m + 1) (by omega) - oddCarryAdjacentApprox m =
      argumentDoublingContinuous
        (normalizedResidueHilbert (2 * m + 2) (by omega) -
          normalizedResidueHilbert (2 * m + 1) (by omega)) := by
  rw [map_sub]
  simp only [argumentDoublingContinuous_apply]
  have he : hilbertArgumentDoubling (normalizedResidueHilbert (2 * m + 2) (by omega)) =
      normalizedResidueHilbert (m + 1) (by omega) := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      hilbertArgumentDoubling_residue_even (m + 1) (by omega)
  rw [he, hilbertArgumentDoubling_residue]
  unfold oddCarryAdjacentApprox
  abel

theorem oddCarryAdjacentApprox_error_norm_le (m : ℕ) :
    ‖doublingCarryHilbert (2 * m + 1) (by omega) - oddCarryAdjacentApprox m‖ ≤
      2 * ‖normalizedResidueHilbert (2 * m + 2) (by omega) -
        normalizedResidueHilbert (2 * m + 1) (by omega)‖ := by
  rw [oddCarryAdjacentApprox_error, argumentDoublingContinuous_apply]
  exact hilbertArgumentDoubling_norm_le _

/-- The surviving error at physical coordinate 2*m+1 is explicit. -/
theorem oddCarryAdjacentApprox_error_coordinate (m : ℕ) :
    hilbertSequence
      (doublingCarryHilbert (2 * m + 1) (by omega) - oddCarryAdjacentApprox m)
      (2 * m + 1) = (m : ℝ) / ((m : ℝ) + 1) := by
  rw [oddCarryAdjacentApprox_error, argumentDoublingContinuous_apply,
    hilbertArgumentDoubling_sequence]
  change hilbertSequenceLinear
    (normalizedResidueHilbert (2 * m + 2) (by omega) -
      normalizedResidueHilbert (2 * m + 1) (by omega)) (2 * (2 * m + 1)) = _
  rw [map_sub]
  change hilbertSequence (normalizedResidueHilbert (2 * m + 2) (by omega))
      (2 * (2 * m + 1)) -
    hilbertSequence (normalizedResidueHilbert (2 * m + 1) (by omega))
      (2 * (2 * m + 1)) = _
  rw [normalizedResidueHilbert_sequence, normalizedResidueHilbert_sequence]
  have hzero : (2 * (2 * m + 1)) % (2 * m + 1) = 0 := by
    simp
  have hrem : (2 * (2 * m + 1)) % (2 * m + 2) = 2 * m := by
    rw [show 2 * (2 * m + 1) = (2 * m + 2) + 2 * m by omega]
    simp [Nat.mod_eq_of_lt (show 2 * m < 2 * m + 2 by omega)]
  simp only [residueFraction, hzero, hrem, Nat.cast_zero, zero_div, sub_zero,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- A positive full-norm lower bound for this particular legal approximation.
It does not lower-bound the optimum over all legal approximations. -/
theorem oddCarryAdjacentApprox_error_sq_lower_bound (m : ℕ) :
    positiveWeight (2 * m + 1) * ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 ≤
      ‖doublingCarryHilbert (2 * m + 1) (by omega) - oddCarryAdjacentApprox m‖ ^ 2 := by
  let f := doublingCarryHilbert (2 * m + 1) (by omega) - oddCarryAdjacentApprox m
  have h := (hilbertSequence_square_summable f).sum_le_tsum
    ({2 * m + 1} : Finset ℕ)
    (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
  simpa only [Finset.sum_singleton, f, oddCarryAdjacentApprox_error_coordinate,
    ← hilbert_norm_weighted_sq] using h

end RiemannResearch.RH.Pareto
