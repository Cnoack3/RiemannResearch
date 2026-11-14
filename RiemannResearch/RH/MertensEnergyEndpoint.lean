/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MertensWeightedEnergy
import RiemannResearch.RH.MertensEnergyConvergence
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensAllLogPowers
import RiemannResearch.Analysis.LogPowerSummability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional endpoint and logarithmic Mertens-energy moments

Source: the user's weighted-energy research agenda. This assembly uses the
repository's proved M_shiftedLog_all_nat_powers provider and elementary
logarithmic p-series comparison. For classical context, see K. Soundararajan,
Partial sums of the Mobius function, introduction, arXiv:0705.0723.
The reference supplies context only; all arithmetic and summability inputs
used here are proved Lean declarations.

For every fixed natural a, both sum |M(n)|(6+log n)^a/n^2 and
sum M(n)^2(6+log n)^a/n^3 are finite. Thus HasFiniteEnergy holds at epsilon=1 / 2
and above. No conclusion for every positive epsilon, no uniform constant in a,
and no RH conclusion follows from this endpoint alone.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.MertensWeightedEnergy
open RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem mertensPrefix_eq_M_nat (N : ℕ) : mertensPrefix N = M (N : ℝ) := by
  rw [mertensPrefix_eq_mobius_sum]
  rw [M, Nat.floor_natCast]
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Iic.mpr (Finset.mem_Icc.mp hn).2
  · intro n hn hnot
    have hzero : n = 0 := by
      simp only [Finset.mem_Iic, Finset.mem_Icc] at hn hnot
      omega
    simp [hzero]

/-- Every fixed logarithmic moment at the unconditional absolute first-moment endpoint. -/
theorem summable_absolute_mertens_log_moment (a : ℕ) :
    Summable (fun n : ℕ =>
      |mertensPrefix (n+1)| * (6 + Real.log ((n : ℝ)+1))^a / ((n : ℝ)+1)^2) := by
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_all_nat_powers (a+2)
  have hs : Summable (fun n : ℕ =>
      B / (((n : ℝ)+1) * Real.log (2 * ((n : ℝ)+1))^2)) := by
    have ht := ((summable_nat_add_iff 1).mpr
      (RiemannResearch.Analysis.summable_log_power_majorant
        (p := 2) (by norm_num))).mul_left B
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two, mul_one_div] using ht
  have hL0 (n : ℕ) : 0 ≤ 6 + Real.log ((n : ℝ)+1) := by
    have hl := Real.log_nonneg (show 1 ≤ (n : ℝ)+1 by
      linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  apply Summable.of_nonneg_of_le (fun n => div_nonneg
    (mul_nonneg (abs_nonneg _) (pow_nonneg (hL0 n) a)) (sq_nonneg _)) _ hs
  intro n
  let x : ℝ := (n : ℝ)+1
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hx : 0 < x := by linarith
  have hL : 0 ≤ 6 + Real.log x := by linarith [Real.log_nonneg hx1]
  have hlog : 0 < Real.log (2*x) := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogL : Real.log (2*x) ≤ 6 + Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne']
    linarith
  have hlogSq : Real.log (2*x)^2 ≤ (6 + Real.log x)^2 :=
    (sq_le_sq₀ hlog.le hL).mpr hlogL
  have hMb : |mertensPrefix (n+1)| * (6 + Real.log x)^(a+2) ≤ B*x := by
    simpa only [mertensPrefix_eq_M_nat, Nat.cast_add, Nat.cast_one, x] using hM x hx1
  have hm : |mertensPrefix (n+1)| * (6 + Real.log x)^a *
      Real.log (2*x)^2 ≤ B*x := by
    calc
      _ ≤ |mertensPrefix (n+1)| * (6 + Real.log x)^a * (6 + Real.log x)^2 :=
        mul_le_mul_of_nonneg_left hlogSq (by positivity)
      _ ≤ B*x := by simpa only [pow_add, mul_assoc] using hMb
  change |mertensPrefix (n+1)| * (6 + Real.log x)^a / x^2 ≤
    B / (x * Real.log (2*x)^2)
  apply (div_le_div_iff₀ (sq_pos_of_pos hx)
    (mul_pos hx (sq_pos_of_pos hlog))).mpr
  nlinarith [mul_le_mul_of_nonneg_right hm hx.le]

/-- Every fixed logarithmic moment of M(n)^2/n^3 is finite unconditionally. -/
theorem summable_mertens_endpoint_log_energy (a : ℕ) :
    Summable (fun n : ℕ =>
      mertensPrefix (n+1)^2 * (6 + Real.log ((n : ℝ)+1))^a / ((n : ℝ)+1)^3) := by
  have hL0 (n : ℕ) : 0 ≤ 6 + Real.log ((n : ℝ)+1) := by
    have hl := Real.log_nonneg (show 1 ≤ (n : ℝ)+1 by
      linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  apply Summable.of_nonneg_of_le (fun n => div_nonneg
    (mul_nonneg (sq_nonneg _) (pow_nonneg (hL0 n) a)) (by positivity)) _
    (summable_absolute_mertens_log_moment a)
  intro n
  have hx : 0 < (n : ℝ)+1 := by positivity
  have hL : 0 ≤ 6 + Real.log ((n : ℝ)+1) := by
    have hl := Real.log_nonneg (show 1 ≤ (n : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hM : |mertensPrefix (n+1)| ≤ (n : ℝ)+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using mertensPrefix_abs_le (n+1)
  have hm : mertensPrefix (n+1)^2 ≤ |mertensPrefix (n+1)| * ((n : ℝ)+1) := by
    simpa only [← pow_two, sq_abs] using
      mul_le_mul_of_nonneg_left hM (abs_nonneg (mertensPrefix (n+1)))
  apply (div_le_div_iff₀ (pow_pos hx 3) (pow_pos hx 2)).mpr
  have ht := mul_le_mul_of_nonneg_right hm
    (mul_nonneg (pow_nonneg hL a) (pow_nonneg hx.le 2))
  nlinarith only [ht]

theorem hasFiniteEnergy_half : HasFiniteEnergy (1 / 2) := by
  have h := summable_mertens_endpoint_log_energy 0
  apply h.congr
  intro n
  simp only [weight, pow_zero, mul_one]
  rw [show (-2 - 2 * (1 / 2 : ℝ)) = -(3 : ℝ) by norm_num,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ)+1), Real.rpow_ofNat]
  ring

theorem hasFiniteEnergy_of_half_le {ε : ℝ} (hε : 1 / 2 ≤ ε) : HasFiniteEnergy ε :=
  hasFiniteEnergy_mono hε hasFiniteEnergy_half

/-- The signed limit is supplied unconditionally at and above the endpoint. -/
theorem offDiagonal_converges_of_half_le {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    ∃ L : ℝ, Tendsto (offDiagonal ε) atTop (𝓝 L) :=
  (hasFiniteEnergy_iff_offDiagonal_converges ε (by linarith)).mp
    (hasFiniteEnergy_of_half_le hε)

#print axioms hasFiniteEnergy_half
#print axioms summable_mertens_endpoint_log_energy
end RiemannResearch.RH.MertensWeightedEnergy
