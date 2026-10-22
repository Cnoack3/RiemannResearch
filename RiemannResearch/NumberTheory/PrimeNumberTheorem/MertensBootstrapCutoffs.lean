/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
The elementary scalar optimization in the Mertens log-power bootstrap.
The arithmetic inequality is supplied separately.  The hypotheses record
coarse consequences of the cutoffs Y=floor(N exp(-sqrt(log N))) and
J=floor(sqrt(log N))+1; no asymptotic estimate is assumed by this lemma.
-/
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- A finite scalar optimization of the Mertens bootstrap inequality. -/
theorem mertens_bootstrap_scalar
    {q r Y J A C D t L H B : ℝ}
    (ht : 1 ≤ t) (hY : 1 ≤ Y) (hJ : t ≤ J)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hr : r * t ≤ 1) (hAC : A * t ^ 2 ≤ 2 * C)
    (hH : H + 1 ≤ 4 * t) (hL : t ≤ 1 + L)
    (hB : L + B ≤ 9 * t)
    (hq : q ≤ r + A + 1 / J + 1 / (Y * J) + A * (H + 1) +
      3 * D / (1 + L) ^ 2 + 2 * A * (L + B)) :
    q * t ≤ 3 + 46 * C + 3 * D := by
  have ht0 : 0 < t := by linarith
  have htN : 0 ≤ t := le_of_lt ht0
  have hJ0 : 0 < J := lt_of_lt_of_le ht0 hJ
  have hYJ0 : 0 < Y * J := mul_pos (by linarith) hJ0
  have ht2 : t ≤ t ^ 2 := by
    nlinarith [mul_nonneg htN (sub_nonneg.mpr ht)]
  have hAt : A * t ≤ 2 * C :=
    (mul_le_mul_of_nonneg_left ht2 hA).trans hAC
  have hJt : (1 / J) * t ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hJ0).2
    simpa only [one_mul] using hJ
  have hYJ : t ≤ Y * J := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hY) (le_of_lt hJ0)]
  have hYJt : (1 / (Y * J)) * t ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hYJ0).2
    simpa only [one_mul] using hYJ
  have hAH : A * (H + 1) * t ≤ 8 * C := by
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hH hA) htN
    nlinarith [hAC]
  have hLp : 0 < 1 + L := lt_of_lt_of_le ht0 hL
  have hden0 : 0 < (1 + L) ^ 2 := by positivity
  have hden : t ≤ (1 + L) ^ 2 := by nlinarith
  have hDt : (3 * D / (1 + L) ^ 2) * t ≤ 3 * D := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden0).2
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hAB : 2 * A * (L + B) * t ≤ 36 * C := by
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB hA) htN
    nlinarith [hAC]
  have hqt := mul_le_mul_of_nonneg_right hq htN
  nlinarith


/-- Unnormalized form, matching the finite arithmetic Mertens inequality. -/
theorem mertens_bootstrap_scalar_unscaled
    {X N Y J A C D t L H B : ℝ}
    (hN : 0 < N) (ht : 1 ≤ t) (hY : 1 ≤ Y) (hJ : t ≤ J)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hYt : Y * t ≤ N) (hAC : A * t ^ 2 ≤ 2 * C)
    (hH : H + 1 ≤ 4 * t) (hL : t ≤ 1 + L)
    (hB : L + B ≤ 9 * t)
    (hX : X * t ^ 2 ≤ Y + A * N +
      N * (1 / J + 1 / (Y * J) + A * (H + 1)) +
      3 * D * N / (1 + L) ^ 2 + 2 * A * N * (L + B)) :
    X * t ^ 3 ≤ (3 + 46 * C + 3 * D) * N := by
  have hr : (Y / N) * t ≤ 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN).2 (by simpa using hYt)
  have hq : X * t ^ 2 / N ≤ Y / N + A + 1 / J + 1 / (Y * J) +
      A * (H + 1) + 3 * D / (1 + L) ^ 2 + 2 * A * (L + B) := by
    apply (div_le_iff₀ hN).2
    have he : (Y / N + A + 1 / J + 1 / (Y * J) +
        A * (H + 1) + 3 * D / (1 + L) ^ 2 + 2 * A * (L + B)) * N =
        Y + A * N + N * (1 / J + 1 / (Y * J) + A * (H + 1)) +
        3 * D * N / (1 + L) ^ 2 + 2 * A * N * (L + B) := by
      have hc := div_mul_cancel₀ Y hN.ne'
      simp only [div_eq_mul_inv] at hc ⊢
      nlinarith only [hc]
    rw [he]
    exact hX
  have h := mertens_bootstrap_scalar ht hY hJ hA hD hr hAC hH hL hB hq
  have hdiv : X * t ^ 3 / N ≤ 3 + 46 * C + 3 * D := by
    convert h using 1 <;> ring
  exact (div_le_iff₀ hN).mp hdiv

end RiemannResearch.NumberTheory.PrimeNumberTheorem

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Fully explicit finite cutoffs for the logarithmic Mertens bootstrap.
The parameter `t` is subsequently taken to be `sqrt(log N)`. -/
theorem exists_mertens_bootstrap_cutoffs (N : ℕ) (t : ℝ)
    (hN : 0 < N) (ht : 4 ≤ t) (hlog : Real.log (N : ℝ) = t ^ 2) :
    ∃ Y J : ℕ, 0 < Y ∧ Y ≤ N ∧ 0 < J ∧
      t ≤ (Y : ℝ) ∧ (Y : ℝ) * t ≤ N ∧
      t ≤ (J : ℝ) ∧ (J : ℝ) ≤ t + 1 ∧
      t ^ 2 / 2 ≤ Real.log (Y : ℝ) ∧
      t ≤ Real.log ((N : ℝ) / Y) ∧
      Real.log ((N : ℝ) / Y) + Real.log 4 + 5 ≤ 9 * t := by
  let z : ℝ := Real.exp (t ^ 2 - t)
  let Y : ℕ := ⌊z⌋₊
  let J : ℕ := ⌊t⌋₊ + 1
  have ht0 : 0 < t := by linarith
  have htlarge : 4 * t ≤ t ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr ht)]
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hz0 : 0 < z := Real.exp_pos _
  have hz2 : 2 ≤ z := by
    have he := Real.add_one_le_exp (t ^ 2 - t)
    dsimp [z]
    nlinarith
  have hYupper : (Y : ℝ) ≤ z := Nat.floor_le (le_of_lt hz0)
  have hYlower : z - 1 < (Y : ℝ) := by
    have he := Nat.lt_floor_add_one z
    dsimp [Y]
    linarith
  have hYhalf : z / 2 ≤ (Y : ℝ) := by linarith
  have htY : t ≤ (Y : ℝ) := by
    have he := Real.add_one_le_exp (t ^ 2 - t)
    change t ^ 2 - t + 1 ≤ z at he
    nlinarith
  have hY0R : 0 < (Y : ℝ) := lt_of_lt_of_le ht0 htY
  have hY0 : 0 < Y := by exact_mod_cast hY0R
  have hNexp : Real.exp (t ^ 2) = (N : ℝ) := by
    rw [← hlog, Real.exp_log hN0]
  have hexpt : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hYt : (Y : ℝ) * t ≤ N := by
    calc
      (Y : ℝ) * t ≤ z * t := mul_le_mul_of_nonneg_right hYupper (le_of_lt ht0)
      _ ≤ z * Real.exp t := mul_le_mul_of_nonneg_left hexpt (le_of_lt hz0)
      _ = Real.exp (t ^ 2) := by
        dsimp [z]
        rw [← Real.exp_add]
        congr 1
        ring
      _ = N := hNexp
  have hYN : Y ≤ N := by
    have hy : (Y : ℝ) ≤ (N : ℝ) := by
      nlinarith [mul_nonneg (le_of_lt hY0R) (show 0 ≤ t - 1 by linarith)]
    exact_mod_cast hy
  have hJlower : t ≤ (J : ℝ) := by
    have he := Nat.lt_floor_add_one t
    simpa [J, Nat.cast_add, Nat.cast_one] using le_of_lt he
  have hJupper : (J : ℝ) ≤ t + 1 := by
    have he := Nat.floor_le (le_of_lt ht0)
    dsimp [J]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hJ0 : 0 < J := by
    have hj : 0 < (J : ℝ) := lt_of_lt_of_le ht0 hJlower
    exact_mod_cast hj
  have hlogYupper : Real.log (Y : ℝ) ≤ t ^ 2 - t := by
    have he := Real.log_le_log hY0R hYupper
    simpa [z, Real.log_exp] using he
  have hlogYlower : t ^ 2 - t - Real.log 2 ≤ Real.log (Y : ℝ) := by
    have he := Real.log_le_log (by positivity : 0 < z / 2) hYhalf
    simpa [Real.log_div hz0.ne' (by norm_num : (2 : ℝ) ≠ 0), z, Real.log_exp] using he
  have hlog2 : Real.log 2 ≤ 1 := by
    have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at he ⊢
    exact he
  have hlog4 : Real.log 4 ≤ 3 := by
    have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at he ⊢
    exact he
  have hlogY : t ^ 2 / 2 ≤ Real.log (Y : ℝ) := by nlinarith
  have hlogdiv : Real.log ((N : ℝ) / Y) = t ^ 2 - Real.log (Y : ℝ) := by
    rw [Real.log_div hN0.ne' hY0R.ne', hlog]
  refine ⟨Y, J, hY0, hYN, hJ0, htY, hYt, hJlower, hJupper, hlogY, ?_, ?_⟩
  · rw [hlogdiv]
    linarith
  · rw [hlogdiv]
    linarith

end RiemannResearch.NumberTheory.PrimeNumberTheorem
