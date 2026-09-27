/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorHyperbolaBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite hyperbola cutoffs for stretched profiles

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Integer cutoff retaining a stretched exponential saving.  The exponent
is preserved; only its positive coefficient is reduced. -/
theorem stretched_hyperbola_cutoff
    {β d : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    {N : ℕ} (hN : 0 < N) (hlarge : 10 ≤ Real.log (N : ℝ)) :
    ∃ y : ℕ, 0 < y ∧ y ≤ N ∧
      ((N : ℝ) * Real.exp (-(d / 2) * (6 + Real.log (N : ℝ)) ^ β)) / 2 ≤ (y : ℝ) ∧
      (y : ℝ) ≤ (N : ℝ) * Real.exp (-(d / 2) * (6 + Real.log (N : ℝ)) ^ β) ∧
      (6 + Real.log (N : ℝ)) / 2 ≤ 6 + Real.log (y : ℝ) := by
  let L : ℝ := 6 + Real.log (N : ℝ)
  let x : ℝ := (N : ℝ) * Real.exp (-(d / 2) * L ^ β)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL16 : 16 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hLpow : L ^ β ≤ L := Real.rpow_le_self_of_one_le (by linarith) hβ1
  have hsmall : (d / 2) * L ^ β ≤ L / 8 := by
    have h1 := mul_le_mul_of_nonneg_left hLpow hd.le
    have h2 := mul_le_mul_of_nonneg_right hd4 hL.le
    nlinarith
  have hx : 0 < x := by dsimp [x]; positivity
  have hlogx : Real.log x = Real.log (N : ℝ) - (d / 2) * L ^ β := by
    dsimp [x]
    rw [Real.log_mul hNR.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hx2 : 2 ≤ x := by
    apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2) hx).mp
    rw [hlogx]
    have hNL : Real.log (N : ℝ) = L - 6 := by dsimp [L]; ring
    rw [hNL]
    linarith
  let y : ℕ := Nat.floor x
  have hyhi : (y : ℝ) ≤ x := Nat.floor_le hx.le
  have hylo : x / 2 ≤ (y : ℝ) := by
    have hh : x < (y : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  have hyR : (0 : ℝ) < y := (div_pos hx (by norm_num)).trans_le hylo
  have hy : 0 < y := by exact_mod_cast hyR
  have hxN : x ≤ (N : ℝ) := by
    apply mul_le_of_le_one_right hNR.le
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg hL.le _)
  have hyN : y ≤ N := by exact_mod_cast hyhi.trans hxN
  have hlogy : L / 2 ≤ 6 + Real.log (y : ℝ) := by
    have hh := Real.log_le_log (div_pos hx (by norm_num)) hylo
    rw [Real.log_div hx.ne' (by norm_num), hlogx] at hh
    have hNL : Real.log (N : ℝ) = L - 6 := by dsimp [L]; ring
    rw [hNL] at hh
    linarith
  exact ⟨y, hy, hyN, by simpa [x, L] using hylo,
    by simpa [x, L] using hyhi, by simpa [L] using hlogy⟩

/-- Scalar balanced hyperbola bound.  The negative exponential is retained
before squaring and the cutoff is rounded only by a fixed factor. -/
theorem hyperbola_stretched_scalar_bound {n y e f W E : ℝ}
    (hn : 0 < n) (hy : 0 < y) (he : 0 < e)
    (hf0 : 0 ≤ f) (hW : 0 ≤ W) (hE : 0 ≤ E)
    (hylo : n * e ^ 2 / 2 ≤ y) (hyhi : y ≤ n * e ^ 2)
    (hf : f ≤ e ^ 2) :
    2 * W * Real.sqrt y + E * n / Real.sqrt y * f ≤
      (2 * W + 2 * E) * Real.sqrt n * e := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsy2 := Real.sq_sqrt hy.le
  have hsn2 := Real.sq_sqrt hn.le
  have hhead : Real.sqrt y ≤ Real.sqrt n * e := by
    have hsq : (Real.sqrt y) ^ 2 ≤ (Real.sqrt n * e) ^ 2 := by
      rw [mul_pow, hsy2, hsn2]
      exact hyhi
    exact (sq_le_sq₀ (Real.sqrt_nonneg y)
      (mul_nonneg (Real.sqrt_nonneg n) he.le)).mp hsq
  have hlower : Real.sqrt n * e ≤ 2 * Real.sqrt y := by
    have hsq : (Real.sqrt n * e) ^ 2 ≤ (2 * Real.sqrt y) ^ 2 := by
      rw [mul_pow, mul_pow, hsn2, hsy2]
      nlinarith
    exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg n) he.le)
      (by positivity : 0 ≤ 2 * Real.sqrt y)).mp hsq
  have htail : n / Real.sqrt y * f ≤ 2 * Real.sqrt n * e := by
    calc
      _ ≤ n / Real.sqrt y * e ^ 2 :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (n * e ^ 2) / Real.sqrt y := by ring
      _ ≤ 2 * Real.sqrt n * e := by
        apply (div_le_iff₀ hsy).mpr
        have hh := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ Real.sqrt n * e)
        rw [← sq, mul_pow, hsn2] at hh
        nlinarith
  calc
    _ ≤ 2 * W * (Real.sqrt n * e) + E * (2 * Real.sqrt n * e) := by
      have hh := mul_le_mul_of_nonneg_left hhead (by positivity : 0 ≤ 2 * W)
      have ht := mul_le_mul_of_nonneg_left htail hE
      simpa only [mul_div_assoc, mul_assoc] using add_le_add hh ht
    _ = _ := by ring

/-- The square-root hyperbola method preserves every stretched-log exponent
in (0,1], with explicit coefficient loss d to d/4. -/
theorem arithmeticFloorPrefix_stretched_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    {W B D β d : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hw : ∀ t : ℕ, 0 < t → |w t| ≤ W / Real.sqrt (t : ℝ))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * Real.sqrt (t : ℝ) * Real.exp (-d * (6 + Real.log (t : ℝ)) ^ β))
    (hT : ∀ t : ℕ, 0 < t →
      |C - ∑ t' ∈ Finset.range (t + 1), w t' / (t' : ℝ)| ≤
        D / Real.sqrt (t : ℝ) * Real.exp (-d * (6 + Real.log (t : ℝ)) ^ β))
    {N : ℕ} (hN : 0 < N) (hlarge : 10 ≤ Real.log (N : ℝ)) :
    |arithmeticFloorPrefix w N - (N : ℝ) * C| ≤
      (2 * W + 6 * B + 2 * D) * Real.sqrt (N : ℝ) *
        Real.exp (-(d / 4) * (6 + Real.log (N : ℝ)) ^ β) := by
  obtain ⟨y, hy, hyN, hylo, hyhi, hlog⟩ :=
    stretched_hyperbola_cutoff hβ hβ1 hd hd4 hN hlarge
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  let L : ℝ := 6 + Real.log (N : ℝ)
  let J : ℝ := 6 + Real.log (y : ℝ)
  have hL : 0 < L := by dsimp [L]; linarith
  have hJ : 0 < J := by dsimp [J]; linarith [Real.log_nonneg hy1]
  let Q : ℝ := Real.exp (d * J ^ β)
  have hQ : 0 < Q := Real.exp_pos _
  have he (t : ℝ) : Real.exp (-d * t ^ β) = (Real.exp (d * t ^ β))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have hp : ∀ t : ℕ, y ≤ t → |positiveArithmeticPrefix w t| ≤
      B * Real.sqrt (t : ℝ) / Q := by
    intro t hyt
    have ht : 0 < t := hy.trans_le hyt
    have hjt : J ≤ 6 + Real.log (t : ℝ) := by
      dsimp [J]
      linarith [Real.log_le_log hy0 (show (y : ℝ) ≤ t by exact_mod_cast hyt)]
    have hs : Real.exp (-d * (6 + Real.log (t : ℝ)) ^ β) ≤ Real.exp (-d * J ^ β) := by
      apply Real.exp_le_exp.mpr
      have hpow := Real.rpow_le_rpow hJ.le hjt hβ.le
      nlinarith
    calc
      _ ≤ B * Real.sqrt (t : ℝ) * Real.exp (-d * (6 + Real.log (t : ℝ)) ^ β) := hP t ht
      _ ≤ B * Real.sqrt (t : ℝ) * Real.exp (-d * J ^ β) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [he]; rfl
  have ht : |C - ∑ t ∈ Finset.range (y + 1), w t / (t : ℝ)| ≤
      D / (Real.sqrt (y : ℝ) * Q) := by
    have h := hT y hy
    rw [he] at h
    simpa only [Q, J, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h
  have hbound := arithmeticFloorPrefix_centered_hyperbola_bound
    w hw0 C hy hyN hW hB hD hQ hw hp ht
  let e : ℝ := Real.exp (-(d / 4) * L ^ β)
  let f : ℝ := Real.exp (-d * J ^ β)
  have he2 : e ^ 2 = Real.exp (-(d / 2) * L ^ β) := by
    dsimp [e]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hJpow : L ^ β / 2 ≤ J ^ β := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ L / 2) hlog hβ.le
    rw [Real.div_rpow hL.le (by norm_num)] at h
    have htwo : (2 : ℝ) ^ β ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hβ1
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hL.le _)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) β) htwo).trans h
  have hf : f ≤ e ^ 2 := by
    rw [he2]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hs := hyperbola_stretched_scalar_bound (e := e) (f := f)
    hn0 hy0 (Real.exp_pos _) (Real.exp_nonneg _)
    hW (show 0 ≤ 3 * B + D by positivity)
    (by rw [he2]; exact hylo) (by rw [he2]; exact hyhi) hf
  have hb' : |arithmeticFloorPrefix w N - (N : ℝ) * C| ≤
      2 * W * Real.sqrt (y : ℝ) + (3 * B + D) * (N : ℝ) / Real.sqrt (y : ℝ) * f := by
    simpa only [Q, f, he, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hbound
  apply hb'.trans
  calc
    _ ≤ (2 * W + 2 * (3 * B + D)) * Real.sqrt (N : ℝ) * e := hs
    _ = _ := by dsimp [e, L]; ring

end RiemannResearch.RH.Pareto
