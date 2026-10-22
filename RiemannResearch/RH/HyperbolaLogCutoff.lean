/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorHyperbolaBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
open RiemannResearch.Analysis
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- An explicit cutoff for the endpoint argument.  The deliberately large
threshold makes the logarithmic comparison elementary and quantitative. -/
theorem logarithmic_hyperbola_cutoff {N : ℕ} (hN : 0 < N)
    (hlarge : 200 ≤ Real.log (N : ℝ)) :
    ∃ y : ℕ, 0 < y ∧ y ≤ N ∧
      (N : ℝ) / (4 * (6 + Real.log (N : ℝ)) ^ (3/2 : ℝ)) ≤ (y : ℝ) ∧
      (y : ℝ) ≤ (N : ℝ) / (6 + Real.log (N : ℝ)) ^ (3/2 : ℝ) ∧
      (6 + Real.log (N : ℝ))/2 ≤ 6 + Real.log (y : ℝ) := by
  let L : ℝ := 6 + Real.log (N : ℝ)
  let U : ℝ := L ^ (3/2 : ℝ)
  let x : ℝ := (N : ℝ) / U
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLlarge : 206 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hU : 0 < U := Real.rpow_pos_of_pos hL _
  have hx : 0 < x := div_pos hNR hU
  have hsq := Real.sq_sqrt hL.le
  have hs0 := Real.sqrt_nonneg L
  have hs12 : 12 ≤ Real.sqrt L := by nlinarith
  have hlogL : Real.log L ≤ 2 * Real.sqrt L := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hL)
    have he : Real.log (Real.sqrt L) = (1/2 : ℝ) * Real.log L := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow hL]
    rw [he] at hh
    nlinarith
  have hsquarter : 3 * Real.sqrt L ≤ L / 4 := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs12)]
  have hlogquarter : (3/2 : ℝ) * Real.log L ≤ L/4 := by linarith
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at he
    exact he
  have hlogx : Real.log x = Real.log (N : ℝ) - (3/2 : ℝ)*Real.log L := by
    dsimp [x, U]
    rw [Real.log_div (ne_of_gt hNR) (ne_of_gt (Real.rpow_pos_of_pos hL _)),
      Real.log_rpow hL]
  have hx2 : 2 ≤ x := by
    apply (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2) hx).mp
    rw [hlogx]
    have hNL : Real.log (N : ℝ) = L - 6 := by dsimp [L]; ring
    rw [hNL]
    linarith
  let y : ℕ := Nat.floor x
  have hy_upper : (y : ℝ) ≤ x := Nat.floor_le hx.le
  have hy_lower : x/2 ≤ (y : ℝ) := by
    have hh : x < (y : ℝ)+1 := Nat.lt_floor_add_one x
    linarith
  have hyR : (0 : ℝ) < y := lt_of_lt_of_le (div_pos hx (by norm_num)) hy_lower
  have hy : 0 < y := by exact_mod_cast hyR
  have hUone : 1 ≤ U := by
    dsimp [U]
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (show 1 ≤ L by linarith) (by norm_num : (0 : ℝ) ≤ 3/2)
  have hxN : x ≤ (N : ℝ) := by
    dsimp [x]
    exact div_le_self hNR.le hUone
  have hyN : y ≤ N := by exact_mod_cast hy_upper.trans hxN
  have hy_lower4 : (N : ℝ)/(4*U) ≤ (y : ℝ) := by
    have hxeq : (N : ℝ)/(4*U) = x/4 := by dsimp [x]; ring
    rw [hxeq]
    linarith
  have hlogy : L/2 ≤ 6 + Real.log (y : ℝ) := by
    have hh := Real.log_le_log (div_pos hx (by norm_num)) hy_lower
    rw [Real.log_div (ne_of_gt hx) (by norm_num), hlogx] at hh
    have hNL : Real.log (N : ℝ) = L - 6 := by dsimp [L]; ring
    rw [hNL] at hh
    linarith
  exact ⟨y, hy, hyN, by simpa [U, L] using hy_lower4,
    by simpa [x, U, L] using hy_upper, by simpa [L] using hlogy⟩

private theorem endpoint_power_square {L : ℝ} (hL : 0 ≤ L) :
    (L ^ (3/4 : ℝ)) ^ 2 = L ^ (3/2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num

/-- Scalar optimization of the exact hyperbola bound.  The constant is
kept simple; the logarithmic exponent `3/4` is the substantive endpoint gain. -/
theorem hyperbola_endpoint_scalar_bound {n y L J W E : ℝ}
    (hn : 0 < n) (hy : 0 < y) (hL : 0 < L) (hJ : 0 < J)
    (hW : 0 ≤ W) (hE : 0 ≤ E)
    (hylo : n / (4 * L ^ (3/2 : ℝ)) ≤ y)
    (hyhi : y ≤ n / L ^ (3/2 : ℝ))
    (hJL : L/2 ≤ J) :
    2*W*Real.sqrt y + E*n/(Real.sqrt y * J^(3/2 : ℝ)) ≤
      (2*W+8*E) * Real.sqrt n / L^(3/4 : ℝ) := by
  let u : ℝ := L ^ (3/4 : ℝ)
  let q : ℝ := J ^ (3/2 : ℝ)
  have hu : 0 < u := Real.rpow_pos_of_pos hL _
  have hq : 0 < q := Real.rpow_pos_of_pos hJ _
  have hu2 : u^2 = L^(3/2 : ℝ) := endpoint_power_square hL.le
  have hsyp : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsnp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsy2 := Real.sq_sqrt hy.le
  have hsn2 := Real.sq_sqrt hn.le
  have hhead : Real.sqrt y * u ≤ Real.sqrt n := by
    have hyy : y*u^2 ≤ n := by
      rw [hu2]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hL _)).mp hyhi
    have hp : 0 ≤ Real.sqrt y * u := by positivity
    have hsqbound : (Real.sqrt y * u)^2 ≤ (Real.sqrt n)^2 := by
      rw [mul_pow, hsy2, hsn2]
      exact hyy
    nlinarith
  have hlower : Real.sqrt n ≤ 2*Real.sqrt y*u := by
    have hyy : n ≤ y*(4*u^2) := by
      rw [hu2]
      exact (div_le_iff₀ (by positivity : 0 < 4*L^(3/2 : ℝ))).mp hylo
    have hp : 0 ≤ 2*Real.sqrt y*u := by positivity
    have hsqbound : (Real.sqrt n)^2 ≤ (2*Real.sqrt y*u)^2 := by
      rw [mul_pow, mul_pow, hsy2, hsn2]
      nlinarith
    nlinarith
  have hqcomp : u^2 ≤ 4*q := by
    have hbase := Real.rpow_le_rpow (by positivity : 0 ≤ L/2) hJL
      (by norm_num : (0 : ℝ) ≤ 3/2)
    have htwo : (2 : ℝ) ^ (3/2 : ℝ) ≤ 4 := by
      calc
        _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := by norm_num
    rw [Real.div_rpow hL.le (by norm_num)] at hbase
    have hbase' : L^(3/2 : ℝ) ≤ q * (2 : ℝ)^(3/2 : ℝ) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(3/2 : ℝ))).mp hbase
    rw [hu2]
    nlinarith
  have hdenom : Real.sqrt n*u ≤ 8*Real.sqrt y*q := by
    have ha := mul_le_mul_of_nonneg_right hlower hu.le
    have hb := mul_le_mul_of_nonneg_left hqcomp (by positivity : 0 ≤ 2*Real.sqrt y)
    nlinarith
  have hhead' : Real.sqrt y ≤ Real.sqrt n/u := (le_div_iff₀ hu).mpr hhead
  have htail : n/(Real.sqrt y*q) ≤ 8*Real.sqrt n/u := by
    apply (div_le_iff₀ (mul_pos hsyp hq)).mpr
    have hh := mul_le_mul_of_nonneg_left hdenom hsnp.le
    have heq : Real.sqrt n * (Real.sqrt n*u) = n*u := by
      rw [← mul_assoc, ← sq, hsn2]
    rw [heq] at hh
    have hg : n ≤ (8*Real.sqrt n*(Real.sqrt y*q))/u := by
      apply (le_div_iff₀ hu).mpr
      convert hh using 1 <;> ring
    calc
      n ≤ (8*Real.sqrt n*(Real.sqrt y*q))/u := hg
      _ = (8*Real.sqrt n/u)*(Real.sqrt y*q) := by ring
  change 2*W*Real.sqrt y + E*n/(Real.sqrt y*q) ≤ (2*W+8*E)*Real.sqrt n/u
  calc
    _ ≤ 2*W*(Real.sqrt n/u) + E*(8*Real.sqrt n/u) := by
      have hh := mul_le_mul_of_nonneg_left hhead' (by positivity : 0 ≤ 2*W)
      have ht := mul_le_mul_of_nonneg_left htail hE
      simpa only [mul_div_assoc] using add_le_add hh ht
    _ = _ := by ring

/-- Uniform logarithmic prefix cancellation with exponent `3/2` gives the
summable endpoint discrepancy exponent `3/4`, for arbitrary signed weights. -/
theorem arithmeticFloorPrefix_endpoint_log_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    {W B D : ℝ} (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W / Real.sqrt (d : ℝ))
    (hP : ∀ t : ℕ, 0 < t →
      |positiveArithmeticPrefix w t| ≤
        B * Real.sqrt (t : ℝ) / (6 + Real.log (t : ℝ))^(3/2 : ℝ))
    (hT : ∀ t : ℕ, 0 < t →
      |C - ∑ d ∈ Finset.range (t+1), w d / (d : ℝ)| ≤
        D / (Real.sqrt (t : ℝ) * (6 + Real.log (t : ℝ))^(3/2 : ℝ)))
    {N : ℕ} (hN : 0 < N) (hlarge : 200 ≤ Real.log (N : ℝ)) :
    |arithmeticFloorPrefix w N - (N : ℝ)*C| ≤
      (2*W + 24*B + 8*D) * Real.sqrt (N : ℝ) /
        (6 + Real.log (N : ℝ))^(3/4 : ℝ) := by
  obtain ⟨y, hy, hyN, hylo, hyhi, hlog⟩ := logarithmic_hyperbola_cutoff hN hlarge
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hNy : (0 : ℝ) < N := by exact_mod_cast hN
  have hyone : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hL : 0 < 6 + Real.log (N : ℝ) := by linarith
  have hJ : 0 < 6 + Real.log (y : ℝ) := by linarith [Real.log_nonneg hyone]
  have hQ : 0 < (6 + Real.log (y : ℝ))^(3/2 : ℝ) := Real.rpow_pos_of_pos hJ _
  have hp : ∀ t : ℕ, y ≤ t → |positiveArithmeticPrefix w t| ≤
      B*Real.sqrt (t : ℝ)/(6 + Real.log (y : ℝ))^(3/2 : ℝ) := by
    intro t hyt
    have ht : 0 < t := lt_of_lt_of_le hy hyt
    have hty : (y : ℝ) ≤ t := by exact_mod_cast hyt
    have hlog' := Real.log_le_log hyR hty
    have hpow := Real.rpow_le_rpow hJ.le (by linarith : 6+Real.log (y : ℝ) ≤ 6+Real.log (t : ℝ))
      (by norm_num : (0 : ℝ) ≤ 3/2)
    exact (hP t ht).trans (div_le_div_of_nonneg_left (by positivity) hQ hpow)
  have hbound := arithmeticFloorPrefix_centered_hyperbola_bound w hw0 C hy hyN
    hW hB hD hQ hw hp (hT y hy)
  refine hbound.trans ?_
  have he := hyperbola_endpoint_scalar_bound hNy hyR hL hJ hW
    (show 0 ≤ 3*B+D by positivity) hylo hyhi hlog
  calc
    _ ≤ (2*W + 8*(3*B+D)) * Real.sqrt (N : ℝ) /
        (6 + Real.log (N : ℝ))^(3/4 : ℝ) := he
    _ = _ := by ring

end
end RiemannResearch.RH.Pareto
