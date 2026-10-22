/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.OldNewDigitHead
import RiemannResearch.Analysis.FiniteHarmonicBounds

/-!
# Uniform covariance bounds between old and new digit packets

Source: RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md and its
formal continuation. The four concrete corollaries discharge the periodic
source premise of the generic estimate and retain the entire signed tail.
-/

namespace RiemannResearch.RH.Pareto.AdjacentDigit
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- An explicit full-tail old/new estimate from its verified periodic source. -/
theorem old_new_scaled_covariance_bound (p q a k r : ℕ) (μ : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : (p:ℝ)*q ≤ 9)
    (ha : 1 ≤ a) (ha3 : a ≤ 3) (hk : 24 ≤ k) (hr : r < a)
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2)
    (hsample : |sampledHarmonic p q a (k/12) - μ*(harmonic (k/12):ℝ)| ≤ 132) :
    |((a*k+r:ℕ):ℝ)*(k:ℝ)*crossCovariance p q (a*k+r) k -
      (μ/(a:ℝ))*(harmonic k:ℝ)| ≤ 500 := by
  let T := k/12
  let m := a*k+r
  let N := (m+1)*T
  let H := (harmonic T:ℝ)
  let S := sampledHarmonic p q a T
  let δ := ∑' n, crossTail p q m k N n
  let c := (k:ℝ)/((m:ℝ)+1)
  have hTpos : 0 < T := by dsimp [T]; omega
  have hT : 12*T ≤ k := by dsimp [T]; omega
  have hTk : T ≤ k := by dsimp [T]; omega
  have hkT : k ≤ 24*T := by dsimp [T]; omega
  have hak := Nat.mul_le_mul_right k ha
  have hkm : k ≤ m := by dsimp [m]; omega
  have hmpos : 0 < m := by omega
  have hNpos : 0 < N := Nat.mul_pos (Nat.succ_pos _) hTpos
  have hapos : 0 < (a:ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hmpos
  have hm1R : 0 < (m:ℝ)+1 := by positivity
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hNpos
  have hmcast : (m:ℝ) = (a:ℝ)*(k:ℝ)+(r:ℝ) := by simp [m]
  have hNcast : (N:ℝ) = ((m:ℝ)+1)*(T:ℝ) := by simp [N]
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_iff₀ hm1R).mpr
    have hkmR : (k:ℝ) ≤ m := by exact_mod_cast hkm
    linarith
  have hca : c ≤ 1/(a:ℝ) := by
    dsimp [c]
    apply (div_le_div_iff₀ hm1R hapos).mpr
    rw [hmcast]
    nlinarith only [Nat.cast_nonneg (α:=ℝ) r]
  have hratio0 : 0 ≤ μ/(a:ℝ) := div_nonneg hμ0 (le_of_lt hapos)
  have hratio2 : μ/(a:ℝ) ≤ 2 := by
    apply (div_le_iff₀ hapos).mpr
    have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
    nlinarith only [haR, hμ2]
  have hH0 : 0 ≤ H := harmonic_nonnegative T
  have hHle : H ≤ (m:ℝ)+1 := by
    have hH := harmonic_le_index T
    have hTmR : (T:ℝ) ≤ m := by exact_mod_cast hTk.trans hkm
    dsimp [H]
    linarith only [hH, hTmR]
  have hgap0 : 0 ≤ 1/(a:ℝ)-c := sub_nonneg.mpr hca
  have hgap_exact : (1/(a:ℝ)-c)*((m:ℝ)+1) = ((r:ℝ)+1)/(a:ℝ) := by
    dsimp [c]
    rw [hmcast]
    field_simp
    ring
  have hgap_unit : (1/(a:ℝ)-c)*H ≤ 1 := by
    calc
      _ ≤ (1/(a:ℝ)-c)*((m:ℝ)+1) := mul_le_mul_of_nonneg_left hHle hgap0
      _ = ((r:ℝ)+1)/(a:ℝ) := hgap_exact
      _ ≤ 1 := by
        apply (div_le_iff₀ hapos).mpr
        have hrR : (r:ℝ)+1 ≤ a := by exact_mod_cast (show r+1 ≤ a by omega)
        simpa using hrR
  have hex := old_new_exact_harmonic_tail p q a k r T hp hq ha ha3
    (by omega) hr hT
  have hm1cast : ((m+1:ℕ):ℝ) = (m:ℝ)+1 := by simp
  rw [hm1cast] at hex
  change crossCovariance p q m k =
    (1/(m:ℝ)-1/((m:ℝ)+1))*S + δ at hex
  have hscale : (m:ℝ)*(k:ℝ)*(1/(m:ℝ)-1/((m:ℝ)+1)) = c := by
    dsimp [c]
    field_simp
    ring
  have hscaled : (m:ℝ)*(k:ℝ)*crossCovariance p q m k =
      c*S+(m:ℝ)*(k:ℝ)*δ := by
    rw [hex]
    calc
      _ = ((m:ℝ)*(k:ℝ)*(1/(m:ℝ)-1/((m:ℝ)+1)))*S +
          (m:ℝ)*(k:ℝ)*δ := by ring
      _ = _ := by rw [hscale]
  have htail0 := cross_tail_bound p q m k N hp hq hNpos
  change |δ| ≤ (p:ℝ)*q/(N:ℝ) at htail0
  have htail : |(m:ℝ)*(k:ℝ)*δ| ≤ 216 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)*(k:ℝ))]
    calc
      _ ≤ (m:ℝ)*(k:ℝ)*((p:ℝ)*q/(N:ℝ)) :=
        mul_le_mul_of_nonneg_left htail0 (by positivity)
      _ = ((m:ℝ)*(k:ℝ)*((p:ℝ)*q))/(N:ℝ) := by ring
      _ ≤ 216 := by
        apply (div_le_iff₀ hNR).mpr
        rw [hNcast]
        have hprod := mul_le_mul_of_nonneg_left hpq
          (by positivity : 0 ≤ (m:ℝ)*(k:ℝ))
        have hkTR : (k:ℝ) ≤ 24*(T:ℝ) := by exact_mod_cast hkT
        have hmul := mul_le_mul_of_nonneg_left hkTR (by positivity : 0 ≤ 9*(m:ℝ))
        nlinarith only [hprod, hmul, Nat.cast_nonneg (α:=ℝ) T]
  have hperiod : |c*(S-μ*H)| ≤ 132 := by
    rw [abs_mul, abs_of_nonneg hc0]
    have hs : |S-μ*H| ≤ 132 := hsample
    have h1 := mul_le_mul_of_nonneg_left hs hc0
    have h2 := mul_le_mul_of_nonneg_right hc1 (by norm_num : (0:ℝ) ≤ 132)
    nlinarith only [h1, h2]
  have hcoefficient : |(c-1/(a:ℝ))*μ*H| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr hca),
      abs_of_nonneg hμ0, abs_of_nonneg hH0]
    have hh := mul_le_mul_of_nonneg_left hgap_unit hμ0
    nlinarith only [hh, hμ2]
  have hcutoff : |(μ/(a:ℝ))*(H-(harmonic k:ℝ))| ≤ 24 := by
    rw [abs_mul, abs_of_nonneg hratio0]
    have hgap : |H-(harmonic k:ℝ)| ≤ 12 := by
      dsimp [H,T]
      simpa only [abs_sub_comm] using harmonic_twelfth_gap k
    have h1 := mul_le_mul_of_nonneg_left hgap hratio0
    have h2 := mul_le_mul_of_nonneg_right hratio2 (by norm_num : (0:ℝ) ≤ 12)
    nlinarith only [h1, h2]
  have he : (m:ℝ)*(k:ℝ)*crossCovariance p q m k -
      (μ/(a:ℝ))*(harmonic k:ℝ) =
      c*(S-μ*H) + (c-1/(a:ℝ))*μ*H + (m:ℝ)*(k:ℝ)*δ +
      (μ/(a:ℝ))*(H-(harmonic k:ℝ)) := by
    rw [hscaled]
    ring
  change |(m:ℝ)*(k:ℝ)*crossCovariance p q m k -
    (μ/(a:ℝ))*(harmonic k:ℝ)| ≤ 500
  rw [he]
  have h1 := abs_add_le (c*(S-μ*H)) ((c-1/(a:ℝ))*μ*H)
  have h2 := abs_add_le (c*(S-μ*H)+(c-1/(a:ℝ))*μ*H) ((m:ℝ)*(k:ℝ)*δ)
  have h3 := abs_add_le (c*(S-μ*H)+(c-1/(a:ℝ))*μ*H+(m:ℝ)*(k:ℝ)*δ)
    ((μ/(a:ℝ))*(H-(harmonic k:ℝ)))
  linarith only [h1, h2, h3, htail, hperiod, hcoefficient, hcutoff]

theorem old_new_binary_covariance_bound (k r : ℕ) (hk : 24 ≤ k) (hr : r < 3) :
    |((3*k+r:ℕ):ℝ)*(k:ℝ)*crossCovariance 2 2 (3*k+r) k -
      (1/3:ℝ)*(harmonic k:ℝ)| ≤ 500 := by
  apply old_new_scaled_covariance_bound 2 2 3 k r 1
    (by omega) (by omega) (by norm_num) (by omega) (by omega) hk hr
    (by norm_num) (by norm_num)
  have h := old_new_binary_harmonic_error (k/12)
  norm_num at h ⊢
  linarith

theorem old_new_ternary_covariance_bound (k r : ℕ) (hk : 24 ≤ k) (hr : r < 2) :
    |((2*k+r:ℕ):ℝ)*(k:ℝ)*crossCovariance 3 3 (2*k+r) k -
      (harmonic k:ℝ)| ≤ 500 := by
  have h := old_new_scaled_covariance_bound 3 3 2 k r 2
    (by omega) (by omega) (by norm_num) (by omega) (by omega) hk hr
    (by norm_num) (by norm_num) (old_new_ternary_harmonic_error (k/12))
  norm_num at h
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

theorem old_new_binary_ternary_covariance_bound (k r : ℕ) (hk : 24 ≤ k) (hr : r < 3) :
    |((3*k+r:ℕ):ℝ)*(k:ℝ)*crossCovariance 2 3 (3*k+r) k| ≤ 500 := by
  have hs : |sampledHarmonic 2 3 3 (k/12) - (0:ℝ)*(harmonic (k/12):ℝ)| ≤ 132 := by
    have h := old_new_binary_ternary_harmonic_bound (k/12)
    simp only [zero_mul, sub_zero]
    linarith
  have h := old_new_scaled_covariance_bound 2 3 3 k r 0
    (by omega) (by omega) (by norm_num) (by omega) (by omega) hk hr
    (by norm_num) (by norm_num) hs
  simpa using h

theorem old_new_ternary_binary_covariance_bound (k r : ℕ) (hk : 24 ≤ k) (hr : r < 2) :
    |((2*k+r:ℕ):ℝ)*(k:ℝ)*crossCovariance 3 2 (2*k+r) k| ≤ 500 := by
  have hs : |sampledHarmonic 3 2 2 (k/12) - (0:ℝ)*(harmonic (k/12):ℝ)| ≤ 132 := by
    have h := old_new_ternary_binary_harmonic_bound (k/12)
    simp only [zero_mul, sub_zero]
    linarith
  have h := old_new_scaled_covariance_bound 3 2 2 k r 0
    (by omega) (by omega) (by norm_num) (by omega) (by omega) hk hr
    (by norm_num) (by norm_num) hs
  simpa using h

end
end RiemannResearch.RH.Pareto.AdjacentDigit
