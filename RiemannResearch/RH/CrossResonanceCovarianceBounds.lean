/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHarmonicBounds
import RiemannResearch.RH.ResonantHarmonicHead
import RiemannResearch.RH.AdjacentPacketCovarianceTransfer

/-!
# Uniform cross-seed covariance in a two-three resonance cell

Source: Christian Noack's resonance-cell continuation, 15 September 2026.
These estimates retain the complete signed tails of the actual digit covariance.
-/
namespace RiemannResearch.RH.Pareto.AdjacentDigit
open RiemannResearch.Analysis
noncomputable section

/-- The six exact leading cross-seed coefficients. -/
def crossLeading (r s : ℕ) : ℝ :=
  if r=0 then (if s=0 then 2/3 else 0)
  else if r=1 then 1/3 else (if s=1 then 2/3 else 0)

private def crossCoefficientError (k : ℝ) (r s : ℕ) : ℝ :=
  if r=0 then 2/(3*(3*k+1)) else if s=0 then 1/(3*(2*k+1))
  else if r=1 then 1/(3*(3*k+2)) else 1/(3*(k+1))

private theorem cross_coefficient_identity (k : ℝ) (hk : 0<k)
    (r s : ℕ) (hr : r≤2) (hs : s≤1)
    (hpos : max (2*r) (3*s) < min (2*(r+1)) (3*(s+1))) :
    (3*k+r)*(2*k+s)*(2/(6*k+(max (2*r) (3*s):ℕ))-
      2/(6*k+(min (2*(r+1)) (3*(s+1)):ℕ))) =
      crossLeading r s-crossCoefficientError k r s := by
  interval_cases r <;> interval_cases s <;>
    norm_num [crossLeading, crossCoefficientError] at * <;>
    field_simp <;> ring

private theorem cross_coefficient_error_bound (k : ℝ) (hk : 0<k) (r s : ℕ) :
    0 ≤ crossCoefficientError k r s ∧ crossCoefficientError k r s ≤ 1/k := by
  unfold crossCoefficientError
  split_ifs <;> constructor
  all_goals first | positivity | (apply (div_le_div_iff₀ (by positivity) hk).mpr; nlinarith)

/-- All six scaled digit entries have a uniform bounded harmonic remainder. -/
theorem cross_cell_harmonic_bound (k r s : ℕ) (hk : 24≤k)
    (hr : r≤2) (hs : s≤1) :
    |((3*k+r:ℕ):ℝ)*((2*k+s:ℕ):ℝ)*crossCovariance 2 3 (3*k+r) (2*k+s)-
      crossLeading r s*(harmonic k:ℝ)| ≤ 500 := by
  have hk0 : 0<k := by omega
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hmn : (0:ℝ)≤((3*k+r:ℕ):ℝ)*((2*k+s:ℕ):ℝ) := by positivity
  have hmhi : ((3*k+r:ℕ):ℝ)≤5*(k:ℝ) := by exact_mod_cast (show 3*k+r≤5*k by omega)
  have hnhi : ((2*k+s:ℕ):ℝ)≤3*(k:ℝ) := by exact_mod_cast (show 2*k+s≤3*k by omega)
  have hmprod : ((3*k+r:ℕ):ℝ)*((2*k+s:ℕ):ℝ)≤15*(k:ℝ)^2 := by
    nlinarith [mul_le_mul hmhi hnhi (by positivity) (by positivity : (0:ℝ)≤5*k)]
  by_cases hpos : max (2*r) (3*s)<min (2*(r+1)) (3*(s+1))
  · let T := k/12
    let U := min (2*(r+1)) (3*(s+1))
    let N := (6*k+U)*T
    have hT : 0<T := by dsimp [T]; omega
    have hTk : 12*T≤k := by dsimp [T]; omega
    have hkT : k≤24*T := by dsimp [T]; omega
    have hN : 0<N := by dsimp [N]; positivity
    have hNlo : (k:ℝ)^2≤4*(N:ℝ) := by
      have htR : (k:ℝ)≤24*(T:ℝ) := by exact_mod_cast hkT
      dsimp [N]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left htR (le_of_lt hkR),
        mul_nonneg (Nat.cast_nonneg (α:=ℝ) U) (Nat.cast_nonneg (α:=ℝ) T)]
    have htail := cross_tail_bound 2 3 (3*k+r) (2*k+s) N (by omega) (by omega) hN
    have hscaled : |((3*k+r:ℕ):ℝ)*((2*k+s:ℕ):ℝ)*
        (∑' n, crossTail 2 3 (3*k+r) (2*k+s) N n)|≤360 := by
      rw [abs_mul, abs_of_nonneg hmn]
      apply (mul_le_mul_of_nonneg_left htail hmn).trans
      norm_num only [Nat.cast_ofNat]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)).mpr
      nlinarith
    have hc := cross_coefficient_identity (k:ℝ) hkR r s hr hs hpos
    have he := cross_coefficient_error_bound (k:ℝ) hkR r s
    have hHT0 := harmonic_nonnegative T
    have hHT : (harmonic T:ℝ)≤(k:ℝ) :=
      (harmonic_le_index T).trans (by exact_mod_cast (show T≤k by dsimp [T]; omega))
    have herr : |crossCoefficientError (k:ℝ) r s*(harmonic T:ℝ)|≤1 := by
      rw [abs_of_nonneg (mul_nonneg he.1 hHT0)]
      calc
        _ ≤ (1/(k:ℝ))*(k:ℝ) := mul_le_mul he.2 hHT hHT0 (by positivity)
        _ = 1 := by field_simp
    have hw : |crossLeading r s|≤2 := by
      unfold crossLeading
      split_ifs <;> norm_num
    have hgap : |crossLeading r s*((harmonic T:ℝ)-(harmonic k:ℝ))|≤24 := by
      rw [abs_mul, abs_sub_comm]
      exact (mul_le_mul hw (harmonic_twelfth_gap k) (abs_nonneg _) (by norm_num)).trans (by norm_num)
    have hid : ((3*k+r:ℕ):ℝ)*((2*k+s:ℕ):ℝ)*crossCovariance 2 3 (3*k+r) (2*k+s)-
        crossLeading r s*(harmonic k:ℝ) =
        crossLeading r s*((harmonic T:ℝ)-(harmonic k:ℝ))-
          crossCoefficientError (k:ℝ) r s*(harmonic T:ℝ)+
          ((3*k+r:ℕ):ℝ)*((2*k+s:ℕ):ℝ)*
            (∑' n, crossTail 2 3 (3*k+r) (2*k+s) N n) := by
      rw [two_three_exact_harmonic_tail k r s T hk0 hr hs hTk hpos]
      dsimp [N,U]
      push_cast at hc ⊢
      have hcm := congrArg (fun z : ℝ => z*(harmonic T:ℝ)) hc
      nlinarith only [hcm]
    rw [hid]
    calc
      _ ≤ |crossLeading r s*((harmonic T:ℝ)-(harmonic k:ℝ))-
          crossCoefficientError (k:ℝ) r s*(harmonic T:ℝ)|+
          |((3*k+r:ℕ):ℝ)*((2*k+s:ℕ):ℝ)*
            (∑' n, crossTail 2 3 (3*k+r) (2*k+s) N n)| := abs_add_le _ _
      _ ≤ (24+1)+360 := add_le_add ((abs_sub _ _).trans (add_le_add hgap herr)) hscaled
      _ ≤ 500 := by norm_num
  · have hsep : 2*(r+1)≤3*s ∨ 3*(s+1)≤2*r := by omega
    have hc := separated_two_three_covariance_bound 2 3 k r s (k*k)
      (by omega) (by omega) hk0 hr hs hsep (by positivity) le_rfl
    have hw : crossLeading r s=0 := by
      interval_cases r <;> interval_cases s <;> norm_num [crossLeading] at *
    rw [hw, zero_mul, sub_zero, abs_mul, abs_of_nonneg hmn]
    apply (mul_le_mul_of_nonneg_left hc hmn).trans
    norm_num only [Nat.cast_ofNat, Nat.cast_mul]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(k:ℝ)*(k:ℝ))).mpr
    nlinarith

end
end RiemannResearch.RH.Pareto.AdjacentDigit
