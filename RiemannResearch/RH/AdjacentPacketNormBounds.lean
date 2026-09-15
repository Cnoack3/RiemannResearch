/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.AdjacentDigitCovariance
import RiemannResearch.RH.AdjacentDilationPackets
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Uniform logarithmic bounds for the actual adjacent packets

Source: the written analytic proof in
RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md and its predecessor.
The digit covariance estimates include the complete infinite tail.
Weighted Young's inequality controls the correction from digit differences
to the original scaled generators without changing their normalization.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket
noncomputable section
open scoped BigOperators
open AdjacentDigit

private theorem harmonic_cast_le_nat (m : ℕ) : (harmonic m : ℝ) ≤ (m:ℝ) := by
  have he : (harmonic m : ℝ) = ∑ k ∈ Finset.range m, 1/((k:ℝ)+1) := by
    simp [harmonic, one_div]
  rw [he]
  calc
    _ ≤ ∑ _k ∈ Finset.range m, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (div_le_iff₀ (by positivity : 0 < (k:ℝ)+1)).mpr
      norm_num
    _ = (m:ℝ) := by simp

private theorem harmonic_log_abs_le (m : ℕ) (hm : 0 < m) :
    |(harmonic m:ℝ)-Real.log (m:ℝ)| ≤ 1 := by
  have hu := harmonic_le_one_add_log m
  have hl := log_add_one_le_harmonic m
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log (m:ℝ) ≤ Real.log ((m+1:ℕ):ℝ) :=
    Real.log_le_log hm0 (by exact_mod_cast Nat.le_succ m)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact energy scaling for the unscaled digit Hilbert vector. -/
theorem digit_energy_scaling (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    (m:ℝ)*‖digitHilbert p m hp hm‖^2 =
      ‖digitHilbert p 1 hp (by omega)‖^2 := by
  have he := digitHilbert_norm_sq_scale p 1 m hp (by omega) hm
  simp only [Nat.mul_one] at he
  rw [he]
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  field_simp

/-- The actual packet differs from the scaled digit difference by one small digit. -/
theorem packet_eq_digit_correction (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    packet p m hp hm = digitHilbert p (m+1) hp (by omega) -
      (m:ℝ) • (digitHilbert p m hp hm-digitHilbert p (m+1) hp (by omega)) := by
  unfold packet
  rw [generator_eq_scaled_digit, generator_eq_scaled_digit]
  push_cast
  rw [add_smul, one_smul, smul_sub]
  abel

/-- Transfer a complete digit covariance bound to the original packet norm. -/
theorem packet_harmonic_error (p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    {a E : ℝ} (ha : 0 ≤ a) (hE : 0 ≤ E)
    (he : |(m:ℝ)*((m:ℝ)+1)*covariance p p m-a*(harmonic m:ℝ)| ≤ E) :
    |‖packet p m hp hm‖^2-a*(harmonic m:ℝ)| ≤
      2*‖digitHilbert p 1 hp (by omega)‖^2+2*a+3*E := by
  let B := digitHilbert p (m+1) hp (by omega)
  let U := (m:ℝ) • (digitHilbert p m hp hm-digitHilbert p (m+1) hp (by omega))
  let C := ‖digitHilbert p 1 hp (by omega)‖^2
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hH := harmonic_cast_le_nat m
  have hc : 0 ≤ covariance p p m := by
    rw [covariance_eq_inner p p m hp hp hm, real_inner_self_eq_norm_sq]
    positivity
  have hU : ‖U‖^2 = (m:ℝ)^2*covariance p p m := by
    dsimp [U]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      covariance_eq_inner p p m hp hp hm, real_inner_self_eq_norm_sq]
  have hB : ((m:ℝ)+1)*‖B‖^2 = C := by
    simpa only [Nat.cast_add, Nat.cast_one] using digit_energy_scaling p (m+1) hp (by omega)
  have hB0 := sq_nonneg ‖B‖
  have hC0 : 0 ≤ C := sq_nonneg _
  have hBsmall : ‖B‖^2 ≤ C := by nlinarith
  have hmB : (m:ℝ)*‖B‖^2 ≤ C := by nlinarith
  have hraw := abs_le.mp he
  have hsmall : ((m:ℝ)+1)*covariance p p m ≤ a+E := by
    refine le_of_mul_le_mul_left (a := (m:ℝ)) ?_ hm0
    have h1 := mul_le_mul_of_nonneg_left hH ha
    have h2 := mul_le_mul_of_nonneg_left hm1 hE
    nlinarith
  have hmc : (m:ℝ)*covariance p p m ≤ a+E := by nlinarith
  have hUbound : ‖U‖^2 ≤ (m:ℝ)*(a+E) := by
    rw [hU]
    have he := mul_le_mul_of_nonneg_left hmc (le_of_lt hm0)
    nlinarith
  have hUerror : |‖U‖^2-a*(harmonic m:ℝ)| ≤ a+2*E := by
    rw [hU]
    have hmc0 : 0 ≤ (m:ℝ)*covariance p p m := mul_nonneg (le_of_lt hm0) hc
    apply abs_le.mpr
    constructor <;> nlinarith
  have hYoung : 2*‖B‖*‖U‖ ≤ C+a+E := by
    refine le_of_mul_le_mul_left (a := (m:ℝ)) ?_ hm0
    have h1 := mul_le_mul_of_nonneg_left hmB (le_of_lt hm0)
    nlinarith [sq_nonneg ((m:ℝ)*‖B‖-‖U‖)]
  have hinner : |inner ℝ B U| ≤ ‖B‖*‖U‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) B U
  have hpacket : packet p m hp hm = B-U := packet_eq_digit_correction p m hp hm
  have hnorm := norm_sub_sq_real B U
  have hcorrection : |‖packet p m hp hm‖^2-‖U‖^2| ≤ 2*C+a+E := by
    rw [hpacket]
    have hi := abs_le.mp hinner
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have ht := abs_add_le (‖packet p m hp hm‖^2-‖U‖^2)
    (‖U‖^2-a*(harmonic m:ℝ))
  simp only [sub_add_sub_cancel] at ht
  change |‖packet p m hp hm‖^2-a*(harmonic m:ℝ)| ≤ 2*C+2*a+3*E
  linarith

/-- Complete binary packet energy equals log(m) plus a fixed bounded remainder. -/
theorem binary_packet_log_bound (m : ℕ) (hm : 0 < m) :
    |‖packet 2 m (by omega) hm‖^2-Real.log (m:ℝ)| ≤
      2*‖digitHilbert 2 1 (by omega) (by omega)‖^2+87 := by
  have he := packet_harmonic_error 2 m (by omega) hm (a:=1) (E:=28)
    (by norm_num) (by norm_num) (by simpa using binary_covariance_harmonic_error m hm)
  have hh := harmonic_log_abs_le m hm
  have ht := abs_add_le (‖packet 2 m (by omega) hm‖^2-(harmonic m:ℝ))
    ((harmonic m:ℝ)-Real.log (m:ℝ))
  simp only [one_mul] at he
  simp only [sub_add_sub_cancel] at ht
  linarith

/-- Complete ternary packet energy equals 2 log(m) plus a fixed bounded remainder. -/
theorem ternary_packet_log_bound (m : ℕ) (hm : 0 < m) :
    |‖packet 3 m (by omega) hm‖^2-2*Real.log (m:ℝ)| ≤
      2*‖digitHilbert 3 1 (by omega) (by omega)‖^2+249 := by
  have he := packet_harmonic_error 3 m (by omega) hm (a:=2) (E:=81)
    (by norm_num) (by norm_num) (ternary_covariance_harmonic_error m hm)
  have hh := harmonic_log_abs_le m hm
  have hh2 : |2*(harmonic m:ℝ)-2*Real.log (m:ℝ)| ≤ 2 := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have ht := abs_add_le (‖packet 3 m (by omega) hm‖^2-2*(harmonic m:ℝ))
    (2*(harmonic m:ℝ)-2*Real.log (m:ℝ))
  simp only [sub_add_sub_cancel] at ht
  linarith

end
end RiemannResearch.RH.Pareto.AdjacentPacket
