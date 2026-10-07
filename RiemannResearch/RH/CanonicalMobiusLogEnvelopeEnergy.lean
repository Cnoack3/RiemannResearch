/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusQuantitativeEnergy

/-!
# Logarithmic loss in the full canonical Möbius energy transfer

Source: the user-requested source-resolvent continuation, 7 October 2026.
The cutoff inequalities are established in CanonicalMobiusQuantitativeEnergy.

The arithmetic premises and the entire infinite physical tail are preserved.
The proof improves the square-root uniform-Mertens envelope by using the
logarithmic harmonic bound in the two finite cutoff choices.
No novelty is asserted for the elementary optimization.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis

/-- A logarithmic harmonic estimate uniform for every integer below `2 / ε`.
The positive-index assumption prevents a logarithm-at-zero specialization. -/
private theorem harmonic_add_one_le_three_reciprocal_log
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (R : ℕ) (hR : 0 < R) (hRupper : (R : ℝ) ≤ 2 * (1 / ε)) :
    (harmonic R : ℝ) + 1 ≤ 3 * (1 + Real.log (1 / ε)) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hinvpos : 0 < 1 / ε := one_div_pos.mpr hε
  have hinvone : (1 : ℝ) ≤ 1 / ε :=
    (le_div_iff₀ hε).mpr (by simpa using hεone)
  have hloginv : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hinvone
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogR := Real.log_le_log hRpos hRupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hinvpos.ne'] at hlogR
  have hH := harmonic_le_one_add_log R
  linarith

/-- If the complete Mertens tail has relative size `ε`, both the reciprocal
charge and the complete canonical energy have size `ε * (1 + log (1 / ε))`.
The uniform arithmetic provider is explicit in the theorem's type. -/
theorem canonicalMobius_energy_of_uniform_mertens_log
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ ε * y) :
    |mobiusReciprocalSum N| ≤ 5 * (ε * (1 + Real.log (1 / ε))) ∧
      ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ) ≤
        3 / (N : ℝ) + 260 * (ε * (1 + Real.log (1 / ε))) := by
  let L : ℝ := 1 + Real.log (1 / ε)
  let h : ℝ := ε * L
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hinvpos : 0 < 1 / ε := one_div_pos.mpr hε
  have hinvone : (1 : ℝ) ≤ 1 / ε :=
    (le_div_iff₀ hε).mpr (by simpa using hεone)
  have hLone : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hinvone]
  have hLpos : 0 < L := by linarith
  have hh : 0 < h := mul_pos hε hLpos
  have hhsmall : h ≤ 1 / 2 := hsmall
  have hεh : ε ≤ h := by
    dsimp [h]
    nlinarith
  let J : ℕ := ⌈1 / ε⌉₊
  let K : ℕ := ⌈1 / h⌉₊
  have hJlo : 1 / ε ≤ (J : ℝ) := Nat.le_ceil _
  have hJhi : (J : ℝ) ≤ 1 / ε + 1 :=
    (Nat.ceil_lt_add_one hinvpos.le).le
  have hJ0 : (0 : ℝ) < J := hinvpos.trans_le hJlo
  have hJ : 0 < J := by exact_mod_cast hJ0
  have hJupper : (J : ℝ) ≤ 2 * (1 / ε) := by linarith
  have hKlo : 1 / h ≤ (K : ℝ) := Nat.le_ceil _
  have hKhi : (K : ℝ) ≤ 1 / h + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / h)).le
  have hinv2 : (2 : ℝ) ≤ 1 / h := (le_div_iff₀ hh).mpr (by linarith)
  have hK2 : 2 ≤ K := by exact_mod_cast hinv2.trans hKlo
  have hK : 0 < K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hhinv : 1 / h ≤ 1 / ε := one_div_le_one_div_of_le hε hεh
  have hKupper : (K : ℝ) ≤ 2 * (1 / ε) := by linarith
  have hHJ : (harmonic J : ℝ) + 1 ≤ 3 * L :=
    harmonic_add_one_le_three_reciprocal_log ε hε hεone J hJ hJupper
  have hHK : (harmonic K : ℝ) + 1 ≤ 3 * L :=
    harmonic_add_one_le_three_reciprocal_log ε hε hεone K hK hKupper
  have hJinv : 1 / (J : ℝ) ≤ ε := by
    apply (div_le_iff₀ hJ0).mpr
    have hp := (div_le_iff₀ hε).mp hJlo
    nlinarith
  have hNJ : 1 / ((N : ℝ) * (J : ℝ)) ≤ 1 / (J : ℝ) := by
    apply one_div_le_one_div_of_le hJ0
    nlinarith
  have hKinv : 1 / (K : ℝ) ≤ h := by
    apply (div_le_iff₀ hK0).mpr
    have hp := (div_le_iff₀ hh).mp hKlo
    nlinarith
  have hKh : (K : ℝ) * h ≤ 2 := by
    have hp := mul_le_mul_of_nonneg_right hKhi hh.le
    have hi : (1 / h + 1) * h = 1 + h := by field_simp
    rw [hi] at hp
    linarith
  have hAhJ : ε * ((harmonic J : ℝ) + 1) ≤ 3 * h := by
    have hp := mul_le_mul_of_nonneg_left hHJ hε.le
    dsimp [h] at *
    nlinarith
  have hAhK : ε * ((harmonic K : ℝ) + 1) ≤ 3 * h := by
    have hp := mul_le_mul_of_nonneg_left hHK hε.le
    dsimp [h] at *
    nlinarith
  have hm := mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound N J hN
    hJ ε hε.le hM
  have hm5 : |mobiusReciprocalSum N| ≤ 5 * h := by
    linarith
  change |mobiusReciprocalSum N| ≤ 5 * h ∧
    ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ) ≤ 3 / (N : ℝ) + 260 * h
  refine ⟨hm5, ?_⟩
  have hnat : ∀ t : ℕ, N ≤ t → |∑ d ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ) := by
    intro t hNt
    have hi := M_nat_difference 0 t (Nat.zero_le t)
    have hset : Finset.Ioc 0 t = Finset.Icc 1 t := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hzero : M (0 : ℝ) = 0 := by
      have hz : Finset.Iic (0 : ℕ) = {0} := by ext n; simp
      simp [M, hz]
    rw [hset, Nat.cast_zero, hzero, sub_zero] at hi
    rw [← hi]
    exact hM _ (by exact_mod_cast hNt)
  have he := canonicalMobiusHilbert_harmonic_energy_bound N K hN hK2
    ε (5 * h) hε.le (by positivity) hnat hm5
  have hH0 : (0 : ℝ) ≤ (harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i))
  have hD0 : 0 ≤ ε * ((harmonic K : ℝ) + 1) + 5 * h := by positivity
  have hD8 : ε * ((harmonic K : ℝ) + 1) + 5 * h ≤ 8 * h := by linarith
  have hs := (sq_le_sq₀ hD0 (by positivity : 0 ≤ 8 * h)).mpr hD8
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * (K : ℝ) by positivity)
  have hp' := mul_le_mul_of_nonneg_right hKh hh.le
  have hfour : 4 / (K : ℝ) ≤ 4 * h := by
    calc
      _ = 4 * (1 / (K : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKinv (by norm_num)
  nlinarith only [he, hp, hp', hfour]

end RiemannResearch.RH.Pareto
