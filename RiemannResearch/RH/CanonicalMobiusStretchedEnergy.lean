/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CanonicalMobiusQuantitativeEnergy
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensStretchedDecay
import RiemannResearch.Analysis.StretchedExponentialBounds

/-!
# Full canonical Möbius energy from stretched Mertens cancellation

Source: the user's request to improve the unconditional arithmetic estimate in
the Pareto projection program. This development combines the repository's
Mertens provider with its exact reciprocal cutoff and complete harmonic-window
energy estimate. The infinite physical tail is included throughout.
The transfer argument is elementary; no mathematical novelty is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis

theorem canonicalMobius_energy_of_uniform_mertens_square
    (N : ℕ) (hN : 0 < N) (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ h ^ 2 * y) :
    |mobiusReciprocalSum N| ≤ 5 * h ∧
      ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ) ≤ 3 / (N : ℝ) + 260 * h := by
  let K : ℕ := ⌈1 / h⌉₊
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hKlo : 1 / h ≤ (K : ℝ) := Nat.le_ceil _
  have hKhi : (K : ℝ) ≤ 1 / h + 1 := by
    exact (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / h)).le
  have hinv2 : (2 : ℝ) ≤ 1 / h := (le_div_iff₀ hh).mpr (by linarith)
  have hK2 : 2 ≤ K := by exact_mod_cast hinv2.trans hKlo
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKinv : 1 / (K : ℝ) ≤ h := by
    apply (div_le_iff₀ hK0).mpr
    have hp := (div_le_iff₀ hh).mp hKlo
    nlinarith
  have hKh : (K : ℝ) * h ≤ 2 := by
    have hp := mul_le_mul_of_nonneg_right hKhi hh.le
    have hi : (1 / h + 1) * h = 1 + h := by field_simp
    rw [hi] at hp
    linarith
  have hNK : 1 / ((N : ℝ) * (K : ℝ)) ≤ 1 / (K : ℝ) := by
    apply one_div_le_one_div_of_le hK0
    nlinarith
  have hH := harmonic_le_index K
  have hH0 := harmonic_nonnegative K
  have hAh : h ^ 2 * ((harmonic K : ℝ) + 1) ≤ 3 * h := by
    have hp := mul_le_mul_of_nonneg_left (by linarith : (harmonic K : ℝ) + 1 ≤ (K : ℝ) + 1)
      (sq_nonneg h)
    have hp' := mul_le_mul_of_nonneg_right hKh hh.le
    nlinarith
  have hm := mobiusReciprocalSum_cutoff_bound_of_uniform_M_bound N K hN
    (by omega) (h ^ 2) (sq_nonneg h) hM
  have hm5 : |mobiusReciprocalSum N| ≤ 5 * h := by linarith
  refine ⟨hm5, ?_⟩
  have hnat : ∀ t : ℕ, N ≤ t → |∑ d ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ)| ≤ h ^ 2 * (t : ℝ) := by
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
    (h ^ 2) (5 * h) (sq_nonneg h) (by positivity) hnat hm5
  have hD0 : 0 ≤ h ^ 2 * ((harmonic K : ℝ) + 1) + 5 * h := by positivity
  have hD8 : h ^ 2 * ((harmonic K : ℝ) + 1) + 5 * h ≤ 8 * h := by linarith
  have hs := (sq_le_sq₀ hD0 (by positivity : 0 ≤ 8 * h)).mpr hD8
  have hp := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * (K : ℝ) by positivity)
  have hp' := mul_le_mul_of_nonneg_right hKh hh.le
  have hfour : 4 / (K : ℝ) ≤ 4 * h := by
    calc
      _ = 4 * (1 / (K : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKinv (by norm_num)
  nlinarith only [he, hp, hp', hfour]

/-- Unconditional stretched decay for both the reciprocal charge and the
complete canonical energy. The constants come from the checked Mertens provider. -/
theorem canonicalMobius_eventual_stretched_bounds :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |mobiusReciprocalSum N| ≤ C *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) ∧
      ‖canonicalMobiusHilbert N‖ ^ 2 ≤ 3 + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
  obtain ⟨d, hd, B, hB, hM⟩ := M_stretched_loglog_bound
  let φ : ℕ → ℝ := fun N => logProductPower (1 / 11) (6 + Real.log (N : ℝ))
  let h : ℕ → ℝ := fun N => Real.sqrt (B + 1) * Real.exp (-(d / 2) * φ N)
  have hroot : 0 < Real.sqrt (B + 1) := Real.sqrt_pos.2 (by linarith)
  have hpos (N : ℕ) : 0 < h N := mul_pos hroot (Real.exp_pos _)
  have hL : Tendsto (fun N : ℕ => 6 + Real.log (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hphi : Tendsto φ atTop atTop :=
    (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp hL
  have hexp : Tendsto (fun N => Real.exp (-(d / 2) * φ N)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_comp_nhds_zero.mpr
    exact hphi.const_mul_atTop_of_neg (by linarith)
  have hlim : Tendsto h atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul (Real.sqrt (B + 1))
  refine ⟨d / 2, by positivity, 260 * Real.sqrt (B + 1), by positivity, ?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (1 : ℕ)] with N hsmall hN
  have hN0 : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR : (0 : ℝ) < N := by positivity
  have hsquare : h N ^ 2 = (B + 1) * Real.exp (-d * φ N) := by
    have he : (Real.exp (-(d / 2) * φ N)) ^ 2 = Real.exp (-d * φ N) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    dsimp [h]
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ B + 1), he]
  have htail (y : ℝ) (hy : (N : ℝ) ≤ y) : |M y| ≤ h N ^ 2 * y := by
    have hy1 : 1 ≤ y := hN1.trans hy
    have hmono : φ N ≤ logProductPower (1 / 11) (6 + Real.log y) := by
      apply logProductPower_mono (1 / 11) (by norm_num)
      · linarith [Real.log_nonneg hN1]
      · linarith [Real.log_le_log hNR hy]
    have he : Real.exp (-d * logProductPower (1 / 11) (6 + Real.log y)) ≤
        Real.exp (-d * φ N) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hm : |M y| ≤ B * y *
        Real.exp (-d * logProductPower (1 / 11) (6 + Real.log y)) := hM y hy1
    rw [hsquare]
    calc
      _ ≤ B * y * Real.exp (-d * φ N) :=
        hm.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hB (by linarith)))
      _ ≤ (B + 1) * Real.exp (-d * φ N) * y := by
        nlinarith [mul_nonneg (Real.exp_pos (-d * φ N)).le (show 0 ≤ y by linarith)]
  obtain ⟨hm, he⟩ := canonicalMobius_energy_of_uniform_mertens_square N hN0
    (h N) (hpos N) hsmall.le htail
  constructor
  · change |mobiusReciprocalSum N| ≤ 260 * Real.sqrt (B + 1) *
      Real.exp (-(d / 2) * φ N)
    have hh : 5 * h N ≤ 260 * h N := by nlinarith [hpos N]
    calc
      _ ≤ 260 * h N := hm.trans hh
      _ = _ := by dsimp [h]; ring
  · have hh := (div_le_iff₀ hNR).mp he
    calc
      _ ≤ (3 / (N : ℝ) + 260 * h N) * (N : ℝ) := hh
      _ = _ := by
        dsimp [h, φ]
        field_simp

/-- The stronger arithmetic rate controls the full error of the auxiliary
exact-head family. The factor N remains; this is not norm convergence to one. -/
theorem canonicalMobiusResidual_eventual_stretched_energy :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ 8 + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
  obtain ⟨a, ha, C, hC, hbounds⟩ := canonicalMobius_eventual_stretched_bounds
  refine ⟨a, ha, 2 * C, by positivity, ?_⟩
  filter_upwards [hbounds] with N hN
  have he := canonicalMobiusResidual_norm_sq_le N
  nlinarith [hN.2]

end RiemannResearch.RH.Pareto
