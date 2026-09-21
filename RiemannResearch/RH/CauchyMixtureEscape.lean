import RiemannResearch.RH.CauchyMellinMixture
import RiemannResearch.RH.MellinModeEnergyBounds
import RiemannResearch.RH.MellinModeResiduePairing
import RiemannResearch.RH.CriticalMellinMixtureEnergy
import RiemannResearch.RH.CauchyFrequencyMoments

/-!
# The Cauchy escape from compact critical-frequency rigidity

Every positive-scale Cauchy mixture has positive finite Pareto energy,
although its individual critical-line modes have infinite energy. In the
right half of the critical strip, this concrete mixture annihilates every
arithmetic generator exactly when the corresponding point is a zeta zero.
This is an equivalence; it does not assert the existence of such a zero.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace RiemannResearch.RH.Pareto.SpectralObstruction

theorem cauchyMellinPoint_re_gt_half
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    (1 / 2 : ℝ) < (cauchyMellinPoint δ γ).re := by
  have hδpos : 0 < (δ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hδ)
  rw [cauchyMellinPoint_re]
  linarith

/-- Finite energy of the actual continuous critical-line mixture. -/
theorem cauchyMellinMixture_energy_summable
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    Summable (fun n : ℕ => paretoWeight n * ‖cauchyMellinMixture δ γ n‖ ^ 2) := by
  rw [cauchyMellinMixture_eq_mellinMode δ γ hδ]
  exact mellinMode_energy_summable _ (cauchyMellinPoint_re_gt_half δ γ hδ)

/-- The exact integral upper bound, with denominator twice the Cauchy scale. -/
theorem cauchyMellinMixture_energy_le
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    (∑' n : ℕ, paretoWeight n * ‖cauchyMellinMixture δ γ n‖ ^ 2) ≤
      ‖cauchyMellinPoint δ γ‖ ^ 2 / (2 * (δ : ℝ)) := by
  rw [cauchyMellinMixture_eq_mellinMode δ γ hδ]
  have h := mellinMode_energy_le _ (cauchyMellinPoint_re_gt_half δ γ hδ)
  simpa only [cauchyMellinPoint_re,
    show 2 * (1 / 2 + (δ : ℝ)) - 1 = 2 * (δ : ℝ) by ring] using h

private theorem one_sub_two_cpow_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    1 - (2 : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have he : (2 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < 2 by norm_num) (-s)
  have hl : (2 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [he, norm_one] at hn
  linarith

theorem cauchyMellinMixture_zero_coordinate_ne_zero
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    cauchyMellinMixture δ γ 0 ≠ 0 := by
  rw [cauchyMellinMixture_eq_mellinMode δ γ hδ]
  have hpoint := cauchyMellinPoint_re_gt_half δ γ hδ
  have h := one_sub_two_cpow_ne_zero_of_re_pos
    (cauchyMellinPoint δ γ) (by linarith)
  simpa only [mellinMode, Nat.cast_zero, zero_add, Complex.one_cpow, one_mul]
    using mul_ne_zero (show (2 : ℂ) ≠ 0 by norm_num) h

theorem cauchyMellinMixture_ne_zero
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    cauchyMellinMixture δ γ ≠ 0 := by
  intro h
  apply cauchyMellinMixture_zero_coordinate_ne_zero δ γ hδ
  simpa using congrFun h 0

/-- Strict positivity is proved from the first actual coordinate. -/
theorem cauchyMellinMixture_energy_pos
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    0 < ∑' n : ℕ, paretoWeight n * ‖cauchyMellinMixture δ γ n‖ ^ 2 := by
  apply (cauchyMellinMixture_energy_summable δ γ hδ).tsum_pos
    (fun n => mul_nonneg (paretoWeight_pos n).le (sq_nonneg _)) 0
  exact mul_pos (paretoWeight_pos 0)
    (pow_pos (norm_pos_iff.mpr (cauchyMellinMixture_zero_coordinate_ne_zero δ γ hδ)) 2)

/-- The multiplier for the single generator `d = 2` cannot vanish to the
left of the line `Re s = 1`. -/
theorem residue_factor_two_ne_zero_of_re_lt_one (s : ℂ) (hs : s.re < 1) :
    1 / (2 : ℂ) - (2 : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have he : (2 : ℂ) ^ (-s) = 1 / 2 := (sub_eq_zero.mp h).symm
  have hn : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < 2 by norm_num) (-s)
  have hl : (1 / 2 : ℝ) < (2 : ℝ) ^ (-s.re) := by
    calc
      _ = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  rw [he] at hn
  norm_num at hn
  linarith

private theorem cauchyMellinPoint_ne_one_of_scale_lt_half
    (δ : ℝ≥0) (γ : ℝ) (hupper : (δ : ℝ) < 1 / 2) :
    cauchyMellinPoint δ γ ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [cauchyMellinPoint_re, Complex.one_re] at hre
  linarith

/-- Actual arithmetic pairing of the Cauchy mixture. -/
theorem cauchyMellinMixture_residuePairing
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) (hupper : (δ : ℝ) < 1 / 2)
    (d : ℕ) (hd : 2 ≤ d) :
    residuePairing (cauchyMellinMixture δ γ) d =
      (1 / (d : ℂ) - (d : ℂ) ^ (-cauchyMellinPoint δ γ)) *
        riemannZeta (cauchyMellinPoint δ γ) := by
  rw [cauchyMellinMixture_eq_mellinMode δ γ hδ]
  have hpoint := cauchyMellinPoint_re_gt_half δ γ hδ
  exact mellinMode_residuePairing _ (by linarith)
    (cauchyMellinPoint_ne_one_of_scale_lt_half δ γ hupper) d hd

/-- The continuous mixture is an annihilator exactly at an actual zeta zero.
This theorem provides no zero-existence hypothesis or conclusion. -/
theorem cauchyMellinMixture_annihilates_iff
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) (hupper : (δ : ℝ) < 1 / 2) :
    (∀ d : ℕ, 2 ≤ d → residuePairing (cauchyMellinMixture δ γ) d = 0) ↔
      riemannZeta (cauchyMellinPoint δ γ) = 0 := by
  constructor
  · intro h
    have h₂ := h 2 (by norm_num)
    rw [cauchyMellinMixture_residuePairing δ γ hδ hupper 2 (by norm_num)] at h₂
    exact (mul_eq_zero.mp h₂).resolve_left
      (residue_factor_two_ne_zero_of_re_lt_one _ (by
        rw [cauchyMellinPoint_re]
        linarith))
  · intro hz d hd
    rw [cauchyMellinMixture_residuePairing δ γ hδ hupper d hd, hz, mul_zero]

/-- The finite-energy mixture coexists with infinite energy in every
individual critical-line coordinate sequence. -/
theorem cauchyMellinMixture_energy_contrast
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    Summable (fun n : ℕ => paretoWeight n * ‖cauchyMellinMixture δ γ n‖ ^ 2) ∧
      ∀ t : ℝ, ¬ Summable (fun n : ℕ => paretoWeight n *
        ‖mellinMode (MellinFrequency.criticalPoint t) n‖ ^ 2) :=
  ⟨cauchyMellinMixture_energy_summable δ γ hδ, criticalMode_not_summable⟩

/-- The representing Cauchy measure satisfies none of the bounded-frequency,
countable-support, or finite-first-moment hypotheses from the earlier
critical-mixture exclusions. -/
theorem cauchyMellinMixture_frequency_obstructions
    (δ : ℝ≥0) (γ : ℝ) (hδ : δ ≠ 0) :
    (∀ T : ℝ, ¬ CompactFrequencyData (1 / 2) T
      (cauchyMeasure γ δ) (fun _ => 1)) ∧
    (∀ S : Set ℝ, S.Countable → ¬ ∀ᵐ t ∂cauchyMeasure γ δ, t ∈ S) ∧
    ¬ Integrable (fun t : ℝ => ‖MellinFrequency.criticalPoint t‖)
      (cauchyMeasure γ δ) := by
  refine ⟨?_, ?_, cauchyMeasure_not_integrable_criticalPoint_norm γ δ hδ⟩
  · intro T hdata
    obtain ⟨_, _, _, _, _, hsupp⟩ := hdata
    exact cauchyMeasure_not_ae_abs_le γ δ hδ T hsupp
  · intro S hS
    exact cauchyMeasure_not_ae_mem_countable γ δ hδ hS

end RiemannResearch.RH.Pareto.SpectralObstruction
