/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoMellinHardyEndpoint
import RiemannResearch.RH.ParetoStepIsometry
import RiemannResearch.RH.ParetoMellinFunctional
import RiemannResearch.Analysis.WeightedMellinHardy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The exact Pareto norm as a Hardy norm on Re(s) > 1/2

Source for the intended norm identification and its squarefree RH consumer:
B. Bagchi, arXiv:math/0607733, Theorems 2 and 7 and Remarks 4 and 8.
The proof uses the project's proved step isometry and Fourier Plancherel
theorem. It supplies the actual critical-half-plane norm identity, rather
than the weaker weighted endpoint identity on Re(s) > 1.

For arbitrary vectors the exact statement uses the supremum over interior
vertical lines. For bounded physical sequences, the critical-line integral
itself is proved to equal the norm. Both statements include every physical
tail coordinate.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.RH.Pareto

/-- Exact complete physical energy at the exponent defining the Pareto norm. -/
theorem complexPhysicalStep_pareto_energy (f : ThresholdHilbert) :
    WeightedMellin.energy (complexPhysicalStep f) 1 = ‖f‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq,
    ← paretoStep_energy_identity _ (hilbertSequence_square_summable f)]
  unfold WeightedMellin.energy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hp : x ^ (-(1 : ℝ) - 1) = 1 / x ^ 2 := by
    norm_num [Real.rpow_neg hx0.le]
  simp only [complexPhysicalStep, Complex.norm_real, Real.norm_eq_abs, sq_abs, hp]
  ring

/-- The transform is genuinely H2 in the full critical half-plane. -/
theorem paretoMellin_hardy_critical (f : ThresholdHilbert) :
    WeightedMellin.HardyH2 (paretoMellin f) (1 / 2) := by
  have h := WeightedMellin.energy_to_hardy (complexPhysicalStep_finiteEnergy f)
  simpa only [complexPhysicalStep_transform] using h

/-- Exact supremum identity. The Fourier convention is s = σ + 2πiw. -/
theorem paretoMellin_norm_sq_isLUB (f : ThresholdHilbert) :
    IsLUB {v : ℝ | ∃ σ : ℝ, (1 / 2 : ℝ) < σ ∧
      v = ∫ w : ℝ, ‖paretoMellin f (WeightedMellin.verticalPoint σ w)‖ ^ 2}
      (‖f‖ ^ 2) := by
  have h := WeightedMellin.hardy_energy_isLUB (complexPhysicalStep_finiteEnergy f)
  simpa only [complexPhysicalStep_transform, complexPhysicalStep_pareto_energy] using h

/-- Uniform interior-line bounds are equivalent to a complete physical norm bound. -/
theorem paretoMellin_norm_sq_le_iff (f : ThresholdHilbert) (B : ℝ) :
    ‖f‖ ^ 2 ≤ B ↔ ∀ σ : ℝ, (1 / 2 : ℝ) < σ →
      (∫ w : ℝ, ‖paretoMellin f (WeightedMellin.verticalPoint σ w)‖ ^ 2) ≤ B := by
  have h := paretoMellin_norm_sq_isLUB f
  constructor
  · intro hb σ hσ
    exact (h.1 ⟨σ, hσ, rfl⟩).trans hb
  · intro hb
    apply h.2
    rintro v ⟨σ, hσ, rfl⟩
    exact hb σ hσ

/-- Bounded physical sequences have finite energy at every positive exponent. -/
theorem complexPhysicalStep_finiteEnergy_of_bounded (f : ThresholdHilbert)
    (C : ℝ) (hC : ∀ n : ℕ, |hilbertSequence f n| ≤ C)
    {s : ℝ} (hs : 0 < s) :
    WeightedMellin.FiniteEnergy (complexPhysicalStep f) s := by
  have hm : Measurable (fun x : ℝ => ‖complexPhysicalStep f x‖ ^ 2 * x ^ (-s - 1)) :=
    ((complexPhysicalStep_measurable f).norm.pow_const 2).mul (measurable_id.pow_const _)
  refine ⟨complexPhysicalStep_measurable f, ?_⟩
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1)
    (by norm_num : (0 : ℝ) < 1)).const_mul (C ^ 2)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := le_trans zero_le_one hx.le
  have hnorm : ‖complexPhysicalStep f x‖ ≤ C := by
    simpa only [complexPhysicalStep, Complex.norm_real, Real.norm_eq_abs] using hC ⌊x⌋₊
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx0 _))]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
    (Real.rpow_nonneg hx0 _)

/-- For bounded physical vectors the ordinary critical-line integral itself
equals the full norm. No abstract boundary-trace assumption is required. -/
theorem paretoMellin_critical_line_norm (f : ThresholdHilbert)
    (C : ℝ) (hC : ∀ n : ℕ, |hilbertSequence f n| ≤ C) :
    (1 / (2 * Real.pi)) *
      (∫ t : ℝ, ‖paretoMellin f ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
      ‖f‖ ^ 2 := by
  have hf := complexPhysicalStep_finiteEnergy_of_bounded f C hC
    (by norm_num : (0 : ℝ) < 1 / 2)
  have h := WeightedMellin.angular_plancherel hf (σ := 1 / 2) (by norm_num)
  simpa only [complexPhysicalStep_transform,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, complexPhysicalStep_pareto_energy,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h

end RiemannResearch.RH.Pareto
