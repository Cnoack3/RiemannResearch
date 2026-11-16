/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ResidueCalcOnRectangles
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Passing finite rectangle identities to full vertical integrals

A bound by B / (1 + t^2), only outside a fixed compact height interval,
suffices for both horizontal limits. Continuity on a vertical line supplies
its compact middle and hence its absolute integrability. The normalization
retains dz = i dt, giving 1 / (2 pi) for the real-line parameterization.

Source: the finite-rectangle and improper-integral proof strategy in
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The general lemmas expose the analytic hypotheses needed by the Estermann consumer.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace MeasureTheory
/-- Continuity handles the compact middle; a quadratic tail bound gives absolute integrability. -/
theorem integrable_of_continuous_of_cauchy_tail {f : ℝ → ℂ} (hf : Continuous f)
    {B T₀ : ℝ}
    (hbound : ∀ t : ℝ, T₀ ≤ |t| → ‖f t‖ ≤ B * (1 + t ^ 2)⁻¹) :
    Integrable f := by
  have hc : Continuous (fun t : ℝ => ‖f t‖ * (1 + t ^ 2)) := by fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-T₀) T₀) hc.continuousOn
  apply (integrable_inv_one_add_sq.const_mul (max B M)).mono' hf.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  by_cases ht : T₀ ≤ |t|
  · exact (hbound t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left B M) (by positivity))
  · have ht' : t ∈ Icc (-T₀) T₀ := by
      have hh := abs_lt.mp (lt_of_not_ge ht)
      exact ⟨hh.1.le, hh.2.le⟩
    have hb : ‖f t‖ * (1 + t ^ 2) ≤ max B M := by
      exact ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM t ht')).trans
        (le_max_right B M)
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)).mpr hb
end MeasureTheory

namespace Complex
/-- Both remote horizontal sides tend to zero under one bound on the whole strip. -/
theorem tendsto_horizontal_integrals_zero_of_cauchy_tail
    {f : ℂ → ℂ} {a b B T₀ : ℝ} (hab : a ≤ b)
    (hbound : ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖f ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹) :
    Tendsto (fun T : ℝ => HIntegral f a b T) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => HIntegral f a b (-T)) atTop (𝓝 0) := by
  have hH (T : ℝ) (hT : T₀ ≤ |T|) :
      ‖HIntegral f a b T‖ ≤ (B * (1 + T ^ 2)⁻¹) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    exact hbound r (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hr) T hT
  have hdecay : Tendsto (fun T : ℝ => (1 + T ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun T : ℝ => by linarith : ∀ T : ℝ, T ^ 2 ≤ 1 + T ^ 2)
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)))
  have hlim : Tendsto (fun T : ℝ => (B * (1 + T ^ 2)⁻¹) * |b - a|) atTop (𝓝 0) := by
    simpa using (hdecay.const_mul B).mul_const |b - a|
  constructor
  · exact squeeze_zero_norm' ((eventually_ge_atTop T₀).mono
      (fun T hT => hH T (hT.trans (le_abs_self T)))) hlim
  · exact squeeze_zero_norm' ((eventually_ge_atTop T₀).mono (fun T hT => by
      simpa only [neg_sq] using hH (-T)
        (by simpa only [abs_neg] using hT.trans (le_abs_self T)))) hlim

/-- Pass an eventual exact rectangle identity to the two full vertical integrals.
The factor is 1/(2 pi) because the vertical variable is real and dz = i dt. -/
theorem mellin_vertical_eq_of_rectangle_of_cauchy_tail
    {f : ℂ → ℂ} {a b B T₀ : ℝ} {R : ℂ} (hab : a ≤ b)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * I)))
    (hbound : ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖f ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹)
    (hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' f ((a : ℂ) - T * I) ((b : ℂ) + T * I) = R) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, f ((b : ℂ) + t * I)) =
      R + (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, f ((a : ℂ) + t * I)) := by
  obtain ⟨hpos, hneg⟩ := tendsto_horizontal_integrals_zero_of_cauchy_tail hab hbound
  have hva := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hvb := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hlimrect :=
    (((hneg.sub hpos).add (hvb.const_mul I)).sub (hva.const_mul I)).const_mul
      (2 * (Real.pi : ℂ) * I)⁻¹
  have hrect' : ∀ᶠ T : ℝ in atTop,
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (HIntegral f a b (-T) - HIntegral f a b T +
          I * (∫ t in -T..T, f ((b : ℂ) + t * I)) -
          I * (∫ t in -T..T, f ((a : ℂ) + t * I))) = R := by
    filter_upwards [hrect] with T hT
    simpa [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] using hT
  have he := tendsto_nhds_unique hlimrect
    (tendsto_const_nhds.congr' (hrect'.mono (fun _ h => h.symm)))
  simp only [sub_self, zero_add] at he
  have hn : (2 * (Real.pi : ℂ) * I)⁻¹ *
      (I * (∫ t : ℝ, f ((b : ℂ) + t * I)) -
        I * (∫ t : ℝ, f ((a : ℂ) + t * I))) =
      (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, f ((b : ℂ) + t * I)) -
        (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ, f ((a : ℂ) + t * I)) := by
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [hn] at he
  exact sub_eq_iff_eq_add.mp he
end Complex
