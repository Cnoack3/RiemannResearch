/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-strip concentration and qualitative actual-zero phase comparison

This module isolates a weaker input than a uniform Selberg estimate for
qualitative fixed-frequency sampling. All counts are actual positive-height
zeta zeros with their analytic multiplicities and original count normalizer.

The classical analytic context is Hlawka's unconditional equidistribution,
as recorded in Ford--Zaharescu, "On the distribution of imaginary parts of
zeros of the Riemann zeta function", introduction, pp. 1--2:
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf . The elementary
concentration argument here does not supply the analytic density theorem.

Fixed-strip concentration is equivalent to normalized horizontal second
moment tending to zero. The already proved reflection estimate then removes
the horizontal weight for every fixed frequency. No RH assumption, moving
strip rate, growing-frequency estimate, or new axiom is used.
-/

noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Each fixed positive strip captures asymptotically all zero copies.
This is an explicit analytic premise, not a provider theorem. -/
def FixedStripConcentration : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Tendsto (fun T : ℝ => strictTail T δ / (Ncount 0 T : ℝ)) atTop (𝓝 0)

/-- Complete finite head/tail estimate for horizontal second moment. -/
theorem horizontalEnergy_le_fixedStrip (T δ : ℝ) (hδ : 0 ≤ δ) :
    horizontalEnergy T ≤ δ ^ 2 * (Ncount 0 T : ℝ) +
      (1 / 4 : ℝ) * strictTail T δ := by
  have hpoint : ∀ ρ ∈ cutoff T, (ρ.re - 1 / 2) ^ 2 ≤
      δ ^ 2 + (if δ < |ρ.re - 1 / 2| then (1 : ℝ) else 0) * (1 / 4) := by
    intro ρ hρ
    by_cases hb : δ < |ρ.re - 1 / 2|
    · rw [if_pos hb, one_mul]
      have hs : |ρ.re - 1 / 2| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (displacement_lt_half hρ).le
      nlinarith [sq_abs (ρ.re - 1 / 2), sq_nonneg δ]
    · rw [if_neg hb, zero_mul, add_zero]
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (ρ.re - 1 / 2)) hδ).mpr (le_of_not_gt hb)
  have hconst : realSum T (fun _ : ℂ => δ ^ 2) = (Ncount 0 T : ℝ) * δ ^ 2 := by
    simpa only [one_mul, realSum_one] using
      realSum_mul_const T (fun _ => (1 : ℝ)) (δ ^ 2)
  calc
    horizontalEnergy T ≤ realSum T (fun ρ => δ ^ 2 +
        (if δ < |ρ.re - 1 / 2| then (1 : ℝ) else 0) * (1 / 4)) :=
      realSum_mono T _ _ hpoint
    _ = _ := by
      rw [realSum_add, hconst, realSum_mul_const, ← strictTail_eq_realSum]
      ring

/-- Original-count normalization, including empty cutoffs. -/
theorem relativeEnergy_le_fixedStrip (T δ : ℝ) (hδ : 0 ≤ δ) :
    relativeEnergy T ≤ δ ^ 2 +
      (1 / 4 : ℝ) * (strictTail T δ / (Ncount 0 T : ℝ)) := by
  by_cases hN : Ncount 0 T = 0
  · simp only [relativeEnergy, hN, Nat.cast_zero, div_zero, mul_zero, add_zero]
    positivity
  · have hN0 : (0 : ℝ) < (Ncount 0 T : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    calc
      relativeEnergy T ≤
          (δ ^ 2 * (Ncount 0 T : ℝ) + (1 / 4 : ℝ) * strictTail T δ) /
            (Ncount 0 T : ℝ) :=
        div_le_div_of_nonneg_right (horizontalEnergy_le_fixedStrip T δ hδ) hN0.le
      _ = _ := by field_simp [ne_of_gt hN0] <;> ring

/-- Finite Markov bound with the original multiplicity-weighted count. -/
theorem fixedStrip_mul_sq_le_horizontalEnergy (T δ : ℝ) (hδ : 0 ≤ δ) :
    δ ^ 2 * strictTail T δ ≤ horizontalEnergy T := by
  have hpoint : ∀ ρ ∈ cutoff T,
      (if δ < |ρ.re - 1 / 2| then (1 : ℝ) else 0) * δ ^ 2 ≤
        (ρ.re - 1 / 2) ^ 2 := by
    intro ρ hρ
    by_cases hb : δ < |ρ.re - 1 / 2|
    · rw [if_pos hb, one_mul]
      simpa only [sq_abs] using
        (sq_le_sq₀ hδ (abs_nonneg (ρ.re - 1 / 2))).mpr hb.le
    · rw [if_neg hb, zero_mul]
      exact sq_nonneg _
  have h := realSum_mono T _ _ hpoint
  rw [realSum_mul_const, ← strictTail_eq_realSum] at h
  simpa only [horizontalEnergy, mul_comm] using h

/-- A fixed-strip concentration assumption gives the vanishing second moment;
the strip threshold is chosen after the desired error and is held fixed. -/
theorem relativeEnergy_tendsto_zero_of_fixedStrip
    (hconcentration : FixedStripConcentration) :
    Tendsto relativeEnergy atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := Real.sqrt (ε / 2)
  have hδ : 0 < δ := Real.sqrt_pos.2 (by positivity)
  have hδsq : δ ^ 2 = ε / 2 := Real.sq_sqrt (by positivity)
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp (hconcentration δ hδ) ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have htail := hT₀ T hT
  have ht0 : 0 ≤ strictTail T δ / (Ncount 0 T : ℝ) :=
    div_nonneg (strictTail_nonneg _ _) (Nat.cast_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0] at htail
  have hE0 : 0 ≤ relativeEnergy T :=
    div_nonneg (horizontalEnergy_nonneg _) (Nat.cast_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hE0]
  have hbound := relativeEnergy_le_fixedStrip T δ hδ.le
  rw [hδsq] at hbound
  linarith

/-- The converse needs no zero-count positivity: Markov's inequality works
with the same zero convention at empty cutoffs. -/
theorem fixedStrip_of_relativeEnergy_tendsto_zero
    (hE : Tendsto relativeEnergy atTop (𝓝 0)) : FixedStripConcentration := by
  intro δ hδ
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have ht : Tendsto (fun T : ℝ => relativeEnergy T / δ ^ 2) atTop (𝓝 0) := by
    simpa using hE.div_const (δ ^ 2)
  apply squeeze_zero
    (fun T => div_nonneg (strictTail_nonneg T δ) (Nat.cast_nonneg _)) _ ht
  intro T
  apply (le_div_iff₀ hδsq).mpr
  have h := div_le_div_of_nonneg_right
    (fixedStrip_mul_sq_le_horizontalEnergy T δ hδ.le)
    (Nat.cast_nonneg (Ncount 0 T) : (0 : ℝ) ≤ (Ncount 0 T : ℝ))
  simpa only [relativeEnergy, mul_div_assoc, mul_comm] using h

theorem fixedStripConcentration_iff_relativeEnergy_tendsto_zero :
    FixedStripConcentration ↔ Tendsto relativeEnergy atTop (𝓝 0) :=
  ⟨relativeEnergy_tendsto_zero_of_fixedStrip, fixedStrip_of_relativeEnergy_tendsto_zero⟩

/-- Qualitative fixed-frequency removal of the horizontal exponential weight.
This is normalized by the zero count, rather than by height. -/
theorem tendsto_normalized_ordinate_landau_error_of_fixedStrip
    (u : ℝ) (hconcentration : FixedStripConcentration) :
    Tendsto (fun T : ℝ => ordinateSum T u / (Ncount 0 T : ℂ) -
      landauSum T u / (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have ht : Tendsto (fun T : ℝ =>
      (u ^ 2 * Real.exp (|u| / 2)) * relativeEnergy T) atTop (𝓝 0) := by
    simpa using (relativeEnergy_tendsto_zero_of_fixedStrip hconcentration).const_mul
      (u ^ 2 * Real.exp (|u| / 2))
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun T => normalized_ordinate_landau_error T u) ht

/-- A separately supplied normalized Landau limit transfers to actual phases.
The analytic density and Landau premises remain explicit. -/
theorem tendsto_normalized_ordinate_of_fixedStrip
    (u : ℝ) (hconcentration : FixedStripConcentration)
    (hlandau : Tendsto (fun T : ℝ => landauSum T u / (Ncount 0 T : ℂ))
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ordinateSum T u / (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
  simpa only [sub_add_cancel, zero_add] using
    (tendsto_normalized_ordinate_landau_error_of_fixedStrip u hconcentration).add hlandau

end RiemannResearch.Analysis.ActualZeroOrdinate
