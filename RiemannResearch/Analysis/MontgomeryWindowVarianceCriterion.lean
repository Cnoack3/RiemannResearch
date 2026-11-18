/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroWindowVariance
import RiemannResearch.Analysis.MontgomeryWindowPairCorrelation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A count-variance input for Montgomery pair correlation

Goldston, Lee, Schettler and Suriajaya, *Pair correlation conjecture for the
zeros of the Riemann zeta-function I*, Propositions 1 and 2,
https://doi.org/10.1112/mtk.70127, connect zero-count second moments to
the triangular pair statistic and to increments of the zeta argument.
Here the count is formed from the actual multiplicity copies in the cutoff.
It has an exact mean-square decomposition and its normalized fixed-width
variance gives a sufficient input for ordinate pair correlation. Positive
rational widths suffice. The reverse implication takes the existing
one-sided GLSS moment bound as an explicit premise.
-/

noncomputable section

open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

open ActualZeroCollisionCertificate ActualZeroOrdinate ActualZeroWindowVariance

/-- A common positive lower bound for all positive ordinates. Only finiteness
of the cutoff at height one is used. -/
private theorem exists_ordinate_floor :
    ∃ d : ℝ, 0 < d ∧ ∀ T : ℝ, ∀ c : Copies T, d ≤ c.1.1.im := by
  classical
  have hf : ∀ s : Finset ℂ, (∀ ρ ∈ s, 0 < ρ.im) →
      ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ ρ ∈ s, d ≤ ρ.im := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, zero_lt_one, le_rfl, by simp⟩
    | insert ρ s hnot ih =>
      intro hs
      obtain ⟨d, hd, hd₁, hsmall⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
      have hρ := hs ρ (Finset.mem_insert_self _ _)
      refine ⟨min d ρ.im, lt_min hd hρ, (min_le_left _ _).trans hd₁, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hsmall z hz)
  obtain ⟨d, hd, hd₁, hsmall⟩ :=
    hf (cutoff 1) (fun ρ hρ => (mem_cutoff.mp hρ).2.1)
  refine ⟨d, hd, ?_⟩
  intro T c
  have hc := mem_cutoff.mp c.1.2
  by_cases h : c.1.1.im ≤ 1
  · exact hsmall c.1.1 (mem_cutoff.mpr ⟨hc.1, hc.2.1, h⟩)
  · exact hd₁.trans (le_of_not_ge h)

/-- The exact mean of the finite-window counting function on the height
interval. The width variable is in unfolded units. -/
def unfoldedWindowMean (T R : ℝ) : ℝ :=
  (Ncount 0 T : ℝ) * (R / (Real.log T / (2 * Real.pi))) / T

/-- Normalized variance with the actual finite-height mean. -/
def unfoldedWindowVariance (T R : ℝ) : ℝ :=
  (∫ t : ℝ, actualCenteredCount T (R / (Real.log T / (2 * Real.pi)))
    (unfoldedWindowMean T R) t ^ 2) / T

/-- The actual mean at a fixed width converges by Riemann–von Mangoldt. -/
theorem unfoldedWindowMean_tendsto (R : ℝ) :
    Tendsto (fun T => unfoldedWindowMean T R) atTop (𝓝 R) := by
  have h := tendsto_count_div_mainTerm.const_mul R
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hTp : 0 < T := by linarith
  have hL := Real.log_pos hT
  unfold unfoldedWindowMean
  field_simp [hTp.ne', hL.ne', Real.pi_ne_zero]
  <;> ring

/-- Eventually the physical width lies below the common positive lower
bound of the ordinates. This removes the geometric premise from the exact
mean-square decomposition at each fixed unfolded width. -/
theorem eventually_unfoldedWindowEnergy_eq_mean_sq_add_variance {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop,
      unfoldedWindowEnergy T R = unfoldedWindowMean T R ^ 2 + unfoldedWindowVariance T R := by
  obtain ⟨d, hd, hfloor⟩ := exists_ordinate_floor
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.pi * R / d)] with T hT hL
  have hTp : 0 < T := by linarith
  have hscale : 0 < Real.log T / (2 * Real.pi) := div_pos (Real.log_pos hT) (by positivity)
  have hwidth : R / (Real.log T / (2 * Real.pi)) ≤ d := by
    apply (div_le_iff₀ hscale).2
    have h := (div_le_iff₀ hd).1 hL
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith only [h]
  have hmean : (Ncount 0 T : ℝ) * (R / (Real.log T / (2 * Real.pi))) =
      T * unfoldedWindowMean T R := by
    unfold unfoldedWindowMean
    field_simp [hTp.ne']
    <;> ring
  exact actual_triangle_eq_mean_sq_add_variance T _ _ hTp (div_nonneg hR hscale.le)
    (fun c => hwidth.trans (hfloor T c)) hmean

/-- At fixed width, the sine-model triangle and centered variance
predictions are equivalent with the full signed sine-hole term. -/
theorem unfoldedWindowVariance_tendsto_iff {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun T => unfoldedWindowVariance T R) atTop
      (𝓝 (sineWindowEnergy R - R ^ 2)) ↔
    Tendsto (fun T => unfoldedWindowEnergy T R) atTop (𝓝 (sineWindowEnergy R)) := by
  have hm := (unfoldedWindowMean_tendsto R).pow 2
  have he := eventually_unfoldedWindowEnergy_eq_mean_sq_add_variance hR
  constructor
  · intro h
    have hh := hm.add h
    rw [show R ^ 2 + (sineWindowEnergy R - R ^ 2) = sineWindowEnergy R by ring] at hh
    exact hh.congr' (he.mono fun T hT => hT.symm)
  · intro h
    exact (h.sub hm).congr' (he.mono fun T hT => by rw [hT]; ring)

/-- Checking the fixed-width triangle law on the positive rationals suffices
by monotonicity of the finite triangle and continuity of the target. -/
theorem sineWindowMoment_of_rational
    (h : ∀ R : ℚ, 0 < R →
      Tendsto (fun T => unfoldedWindowEnergy T (R : ℝ)) atTop (𝓝 (sineWindowEnergy R))) :
    SineWindowMoment := by
  have hc : Continuous sineWindowEnergy := by
    unfold sineWindowEnergy
    exact continuous_id.add ((intervalIntegral.continuous_primitive
      (fun a b => sineGapMass_mono.intervalIntegrable (a := a) (b := b)) 0).const_mul 2)
  have hmono (T : ℝ) (hT : 1 < T) : Monotone (unfoldedWindowEnergy T) := by
    intro a b hab
    unfold unfoldedWindowEnergy actualPhysicalTriangleEnergy
    apply div_le_div_of_nonneg_right _ (by linarith)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hscale : 0 ≤ Real.log T / (2 * Real.pi) := by
      exact div_nonneg (Real.log_pos hT).le (by positivity)
    exact max_le_max_right _ (sub_le_sub_right (div_le_div_of_nonneg_right hab hscale) _)
  intro R hR
  have hcont : ContinuousAt sineWindowEnergy R := hc.continuousAt
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨d, hd, hn⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds ha))
    let ε := min (d / 2) (R / 2)
    have hε : 0 < ε := lt_min (by positivity) (by positivity)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show R - ε < R by linarith)
    change R - min (d / 2) (R / 2) < (q : ℝ) at hq₁
    have hq : 0 < q := by
      have hq₀ : (0 : ℝ) < (q : ℝ) := by linarith [min_le_right (d / 2) (R / 2)]
      exact_mod_cast hq₀
    have hdist : dist (q : ℝ) R < d := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hq₂.le)]
      linarith [min_le_left (d / 2) (R / 2)]
    filter_upwards [(h q hq).eventually (lt_mem_nhds (hn hdist)),
      eventually_gt_atTop (1 : ℝ)] with T ht hT
    exact ht.trans_le (hmono T hT hq₂.le)
  · intro a ha
    obtain ⟨d, hd, hn⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (gt_mem_nhds ha))
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show R < R + d / 2 by linarith)
    have hq : 0 < q := by exact_mod_cast hR.trans hq₁
    have hdist : dist (q : ℝ) R < d := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hq₁.le)]
      linarith
    filter_upwards [(h q hq).eventually (gt_mem_nhds (hn hdist)),
      eventually_gt_atTop (1 : ℝ)] with T ht hT
    exact (hmono T hT hq₁.le).trans_lt ht

/-- The microscopic variance of actual zero counts at positive rational
widths. Its sine-model target retains the signed sinc-square correction. -/
def RationalSineWindowVariance : Prop :=
  ∀ R : ℚ, 0 < R →
    Tendsto (fun T => unfoldedWindowVariance T (R : ℝ)) atTop
      (𝓝 (sineWindowEnergy R - (R : ℝ) ^ 2))

theorem sineWindowMoment_of_rationalSineWindowVariance (h : RationalSineWindowVariance) :
    SineWindowMoment := by
  apply sineWindowMoment_of_rational
  intro R hR
  have hpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  exact (unfoldedWindowVariance_tendsto_iff hpos.le).1 (h R hR)

/-- The rational-width variance prediction alone implies ordinary PCC. -/
theorem positiveGapPCC_of_rationalSineWindowVariance (h : RationalSineWindowVariance) :
    PositiveGapPCC :=
  positiveGapPCC_of_sineWindowMoment (sineWindowMoment_of_rationalSineWindowVariance h)

/-- A rational-width variance provider is sufficient for ordinary PCC.
The forward implication uses the published one-sided moment estimate. -/
theorem positiveGapPCC_iff_rationalSineWindowVariance (hGLSS : ShortWindowSecondMomentUpper) :
    PositiveGapPCC ↔ RationalSineWindowVariance := by
  constructor
  · intro h R hR
    have hpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
    exact (unfoldedWindowVariance_tendsto_iff hpos.le).2
      ((sineWindowMoment_iff_positiveGapPCC hGLSS).2 h R hpos)
  · exact positiveGapPCC_of_rationalSineWindowVariance

/-- The same variance input also forces density one of simple critical zeros. -/
theorem density_one_of_rationalSineWindowVariance (h : RationalSineWindowVariance) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  density_one_of_collision_limit
    (collision_limit_of_sineWindowMoment (sineWindowMoment_of_rationalSineWindowVariance h))

end RiemannResearch.Analysis.MontgomeryPositiveGap
