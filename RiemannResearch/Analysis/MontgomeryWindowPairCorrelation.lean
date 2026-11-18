/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryGapBand
import RiemannResearch.Analysis.MontgomeryIntegratedGapDensity
import RiemannResearch.Analysis.MontgomeryGapMesh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Recovering positive gaps from short-window moments

Goldston, Lee, Schettler and Suriajaya, *Pair Correlation Conjecture for the
zeros of the Riemann zeta-function I*, Propositions 1 and 2,
https://doi.org/10.1112/mtk.70127, connect the physical triangle to the
second moment of zeta zero counts in short intervals. The reverse passage
from exact fixed-width sine-model moments to gap counts uses ordered
secants and the ordinary zero count normalization.
-/

noncomputable section

open Filter MeasureTheory Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance

/-- Unfolded triangle at width R for actual zero occurrences up to T. -/
def unfoldedWindowEnergy (T R : ℝ) : ℝ :=
  actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi)))

/-- The second moment predicted by the sine process. -/
def sineWindowEnergy (R : ℝ) : ℝ :=
  R + 2 * ∫ u in (0 : ℝ)..R, sineGapMass u

/-- Precise fixed-width second moment, in zero-count normalization. -/
def SineWindowMoment : Prop :=
  ∀ R : ℝ, 0 < R →
    Tendsto (fun T => unfoldedWindowEnergy T R) atTop (𝓝 (sineWindowEnergy R))

private def collisionMass (T : ℝ) : ℝ :=
  (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))

/-- The model retains the entire signed sine-hole correction to the mean square. -/
theorem sineWindowEnergy_eq (R : ℝ) :
    sineWindowEnergy R = R + R ^ 2 -
      2 * (∫ s in (0 : ℝ)..R, (R - s) * Real.sinc (Real.pi * s) ^ 2) := by
  rw [sineWindowEnergy, integral_sineGapMass]
  ring

/-- Each secant keeps the zero-gap atom and is bounded by the gap counts
at its two endpoints. -/
theorem unfoldedWindowEnergy_secant_bounds {T U R : ℝ}
    (hT : 1 < T) (hU : 0 ≤ U) (hUR : U < R) :
    (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) + 2 * positiveGapMass T U
        ≤ (unfoldedWindowEnergy T R - unfoldedWindowEnergy T U) / (R - U) ∧
    (unfoldedWindowEnergy T R - unfoldedWindowEnergy T U) / (R - U)
        ≤ (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) +
          2 * positiveGapMass T R := by
  have hP := positiveGapMass_mono hT
  have hl := intervalIntegral.integral_mono_on hUR.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => positiveGapMass T U) volume U R)
    hP.intervalIntegrable (fun u hu => hP hu.1)
  have hr := intervalIntegral.integral_mono_on hUR.le hP.intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => positiveGapMass T R) volume U R)
    (fun u hu => hP hu.2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hl hr
  unfold unfoldedWindowEnergy
  rw [physicalTriangle_sub_eq_collision_add_positiveGapBand hT hU hUR.le]
  exact ⟨(le_div_iff₀ (sub_pos.mpr hUR)).2 (by nlinarith only [hl]),
    (div_le_iff₀ (sub_pos.mpr hUR)).2 (by nlinarith only [hr])⟩

private theorem sineWindowEnergy_sub (U R : ℝ) :
    sineWindowEnergy R - sineWindowEnergy U =
      (R - U) + 2 * ∫ u in U..R, sineGapMass u := by
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := sineGapMass) (a := 0) (b := U) (c := R)
    sineGapMass_mono.intervalIntegrable sineGapMass_mono.intervalIntegrable
  unfold sineWindowEnergy
  linarith only [hi]

private theorem local_sineWindowEnergy_secant (x : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ U R : ℝ, U < R → x - δ ≤ U → R ≤ x + δ →
      |(sineWindowEnergy R - sineWindowEnergy U) / (R - U) -
        (1 + 2 * sineGapMass x)| ≤ η := by
  refine ⟨η / 2, by positivity, ?_⟩
  intro U R hUR hU hR
  have hclose (u : ℝ) (hu : u ∈ Icc U R) : |sineGapMass u - sineGapMass x| ≤ η / 2 := by
    apply abs_le.2
    rcases le_total u x with h | h
    · obtain ⟨hl, hr⟩ := sineGapMass_increment_bounds h
      constructor <;> linarith only [hu.1, hU, hl, hr, hη]
    · obtain ⟨hl, hr⟩ := sineGapMass_increment_bounds h
      constructor <;> linarith only [hu.2, hR, hl, hr, hη]
  have hl := intervalIntegral.integral_mono_on hUR.le
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => sineGapMass x - η / 2) volume U R)
    sineGapMass_mono.intervalIntegrable (fun u hu => by
      have h := (abs_le.mp (hclose u hu)).1
      linarith only [h])
  have hr := intervalIntegral.integral_mono_on hUR.le
    sineGapMass_mono.intervalIntegrable
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => sineGapMass x + η / 2) volume U R)
    (fun u hu => by
      have h := (abs_le.mp (hclose u hu)).2
      linarith only [h])
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hl hr
  rw [sineWindowEnergy_sub]
  apply abs_le.2
  constructor
  · have h := (le_div_iff₀ (sub_pos.mpr hUR)).2
        (show (1 + 2 * sineGapMass x - η) * (R - U) ≤
            R - U + 2 * (∫ u in U..R, sineGapMass u) by nlinarith only [hl])
    linarith only [h]
  · have h := (div_le_iff₀ (sub_pos.mpr hUR)).2
        (show R - U + 2 * (∫ u in U..R, sineGapMass u) ≤
            (1 + 2 * sineGapMass x + η) * (R - U) by nlinarith only [hr])
    linarith only [h]

private theorem unfoldedWindowEnergy_zero (T : ℝ) (hT : 1 < T) :
    unfoldedWindowEnergy T 0 = 0 := by
  unfold unfoldedWindowEnergy
  rw [physicalTriangle_eq_collision_add_positive_gaps hT le_rfl]
  simp

private theorem sineWindowEnergy_zero : sineWindowEnergy 0 = 0 := by
  simp [sineWindowEnergy]

private theorem windowMoment_at_nonneg (h : SineWindowMoment) {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun T => unfoldedWindowEnergy T R) atTop (𝓝 (sineWindowEnergy R)) := by
  rcases hR.eq_or_lt with hr | hr
  · subst R
    rw [sineWindowEnergy_zero]
    exact tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      exact (unfoldedWindowEnergy_zero T hT).symm)
  · exact h R hr

private theorem tendsto_window_secant (h : SineWindowMoment) {U R : ℝ} (hU : 0 ≤ U) (hUR : U < R) :
    Tendsto (fun T => (unfoldedWindowEnergy T R - unfoldedWindowEnergy T U) / (R - U))
      atTop (𝓝 ((sineWindowEnergy R - sineWindowEnergy U) / (R - U))) :=
  ((h R (hU.trans_lt hUR)).sub (windowMoment_at_nonneg h hU)).div_const _

/-- Fixed-width sine-model moments determine the equal-ordinate mass,
using the diagonal lower bound from Riemann–von Mangoldt. -/
theorem collision_limit_of_sineWindowMoment (h : SineWindowMoment) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
  change Tendsto collisionMass atTop (𝓝 1)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [tendsto_count_div_mainTerm.eventually (lt_mem_nhds ha),
      eventually_gt_atTop (1 : ℝ)] with T hn hT
    have hC : Ncount 0 T ≤ actualCollision T := by
      rw [actualCollision_eq_count_add_excess T]
      omega
    have hD : 0 ≤ T * Real.log T / (2 * Real.pi) :=
      div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity)
    exact hn.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hC) hD)
  · intro b hb
    obtain ⟨δ, hδ, hmodel⟩ := local_sineWindowEnergy_secant 0
      (show 0 < (b - 1) / 2 by linarith)
    have hM := (abs_le.mp (hmodel 0 δ hδ (by linarith) (by linarith))).2
    have htarget : (sineWindowEnergy δ - sineWindowEnergy 0) / (δ - 0) < b := by
      have hz : sineGapMass 0 = 0 := by simp [sineGapMass]
      rw [hz] at hM
      linarith
    filter_upwards [(tendsto_window_secant h (le_refl 0) hδ).eventually (gt_mem_nhds htarget),
      eventually_gt_atTop (1 : ℝ)] with T hTsec hT
    have hbnd := (unfoldedWindowEnergy_secant_bounds hT (le_refl 0) hδ).1
    have hP := positiveGapMass_nonneg hT 0
    change collisionMass T + 2 * positiveGapMass T 0 ≤ _ at hbnd
    exact (show collisionMass T ≤ _ by linarith only [hbnd, hP]).trans_lt hTsec

/-- Fixed-width sine-model moments imply pointwise ordinate PCC. -/
theorem positiveGap_tendsto_of_sineWindowMoment (h : SineWindowMoment) {x : ℝ}
    (hx : 0 < x) : Tendsto (fun T => positiveGapMass T x) atTop (𝓝 (sineGapMass x)) := by
  have hC : Tendsto collisionMass atTop (𝓝 1) := collision_limit_of_sineWindowMoment h
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨δ, hδ, hmodel⟩ := local_sineWindowEnergy_secant x (sub_pos.mpr ha)
    let U := x - min (x / 2) δ
    have hd : 0 < min (x / 2) δ := lt_min (by positivity) hδ
    have hU : 0 ≤ U := by dsimp [U]; linarith [min_le_left (x / 2) δ]
    have hUx : U < x := by dsimp [U]; linarith
    have hm := (abs_le.mp (hmodel U x hUx
      (by dsimp [U]; linarith [min_le_right (x / 2) δ]) (by linarith))).1
    have hgoal : 2 * a < (sineWindowEnergy x - sineWindowEnergy U) / (x - U) - 1 := by
      linarith only [hm, ha]
    filter_upwards [((tendsto_window_secant h hU hUx).sub hC).eventually (lt_mem_nhds hgoal),
      eventually_gt_atTop (1 : ℝ)] with T hclose hT
    have hbnd := (unfoldedWindowEnergy_secant_bounds hT hU hUx).2
    change _ ≤ collisionMass T + 2 * positiveGapMass T x at hbnd
    linarith only [hbnd, hclose]
  · intro b hb
    obtain ⟨δ, hδ, hmodel⟩ := local_sineWindowEnergy_secant x (sub_pos.mpr hb)
    have hxR : x < x + δ := by linarith
    have hm := (abs_le.mp (hmodel x (x + δ) hxR (by linarith) le_rfl)).2
    have hgoal : (sineWindowEnergy (x + δ) - sineWindowEnergy x) / (x + δ - x) - 1 < 2 * b := by
      linarith only [hm, hb]
    filter_upwards [((tendsto_window_secant h hx.le hxR).sub hC).eventually (gt_mem_nhds hgoal),
      eventually_gt_atTop (1 : ℝ)] with T hclose hT
    have hbnd := (unfoldedWindowEnergy_secant_bounds hT hx.le hxR).1
    change collisionMass T + 2 * positiveGapMass T x ≤ _ at hbnd
    linarith only [hbnd, hclose]

/-- For monotone gap counts, pointwise convergence to the continuous sine
model implies compact-uniform convergence away from zero. -/
theorem positiveGapPCC_of_pointwise
    (h : ∀ u : ℝ, 0 < u → Tendsto (fun T : ℝ => positiveGapMass T u) atTop
      (𝓝 (sineGapMass u))) : PositiveGapPCC := by
  classical
  intro a b ha _ η hη
  let d := min (a / 2) (η / 4)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hda : d ≤ a / 2 := min_le_left _ _
  have hdη : d ≤ η / 4 := min_le_right _ _
  let U := fun x : Set.Icc a b => Set.Ioo ((x : ℝ) - d) ((x : ℝ) + d)
  have hcover : Set.Icc a b ⊆ ⋃ x, U x := by
    intro x hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, ?_⟩
    change x - d < x ∧ x < x + d
    constructor <;> linarith
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  have hevent : ∀ᶠ T : ℝ in atTop, ∀ x ∈ s,
      |positiveGapMass T ((x : ℝ) - d) - sineGapMass ((x : ℝ) - d)| < η / 4 ∧
      |positiveGapMass T ((x : ℝ) + d) - sineGapMass ((x : ℝ) + d)| < η / 4 := by
    apply (Filter.eventually_all_finset s).mpr
    intro x _
    have hx : a ≤ (x : ℝ) := x.2.1
    have hl := Metric.tendsto_nhds.mp (h ((x : ℝ) - d) (by linarith))
      (η / 4) (by linarith)
    have hr := Metric.tendsto_nhds.mp (h ((x : ℝ) + d) (by linarith))
      (η / 4) (by linarith)
    simpa only [Real.dist_eq] using hl.and hr
  filter_upwards [eventually_gt_atTop (1 : ℝ), hevent] with T hT hTs
  intro u hu
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hs hu)
  obtain ⟨hxmem, hxU⟩ := Set.mem_iUnion.mp hx
  change (x : ℝ) - d < u ∧ u < (x : ℝ) + d at hxU
  obtain ⟨heL, heR⟩ := hTs x hxmem
  have hpL := positiveGapMass_mono hT hxU.1.le
  have hpR := positiveGapMass_mono hT hxU.2.le
  have hgL := (sineGapMass_increment_bounds hxU.1.le).2
  have hgR := (sineGapMass_increment_bounds hxU.2.le).2
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith only [(abs_lt.mp heL).1, hpL, hgL, hxU.2, hdη, hη]
  · linarith only [(abs_lt.mp heR).2, hpR, hgR, hxU.1, hdη, hη]

/-- Fixed-width window moments prove the compact-uniform ordinate PCC
without RH or a separate large-window upper moment premise. -/
theorem positiveGapPCC_of_sineWindowMoment (h : SineWindowMoment) : PositiveGapPCC :=
  positiveGapPCC_of_pointwise (fun _ hu => positiveGap_tendsto_of_sineWindowMoment h hu)

private theorem eventually_gap_close_on_window (h : PositiveGapPCC) {R η : ℝ}
    (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc 0 R, |positiveGapMass T u - sineGapMass u| ≤ η := by
  let d := min R (η / 4)
  have hd : 0 < d := lt_min hR (by positivity)
  have hdR : d ≤ R := min_le_left _ _
  have hdη : d ≤ η / 4 := min_le_right _ _
  have hg0 : sineGapMass 0 = 0 := by simp [sineGapMass]
  filter_upwards [h d R hd hdR (η / 4) (by positivity),
    eventually_gt_atTop (1 : ℝ)] with T hTgap hT
  intro u hu
  by_cases hdu : d ≤ u
  · exact (hTgap u ⟨hdu, hu.2⟩).trans (by linarith only [hη])
  · have hud := le_of_lt (lt_of_not_ge hdu)
    have hg := sineGapMass_increment_bounds hu.1
    simp only [hg0, sub_zero] at hg
    have hGd := (sineGapMass_increment_bounds hd.le).2
    simp only [hg0, sub_zero] at hGd
    have hp := positiveGapMass_nonneg hT u
    have hpd := (positiveGapMass_mono hT) hud
    have he := (abs_le.mp (hTgap d ⟨le_rfl, hdR⟩)).2
    exact abs_le.mpr ⟨by linarith only [hp, hg.2, hud, hdη, hη],
      by linarith only [he, hpd, hGd, hg.1, hdη, hη]⟩

private theorem tendsto_integrated_gap_of_PCC (h : PositiveGapPCC) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ => ∫ u in (0 : ℝ)..R, positiveGapMass T u) atTop
      (𝓝 (∫ u in (0 : ℝ)..R, sineGapMass u)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η := ε / (2 * R)
  have hη : 0 < η := div_pos hε (by positivity)
  have hbudget : R * (ε / (2 * R)) = ε / 2 := by field_simp [hR.ne'] <;> ring
  filter_upwards [eventually_gap_close_on_window h hR hη,
    eventually_gt_atTop (1 : ℝ)] with T hgap hT
  have hP : IntervalIntegrable (positiveGapMass T) volume 0 R :=
    (positiveGapMass_mono hT).intervalIntegrable
  have hG : IntervalIntegrable sineGapMass volume 0 R := sineGapMass_mono.intervalIntegrable
  have hlo := intervalIntegral.integral_mono_on hR.le
    (hG.sub intervalIntegrable_const) hP (fun u hu => by
      have hu' := (abs_le.mp (hgap u hu)).1
      linarith only [hu'])
  have hhi := intervalIntegral.integral_mono_on hR.le hP
    (hG.add intervalIntegrable_const) (fun u hu => by
      have hu' := (abs_le.mp (hgap u hu)).2
      linarith only [hu'])
  rw [intervalIntegral.integral_sub hG intervalIntegrable_const] at hlo
  rw [intervalIntegral.integral_add hG intervalIntegrable_const] at hhi
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlo hhi
  rw [hbudget] at hlo hhi
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith only [hlo, hε], by linarith only [hhi, hε]⟩

/-- With the one-sided GLSS second-moment input, ordinary PCC gives
the exact fixed-width sine-model moments. -/
theorem sineWindowMoment_of_positiveGapPCC (h : PositiveGapPCC)
    (hGLSS : ShortWindowSecondMomentUpper) : SineWindowMoment := by
  intro R hR
  have hC := collision_limit_of_positiveGapPCC h hGLSS
  have hI := tendsto_integrated_gap_of_PCC h hR
  have hsum := (hC.const_mul R).add (hI.const_mul 2)
  simp only [mul_one] at hsum
  change Tendsto _ atTop (𝓝 (sineWindowEnergy R)) at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (physicalTriangle_eq_collision_add_positive_gaps hT hR.le).symm

theorem sineWindowMoment_iff_positiveGapPCC (hGLSS : ShortWindowSecondMomentUpper) :
    SineWindowMoment ↔ PositiveGapPCC :=
  ⟨positiveGapPCC_of_sineWindowMoment, fun h => sineWindowMoment_of_positiveGapPCC h hGLSS⟩

end RiemannResearch.Analysis.MontgomeryPositiveGap
