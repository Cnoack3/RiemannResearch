/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryCauchyGapMesh
import RiemannResearch.Analysis.MontgomeryGapBand
import RiemannResearch.Analysis.MontgomeryIntegratedGapDensity
import RiemannResearch.Analysis.MontgomeryGapMesh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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

private theorem sineWindowEnergy_adjacent_secants (R h : ℝ) (hh : 0 < h) :
    (1 + 2 * sineGapMass R - h) * h ≤ sineWindowEnergy R - sineWindowEnergy (R - h) ∧
      sineWindowEnergy (R + h) - sineWindowEnergy R ≤ (1 + 2 * sineGapMass R + h) * h := by
  let f := fun u : ℝ => sineGapMass R + (u - R)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hI (U V : ℝ) : (∫ u in U..V, f u) =
      (V - U) * (sineGapMass R - R) + (V ^ 2 - U ^ 2) / 2 := by
    have hsum := intervalIntegral.integral_add (f := fun _ : ℝ => sineGapMass R - R)
      (g := fun u : ℝ => u) (μ := volume) intervalIntegrable_const
      (continuous_id.intervalIntegrable U V)
    rw [show f = (fun u => (sineGapMass R - R) + u) by funext u; dsimp [f]; ring,
      hsum, intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul] <;> ring
  have hlo := intervalIntegral.integral_mono_on (μ := volume)
    (show R - h ≤ R by linarith) (hf.intervalIntegrable _ _)
    sineGapMass_mono.intervalIntegrable (fun u hu => by
      have hu' := (sineGapMass_increment_bounds hu.2).2
      dsimp [f]
      linarith only [hu'])
  have hhi := intervalIntegral.integral_mono_on (μ := volume)
    (show R ≤ R + h by linarith) sineGapMass_mono.intervalIntegrable
    (hf.intervalIntegrable _ _) (fun u hu => by
      have hu' := (sineGapMass_increment_bounds hu.1).2
      dsimp [f]
      linarith only [hu'])
  rw [hI] at hlo hhi
  constructor
  · rw [sineWindowEnergy_sub]
    nlinarith only [hlo]
  · rw [sineWindowEnergy_sub]
    nlinarith only [hhi]

/-- The two neighboring window errors bound the signed gap discrepancy,
retaining the collision excess separately. The sine-model secant error
uses the integral of the affine Lipschitz bound. -/
theorem signed_gap_error_le_window_secants {T R h : ℝ}
    (hT : 1 < T) (hh : 0 < h) (hR : h ≤ R) :
    let e := fun u => unfoldedWindowEnergy T u - sineWindowEnergy u
    |positiveGapMass T R - sineGapMass R +
      ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) - 1) / 2| ≤
        h / 2 + max |e (R + h) - e R| |e R - e (R - h)| / (2 * h) := by
  let e := fun u => unfoldedWindowEnergy T u - sineWindowEnergy u
  let B := max |e (R + h) - e R| |e R - e (R - h)|
  let A := positiveGapMass T R - sineGapMass R + (collisionMass T - 1) / 2
  change |A| ≤ h / 2 + B / (2 * h)
  have hR₀ : 0 ≤ R := hh.le.trans hR
  have hmodel := sineWindowEnergy_adjacent_secants R h hh
  have hleft := (unfoldedWindowEnergy_secant_bounds hT (sub_nonneg.mpr hR)
    (show R - h < R by linarith)).2
  have hright := (unfoldedWindowEnergy_secant_bounds hT hR₀ (show R < R + h by linarith)).1
  rw [show R - (R - h) = h by ring] at hleft
  rw [show R + h - R = h by ring] at hright
  have hlo := (div_le_iff₀ hh).mp hleft
  have hhi := (le_div_iff₀ hh).mp hright
  have hEL : -B ≤ e R - e (R - h) := (abs_le.mp (le_max_right _ _)).1
  have hER : e (R + h) - e R ≤ B := (abs_le.mp (le_max_left _ _)).2
  have hbottom : -(h ^ 2 + B) ≤ A * (2 * h) := by
    dsimp only [e] at hEL
    dsimp [A, collisionMass]
    nlinarith only [hmodel.1, hEL, hlo]
  have htop : A * (2 * h) ≤ h ^ 2 + B := by
    dsimp only [e] at hER
    dsimp [A, collisionMass]
    nlinarith only [hmodel.2, hER, hhi]
  have hh₂ : 0 < 2 * h := by positivity
  rw [show h / 2 + B / (2 * h) = (h ^ 2 + B) / (2 * h) by field_simp [hh.ne']]
  apply abs_le.2
  exact ⟨by rw [← neg_div]; exact (div_le_iff₀ hh₂).2 hbottom, (le_div_iff₀ hh₂).2 htop⟩

/-- A common error at the three widths yields the usual finite-difference
bound with full error amplification. -/
theorem signed_gap_error_le_of_window_errors {T R h E : ℝ}
    (hT : 1 < T) (hh : 0 < h) (hR : h ≤ R)
    (hl : |unfoldedWindowEnergy T (R - h) - sineWindowEnergy (R - h)| ≤ E)
    (hm : |unfoldedWindowEnergy T R - sineWindowEnergy R| ≤ E)
    (hr : |unfoldedWindowEnergy T (R + h) - sineWindowEnergy (R + h)| ≤ E) :
    |positiveGapMass T R - sineGapMass R +
      ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) - 1) / 2| ≤
        h / 2 + E / h := by
  let e := fun u => unfoldedWindowEnergy T u - sineWindowEnergy u
  have htri (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  have heR : |e (R + h) - e R| ≤ E + E := (htri _ _).trans (add_le_add hr hm)
  have heL : |e R - e (R - h)| ≤ E + E := (htri _ _).trans (add_le_add hm hl)
  apply (signed_gap_error_le_window_secants hT hh hR).trans
  refine add_le_add le_rfl ?_
  calc
    _ ≤ (E + E) / (2 * h) := div_le_div_of_nonneg_right (max_le heR heL) (by positivity)
    _ = _ := by ring

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

/-- The measured equal-ordinate atom and the signed positive-gap deficit give
the complete error in the physical window moment at each positive width. -/
theorem unfoldedWindowEnergy_sub_sine_eq_collision_sub_deficit {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) :
    unfoldedWindowEnergy T R - sineWindowEnergy R =
      R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) -
        1 - integratedGapDeficit T R) := by
  rw [unfoldedWindowEnergy, physicalTriangle_eq_collision_add_positive_gaps hT hR.le,
    sineWindowEnergy, integratedGapDeficit]
  field_simp [hR.ne'] <;> ring

/-- Monotonicity bounds a band integral between its endpoint masses.
These comparisons also apply to the sine-model cumulative gap mass. -/
private theorem gap_band_bounds {f : ℝ → ℝ} (hf : Monotone f) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * f a ≤ ∫ u in a..b, f u ∧
      (∫ u in a..b, f u) ≤ (b - a) * f b := by
  have hl := intervalIntegral.integral_mono_on (μ := volume) hab
    (f := fun _ : ℝ => f a) intervalIntegrable_const hf.intervalIntegrable
    (fun u hu => hf hu.1)
  have hr := intervalIntegral.integral_mono_on (μ := volume) hab
    hf.intervalIntegrable (g := fun _ : ℝ => f b) intervalIntegrable_const
    (fun u hu => hf hu.2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using And.intro hl hr

/-- Positive-gap PCC is equivalent to a countable family of collision-subtracted
triangle limits. The normalization removes the exact equal-ordinate count at every
height, so both implications hold without a large-window second-moment premise. -/
theorem positiveGapPCC_iff_rationalIntegratedGapDeficit :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => integratedGapDeficit T q) atTop (𝓝 0) := by
  constructor
  · intro h q hq
    have hlim := (tendsto_const_nhds (x := ∫ u in (0 : ℝ)..(q : ℝ), sineGapMass u)).sub
      (tendsto_integrated_gap_of_PCC h (by exact_mod_cast hq : 0 < (q : ℝ)))
    simpa [integratedGapDeficit] using hlim.const_mul (2 / (q : ℝ))
  · intro h
    have hprimitive (q : ℚ) (hq : 0 < q) :
        Tendsto (fun T : ℝ => ∫ u in (0 : ℝ)..(q : ℝ), positiveGapMass T u) atTop
          (𝓝 (∫ u in (0 : ℝ)..(q : ℝ), sineGapMass u)) := by
      have hn : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      have hlim := (tendsto_const_nhds (x := ∫ u in (0 : ℝ)..(q : ℝ), sineGapMass u)).sub
        ((h q hq).const_mul ((q : ℝ) / 2))
      simp only [mul_zero, sub_zero] at hlim
      apply hlim.congr' (Eventually.of_forall fun T => ?_)
      dsimp [integratedGapDeficit]
      field_simp [hn] <;> ring
    have band (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
        Tendsto (fun T : ℝ => ∫ u in (a : ℝ)..(b : ℝ), positiveGapMass T u) atTop
          (𝓝 (∫ u in (a : ℝ)..(b : ℝ), sineGapMass u)) := by
      have hadd {f : ℝ → ℝ} (hf : Monotone f) :
          (∫ u in (0 : ℝ)..(b : ℝ), f u) - (∫ u in (0 : ℝ)..(a : ℝ), f u) =
            ∫ u in (a : ℝ)..(b : ℝ), f u := by
        have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (f := f) (a := 0) (b := (a : ℝ)) (c := (b : ℝ))
          hf.intervalIntegrable hf.intervalIntegrable
        linarith only [hi]
      have hlim := (hprimitive b hb).sub (hprimitive a ha)
      rw [hadd sineGapMass_mono] at hlim
      apply hlim.congr'
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      exact hadd (positiveGapMass_mono hT)
    apply positiveGapPCC_of_pointwise
    intro x hx
    apply tendsto_order.2
    constructor
    · intro l hl
      obtain ⟨a, ha, hax⟩ := exists_rat_btwn
        (show max 0 (x - (sineGapMass x - l)) < x from max_lt hx (by linarith))
      obtain ⟨b, hab, hbx⟩ := exists_rat_btwn hax
      have ha₀ : 0 < (a : ℝ) := lt_of_le_of_lt (le_max_left _ _) ha
      have hb₀ : 0 < (b : ℝ) := ha₀.trans hab
      have hla : l < sineGapMass (a : ℝ) := by
        linarith only [(sineGapMass_increment_bounds hax.le).2,
          lt_of_le_of_lt (le_max_right _ _) ha]
      have hstrict := (mul_lt_mul_of_pos_left hla (sub_pos.mpr hab)).trans_le
        (gap_band_bounds sineGapMass_mono hab.le).1
      filter_upwards [(band a b (by exact_mod_cast ha₀) (by exact_mod_cast hb₀)).eventually
        (lt_mem_nhds hstrict), eventually_gt_atTop (1 : ℝ)] with T ht hT
      have hh := ht.trans_le (gap_band_bounds (positiveGapMass_mono hT) hab.le).2
      exact (lt_of_mul_lt_mul_left hh (sub_nonneg.mpr hab.le)).trans_le
        (positiveGapMass_mono hT hbx.le)
    · intro l hl
      obtain ⟨b, hxb, hb⟩ := exists_rat_btwn
        (show x < x + (l - sineGapMass x) by linarith)
      obtain ⟨a, hxa, hab⟩ := exists_rat_btwn hxb
      have ha₀ : 0 < (a : ℝ) := hx.trans hxa
      have hb₀ : 0 < (b : ℝ) := ha₀.trans hab
      have hbl : sineGapMass (b : ℝ) < l := by
        linarith only [(sineGapMass_increment_bounds hxb.le).2, hb]
      have hstrict := (gap_band_bounds sineGapMass_mono hab.le).2.trans_lt
        (mul_lt_mul_of_pos_left hbl (sub_pos.mpr hab))
      filter_upwards [(band a b (by exact_mod_cast ha₀) (by exact_mod_cast hb₀)).eventually
        (gt_mem_nhds hstrict), eventually_gt_atTop (1 : ℝ)] with T ht hT
      have hh := (gap_band_bounds (positiveGapMass_mono hT) hab.le).1.trans_lt ht
      exact (positiveGapMass_mono hT hxa.le).trans_lt
        (lt_of_mul_lt_mul_left hh (sub_nonneg.mpr hab.le))

/-- Oriented finite-height secants of the weighted integrated deficit bound
the signed pointwise gap discrepancy. Subtracting the measured equal-ordinate
term before taking secants cancels it exactly. -/
theorem gap_error_mul_bounds_of_integrated_deficit {T R h : ℝ}
    (hT : 1 < T) (hh : 0 < h) (hR : h < R) :
    let d := fun u => u * integratedGapDeficit T u
    let error := positiveGapMass T R - sineGapMass R
    d (R - h) - d R - h ^ 2 ≤ 2 * h * error ∧
      2 * h * error ≤ d R - d (R + h) + h ^ 2 := by
  let C := (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))
  let G := sineGapMass R
  let P := positiveGapMass T R
  have hE (x : ℝ) (hx : 0 < x) :
      unfoldedWindowEnergy T x =
        sineWindowEnergy x + x * (C - 1) - x * integratedGapDeficit T x := by
    have he := unfoldedWindowEnergy_sub_sine_eq_collision_sub_deficit hT hx
    dsimp only [C]
    nlinarith only [he]
  have hL := (unfoldedWindowEnergy_secant_bounds hT (sub_nonneg.mpr hR.le)
    (show R - h < R by linarith)).2
  have hU := (unfoldedWindowEnergy_secant_bounds hT (hh.trans hR).le
    (show R < R + h by linarith)).1
  rw [show R - (R - h) = h by ring] at hL
  rw [show R + h - R = h by ring] at hU
  have hl := (div_le_iff₀ hh).mp hL
  have hu := (le_div_iff₀ hh).mp hU
  change unfoldedWindowEnergy T R - unfoldedWindowEnergy T (R - h) ≤ (C + 2 * P) * h at hl
  change (C + 2 * P) * h ≤ unfoldedWindowEnergy T (R + h) - unfoldedWindowEnergy T R at hu
  rw [hE R (hh.trans hR), hE (R-h) (sub_pos.mpr hR)] at hl
  rw [hE R (hh.trans hR), hE (R+h) (by linarith)] at hu
  have hm := sineWindowEnergy_adjacent_secants R h hh
  change (1 + 2 * G - h) * h ≤ _ ∧ _ ≤ (1 + 2 * G + h) * h at hm
  dsimp only
  change _ ≤ 2 * h * (P - G) ∧ 2 * h * (P - G) ≤ _
  exact ⟨by nlinarith only [hl, hm.1], by nlinarith only [hu, hm.2]⟩

/-- Three measurements at positive widths give a pointwise certificate for
the actual positive gaps, with explicit error amplification. -/
theorem gap_error_le_of_three_integrated_deficits {T R h ε : ℝ}
    (hT : 1 < T) (hh : 0 < h) (hR : h < R)
    (hl : |integratedGapDeficit T (R - h)| ≤ ε)
    (hm : |integratedGapDeficit T R| ≤ ε)
    (hu : |integratedGapDeficit T (R + h)| ≤ ε) :
    |positiveGapMass T R - sineGapMass R| ≤ h / 2 + (2 * R + h) * ε / (2 * h) := by
  have hb := gap_error_mul_bounds_of_integrated_deficit hT hh hR
  dsimp only at hb
  have h₀ := hh.trans hR
  have hε := (abs_nonneg _).trans hm
  have l := mul_le_mul_of_nonneg_left (abs_le.mp hl).1 (sub_nonneg.mpr hR.le)
  have m₂ := mul_le_mul_of_nonneg_left (abs_le.mp hm).2 h₀.le
  have u := mul_le_mul_of_nonneg_left (abs_le.mp hu).1 (add_nonneg h₀.le hh.le)
  rw [show h / 2 + (2 * R + h) * ε / (2 * h) =
    (h ^ 2 + (2 * R + h) * ε) / (2 * h) by field_simp [hh.ne']]
  apply abs_le.mpr
  have hh₂ : 0 < 2 * h := by positivity
  constructor
  · rw [← neg_div]
    apply (div_le_iff₀ hh₂).mpr
    nlinarith only [hb.1, l, m₂, mul_nonneg hh.le hε]
  · apply (le_div_iff₀ hh₂).mpr
    nlinarith only [hb.2, u, m₂]

/-- The choice of spacing minimizing the three-width bound gives a
square-root error rate for the positive-gap distribution at each width. -/
theorem gap_error_le_sqrt_of_three_integrated_deficits {T R ε : ℝ}
    (hT : 1 < T) (hε : 0 < ε) (hR : 2 * ε < R)
    (hl : |integratedGapDeficit T (R - Real.sqrt (2 * R * ε))| ≤ ε)
    (hm : |integratedGapDeficit T R| ≤ ε)
    (hu : |integratedGapDeficit T (R + Real.sqrt (2 * R * ε))| ≤ ε) :
    |positiveGapMass T R - sineGapMass R| ≤ Real.sqrt (2 * R * ε) + ε / 2 := by
  have hR₀ : 0 < R := by linarith
  have hp : 0 < 2 * R * ε := by positivity
  have hs := Real.sq_sqrt hp.le
  have hh := Real.sqrt_pos.mpr hp
  have hlR : Real.sqrt (2 * R * ε) < R := by
    nlinarith only [hs, mul_lt_mul_of_pos_left hR hR₀, hR₀, hh]
  apply (gap_error_le_of_three_integrated_deficits hT hh hlR hl hm hu).trans_eq
  field_simp [hh.ne']
  nlinarith only [hs]

/-- An explicitly prescribed finite sampling of the actual gap distribution
detects PCC. At each fixed rational width only a logarithm-squared number of
samples is needed to replace the complete integral. -/
theorem positiveGapPCC_iff_logSquareSampledGapDeficit :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => sampledIntegratedGapDeficit T q (logSquareGapMesh T))
        atTop (𝓝 0) := by
  rw [positiveGapPCC_iff_rationalIntegratedGapDeficit]
  have hdiff (q : ℚ) (hq : 0 < q) :=
    sampled_gap_deficit_sub_tendsto_zero (by exact_mod_cast hq : (0 : ℝ) < q)
      logSquareGapMesh (Eventually.of_forall fun _ => Nat.succ_pos _)
      log_div_logSquareGapMesh_tendsto_zero
  constructor
  · intro hg q hq
    simpa only [sub_add_cancel, zero_add] using (hdiff q hq).add (hg q hq)
  · intro hs q hq
    simpa only [sub_sub_cancel, sub_zero] using (hs q hq).sub (hdiff q hq)

end RiemannResearch.Analysis.MontgomeryPositiveGap
