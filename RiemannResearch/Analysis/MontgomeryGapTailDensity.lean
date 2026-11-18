/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryGapMesh
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The large-gap tail suffices in the signed-gap route

Goldston, Lee, Schettler and Suriajaya, arXiv:2503.15449v3, Section 4,
deduce essential simplicity from positive-gap PCC using their Section 3
short-window moment. Here it suffices to bound large positive gaps from
below by the affine asymptote of their sine model. The earlier part of the
integral enters as a finite loss that is divided by the chosen width.
-/

noncomputable section
open Filter MeasureTheory Set intervalIntegral Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance

/-- The fixed unfolded widths with arbitrarily small relative moment error
can be chosen arbitrarily large. This is the form used in GLSS Section 4. -/
def CofinalShortWindowSecondMomentUpper : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, ∃ R : ℝ, B ≤ R ∧ ∀ᶠ T : ℝ in atTop,
    actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) ≤ R ^ 2 + ε * R

/-- Only an additive lower bound on the large positive gaps, with the
one-half sine-hole constant, is needed. T can depend on the test gap. -/
def LargeGapAffineLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
    ∀ᶠ T : ℝ in atTop, u - (1 / 2 + ε) ≤ positiveGapMass T u

theorem largeGapAffineLower_of_positiveGapPCC (h : PositiveGapPCC) : LargeGapAffineLower := by
  intro ε hε
  refine ⟨1, zero_le_one, fun u hu => ?_⟩
  have hu0 := zero_lt_one.trans_le hu
  filter_upwards [h u u hu0 le_rfl ε hε] with T hT
  have he := (abs_le.mp (hT u ⟨le_rfl, le_rfl⟩)).1
  linarith only [he, sineGapMass_lower hu0.le]

/-- Monotone quadrature turns pointwise eventual lower bounds on a fixed
window into an eventual integrated lower bound with arbitrary mesh error. -/
theorem eventually_integral_positiveGapMass_lower_of_affine
    {U R c η : ℝ} (hUR : U < R) (hη : 0 < η)
    (h : ∀ u : ℝ, U ≤ u → ∀ᶠ T : ℝ in atTop, u - c ≤ positiveGapMass T u) :
    ∀ᶠ T : ℝ in atTop, (R ^ 2 - U ^ 2) / 2 - c * (R - U) - η * (R - U) ≤
      ∫ u in U..R, positiveGapMass T u := by
  let S := R - U
  have hS : 0 < S := sub_pos.mpr hUR
  obtain ⟨n, hn⟩ := exists_nat_gt (S / η)
  have hn' : 0 < (n : ℝ) := (div_pos hS hη).trans hn
  have hn0 : 0 < n := Nat.cast_pos.mp hn'
  let d := S / (n : ℝ)
  have hd : 0 ≤ d := div_nonneg hS.le hn'.le
  have hdη : d ≤ η := by
    apply (div_le_iff₀ hn').mpr
    rw [mul_comm η]
    exact (div_le_iff₀ hη).mp hn.le
  let g : ℝ → ℝ := fun v => v + U - c
  have hg : Monotone g := by
    intro u v huv
    change u + U - c ≤ v + U - c
    linarith only [huv]
  have hnode (k : ℕ) : ∀ᶠ T : ℝ in atTop,
      g ((k : ℝ) * d) ≤ positiveGapMass T ((k : ℝ) * d + U) :=
    h _ (le_add_of_nonneg_left (mul_nonneg (by positivity) hd))
  have hnodes (m : ℕ) : ∀ᶠ T : ℝ in atTop, ∀ k : ℕ, k < m →
      g ((k : ℝ) * d) ≤ positiveGapMass T ((k : ℝ) * d + U) := by
    induction m with
    | zero => exact Eventually.of_forall (by simp)
    | succ m ih =>
        filter_upwards [ih, hnode m] with T hprev hlast
        intro k hk
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk' | rfl
        · exact hprev k hk'
        · exact hlast
  have hIg : (∫ v in (0 : ℝ)..S, g v) = (R ^ 2 - U ^ 2) / 2 - c * (R - U) := by
    have hg' : g = fun v : ℝ => v + (U - c) := by
      funext v
      dsimp [g]
      ring
    have hid : IntervalIntegrable (fun v : ℝ => v) volume 0 S :=
      continuous_id.intervalIntegrable 0 S
    have hconst : IntervalIntegrable (fun _ : ℝ => U - c) volume 0 S :=
      intervalIntegrable_const
    rw [hg']
    change (∫ v in (0 : ℝ)..S, v + (U - c)) = _
    rw [intervalIntegral.integral_add hid hconst, integral_id, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    dsimp [S]
    ring
  have hinc : g S - g 0 = S := by dsimp [g]; ring
  have hG := (integral_sub_gapMeshSum_bounds hg hS.le hn0).2
  rw [hIg, hinc] at hG
  filter_upwards [hnodes n, eventually_gt_atTop (1 : ℝ)] with T hgrid hT
  let p : ℝ → ℝ := fun v => positiveGapMass T (v + U)
  have hp : Monotone p := by
    intro u v huv
    apply positiveGapMass_mono hT
    change u + U ≤ v + U
    linarith only [huv]
  have hpI := (integral_sub_gapMeshSum_bounds hp hS.le hn0).1
  have hi : (∫ v in (0 : ℝ)..S, p v) = ∫ u in U..R, positiveGapMass T u := by
    simpa only [p, S, zero_add, sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := S) (positiveGapMass T) U)
  rw [hi] at hpI
  have hs : gapMeshSum g S n ≤ gapMeshSum p S n := by
    unfold gapMeshSum
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun k hk => hgrid k (Finset.mem_range.mp hk)) hd
  have he := mul_le_mul_of_nonneg_right hdη hS.le
  linarith only [hG, hpI, hs, he]

/-- The large-gap lower bound and the independently supplied moment imply
the equal-ordinate count asymptotic. The segment below U costs at most
U squared divided by the fixed width. -/
theorem collision_limit_of_largeGapAffineLower
    (hg : LargeGapAffineLower) (hm : CofinalShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
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
    let η := (b - 1) / 8
    have hη : 0 < η := div_pos (sub_pos.mpr hb) (by norm_num)
    obtain ⟨U, hU, hl⟩ := hg η hη
    obtain ⟨R, hR, hmoment⟩ := hm η hη (max (U + 1) (U ^ 2 / η))
    have hUR : U < R := by linarith only [(le_max_left (U + 1) (U ^ 2 / η)).trans hR]
    have hR0 := hU.trans_lt hUR
    have hsmall : U ^ 2 ≤ η * R := by
      rw [mul_comm η]
      exact (div_le_iff₀ hη).mp ((le_max_right _ _).trans hR)
    have hηb : 1 + 6 * η < b := by dsimp [η]; linarith only [hb]
    filter_upwards [hmoment, eventually_integral_positiveGapMass_lower_of_affine hUR hη hl,
      eventually_gt_atTop (1 : ℝ)] with T hW hI hT
    let D := T * Real.log T / (2 * Real.pi)
    have hP := positiveGapMass_mono hT
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := positiveGapMass T) (a := 0) (b := U) (c := R)
      hP.intervalIntegrable hP.intervalIntegrable
    have hI0 := intervalIntegral.integral_nonneg_of_forall (μ := volume) hU
      (positiveGapMass_nonneg hT)
    rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at hW
    change R * ((actualCollision T : ℝ) / D) +
      2 * (∫ u in (0 : ℝ)..R, positiveGapMass T u) ≤ R ^ 2 + η * R at hW
    have htail : (1 + 4 * η) * (R - U) ≤ (1 + 4 * η) * R :=
      mul_le_mul_of_nonneg_left (sub_le_self R hU) (by positivity)
    have hC : R * ((actualCollision T : ℝ) / D) ≤ R * (1 + 6 * η) := by
      nlinarith only [hW, hI, hsplit, hI0, hsmall, htail]
    exact (le_of_mul_le_mul_left hC hR0).trans_lt hηb

/-- No small-gap PCC input is needed for these two density-one conclusions. -/
theorem density_one_of_largeGapAffineLower
    (hg : LargeGapAffineLower) (hm : CofinalShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  density_one_of_collision_limit (collision_limit_of_largeGapAffineLower hg hm)

end RiemannResearch.Analysis.MontgomeryPositiveGap
