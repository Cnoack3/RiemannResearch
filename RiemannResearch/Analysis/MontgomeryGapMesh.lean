/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryIntegratedGapDensity
import RiemannResearch.Analysis.MontgomeryFejerCertificate
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite sampling for the signed positive-gap route

The short-window triangle identity follows the normalization of
Goldston--Lee--Schettler--Suriajaya, arXiv:2503.15449v2, §2.
Monotone quadrature preserves the signed gap deficit and gives its finite
left-endpoint approximation with a one-sided error.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance

/-- Left-endpoint sum on the uniform mesh of the unfolded gap window `[0,R]`. -/
def gapMeshSum (f : ℝ → ℝ) (R : ℝ) (n : ℕ) : ℝ :=
  (R / n) * ∑ k ∈ Finset.range n, f ((k : ℝ) * (R / n))

theorem integral_sub_gapMeshSum_bounds {f : ℝ → ℝ} (hf : Monotone f)
    {R : ℝ} (hR : 0 ≤ R) {n : ℕ} (hn : 0 < n) :
    0 ≤ (∫ u in (0 : ℝ)..R, f u) - gapMeshSum f R n ∧
      (∫ u in (0 : ℝ)..R, f u) - gapMeshSum f R n ≤ (R / n) * (f R - f 0) := by
  let d := R / (n : ℝ)
  let a : ℕ → ℝ := fun k => (k : ℝ) * d
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 ≤ d := div_nonneg hR hn'.le
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = R := by dsimp [a, d]; field_simp [hn'.ne']
  have hcell (k : ℕ) :
      d * f (a k) ≤ (∫ u in a k..a (k + 1), f u) ∧
        (∫ u in a k..a (k + 1), f u) ≤ d * f (a (k + 1)) := by
    have hstep : a (k + 1) - a k = d := by
      simp only [a, Nat.cast_add, Nat.cast_one]
      ring
    have hk : a k ≤ a (k + 1) := by linarith only [hstep, hd]
    have hi : IntervalIntegrable f volume (a k) (a (k + 1)) := hf.intervalIntegrable
    have hlo := intervalIntegral.integral_mono_on hk intervalIntegrable_const hi
      (fun u (hu : u ∈ Icc (a k) (a (k + 1))) => hf hu.1)
    have hhi := intervalIntegral.integral_mono_on hk hi intervalIntegrable_const
      (fun u (hu : u ∈ Icc (a k) (a (k + 1))) => hf hu.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hstep] at hlo hhi
    exact ⟨hlo, hhi⟩
  have harea := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := f) (a := a) (n := n) (fun _ _ => hf.intervalIntegrable)
  rw [ha0, han] at harea
  have hmesh : gapMeshSum f R n = d * ∑ k ∈ Finset.range n, f (a k) := rfl
  have hlo : gapMeshSum f R n ≤ ∫ u in (0 : ℝ)..R, f u := by
    rw [hmesh, Finset.mul_sum, ← harea]
    exact Finset.sum_le_sum fun k _ => (hcell k).1
  have hhi : (∫ u in (0 : ℝ)..R, f u) ≤ d * ∑ k ∈ Finset.range n, f (a (k + 1)) := by
    rw [← harea, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => (hcell k).2
  have htel : (∑ k ∈ Finset.range n, f (a (k + 1))) =
      (∑ k ∈ Finset.range n, f (a k)) + f R - f 0 := by
    have he : (∑ k ∈ Finset.range n, f (a (k + 1))) + f (a 0) =
        (∑ k ∈ Finset.range n, f (a k)) + f (a n) :=
      (Finset.sum_range_succ' (fun k => f (a k)) n).symm.trans
        (Finset.sum_range_succ (fun k => f (a k)) n)
    rw [ha0, han] at he
    linarith only [he]
  refine ⟨sub_nonneg.mpr hlo, ?_⟩
  calc
    _ ≤ d * (∑ k ∈ Finset.range n, f (a (k + 1))) - gapMeshSum f R n :=
      sub_le_sub_right hhi _
    _ = _ := by rw [htel, hmesh]; change _ = d * (f R - f 0); ring

theorem sineGapMass_increment_bounds {a b : ℝ} (hab : a ≤ b) :
    0 ≤ sineGapMass b - sineGapMass a ∧ sineGapMass b - sineGapMass a ≤ b - a := by
  let k := fun u : ℝ => 1 - Real.sinc (Real.pi * u) ^ 2
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hk0 (u : ℝ) : 0 ≤ k u := by
    have hsq := (sq_le_sq₀ (abs_nonneg (Real.sinc (Real.pi * u))) zero_le_one).mpr
      (Real.abs_sinc_le_one (Real.pi * u))
    rw [sq_abs, one_pow] at hsq
    exact sub_nonneg.mpr hsq
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hk.intervalIntegrable 0 a) (hk.intervalIntegrable a b)
  change sineGapMass a + (∫ u in a..b, k u) = sineGapMass b at hsplit
  have hlo := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab hk0
  have hhi := intervalIntegral.integral_mono_on (μ := volume) hab (hk.intervalIntegrable a b)
    intervalIntegrable_const
    (fun u _ => (sub_le_self 1 (sq_nonneg (Real.sinc (Real.pi * u))) : k u ≤ 1))
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hhi
  exact ⟨by linarith only [hsplit, hlo], by linarith only [hsplit, hhi]⟩

theorem sineGapMass_mono : Monotone sineGapMass :=
  fun _ _ hab => sub_nonneg.mp (sineGapMass_increment_bounds hab).1

/-- Signed gap deficit using only finitely many samples of the actual gap count. -/
def sampledIntegratedGapDeficit (T R : ℝ) (n : ℕ) : ℝ :=
  (2 / R) * ((∫ u in (0 : ℝ)..R, sineGapMass u) - gapMeshSum (positiveGapMass T) R n)

/-- The sine model cancels from the sum of the three sampled terms. -/
theorem signed_sampled_gap_sum_eq_window_sub_mesh (T : ℝ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    sineHoleTriangle R + shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n =
      (actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) -
        2 * gapMeshSum (positiveGapMass T) R n) / R := by
  unfold sineHoleTriangle shortWindowMomentDeficit sampledIntegratedGapDeficit
  rw [integral_sineGapMass]
  generalize (∫ s in (0 : ℝ)..R, (R - s) * Real.sinc (Real.pi * s) ^ 2) = I
  field_simp [hR.ne']
  ring

/-- The left-endpoint approximation keeps the quadrature correction explicit. -/
theorem collision_div_main_eq_signed_mesh_deficits {T R : ℝ} (hT : 1 < T) (hR : 0 < R)
    (n : ℕ) :
    (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) =
      sineHoleTriangle R + shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n -
        (2 / R) * ((∫ u in (0 : ℝ)..R, positiveGapMass T u) -
          gapMeshSum (positiveGapMass T) R n) := by
  rw [collision_div_main_eq_signed_gap_deficits hT hR]
  unfold sampledIntegratedGapDeficit integratedGapDeficit
  ring

theorem integratedGapDeficit_le_sampled {T R : ℝ} (hT : 1 < T) (hR : 0 < R)
    {n : ℕ} (hn : 0 < n) : integratedGapDeficit T R ≤ sampledIntegratedGapDeficit T R n := by
  have hlo := (integral_sub_gapMeshSum_bounds (positiveGapMass_mono hT) hR.le hn).1
  unfold integratedGapDeficit sampledIntegratedGapDeficit
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (sub_nonneg.mp hlo) _) (by positivity)

/-- At the absolute pair scale the same sampled statistic differs from the
distinct-zero collision count by exactly the nonnegative quadrature error. -/
theorem absolute_sampled_gap_sub_analytic_eq {T R : ℝ} (hT : 1 < T) (hR : 0 < R)
    (n : ℕ) :
    let D := T * Real.log T / (2 * Real.pi)
    D * (sineHoleTriangle R + shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n) -
      (analyticPairCount T : ℝ) = (distinctZeroCollision T : ℝ) + D * ((2 / R) *
        ((∫ u in (0 : ℝ)..R, positiveGapMass T u) - gapMeshSum (positiveGapMass T) R n)) := by
  dsimp only
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have he := collision_div_main_eq_signed_mesh_deficits hT hR n
  have hdiv := (div_eq_iff hD.ne').mp he
  have hC : (actualCollision T : ℝ) = (analyticPairCount T : ℝ) + distinctZeroCollision T := by
    exact_mod_cast collision_eq_analytic_add_distinctZeroCollision T
  let U := sineHoleTriangle R + shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n
  let e := (2 / R) * ((∫ u in (0 : ℝ)..R, positiveGapMass T u) -
    gapMeshSum (positiveGapMass T) R n)
  change (actualCollision T : ℝ) = (U - e) * D at hdiv
  change D * U - (analyticPairCount T : ℝ) = (distinctZeroCollision T : ℝ) + D * e
  rw [hC, sub_mul] at hdiv
  linarith only [hdiv, mul_comm D U, mul_comm D e]

/-- At each fixed positive width, sufficiently fine finite sampling certifies
criticality while allowing arbitrary analytic multiplicity. -/
theorem sampled_gap_critical_line_iff {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    (∃ n : ℕ, 0 < n ∧ (T * Real.log T / (2 * Real.pi)) *
      (sineHoleTriangle R + shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n) -
      (analyticPairCount T : ℝ) < 2) ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  let P := positiveGapMass T
  have hP : Monotone P := positiveGapMass_mono hT
  have hcoef : 0 ≤ 2 / R := by positivity
  constructor
  · rintro ⟨n, hn, hsmall⟩ ρ hρ
    have he := absolute_sampled_gap_sub_analytic_eq hT hR n
    dsimp only at he
    rw [he] at hsmall
    have hn0 := (integral_sub_gapMeshSum_bounds hP hR.le hn).1
    have hnon := mul_nonneg hD.le (mul_nonneg hcoef hn0)
    by_contra hoff
    have htwo : (2 : ℝ) ≤ distinctZeroCollision T := by
      exact_mod_cast two_le_distinctZeroCollision_of_off_line hρ hoff
    exact (not_le.mpr hsmall) (htwo.trans (le_add_of_nonneg_right hnon))
  · intro hall
    have hc := (collision_eq_analyticPairCount_iff T).mpr hall
    have hz : distinctZeroCollision T = 0 := by
      have he := collision_eq_analytic_add_distinctZeroCollision T
      omega
    obtain ⟨n, hn⟩ := exists_nat_gt (D * (2 * (P R - P 0)))
    have hP0 : 0 ≤ P R - P 0 := sub_nonneg.mpr (hP hR.le)
    have hn' : 0 < (n : ℝ) := (mul_nonneg hD.le (mul_nonneg (by norm_num) hP0)).trans_lt hn
    have hnat : 0 < n := Nat.cast_pos.mp hn'
    refine ⟨n, hnat, ?_⟩
    have he := absolute_sampled_gap_sub_analytic_eq hT hR n
    dsimp only at he
    rw [he, hz, Nat.cast_zero, zero_add]
    change D * ((2 / R) * ((∫ u in (0 : ℝ)..R, P u) - gapMeshSum P R n)) < 2
    have hupper := (integral_sub_gapMeshSum_bounds hP hR.le hnat).2
    calc
      _ ≤ D * ((2 / R) * ((R / n) * (P R - P 0))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hcoef) hD.le
      _ = D * (2 * (P R - P 0)) / n := by field_simp [hR.ne', hn'.ne']
      _ < 1 := (div_lt_iff₀ hn').mpr (by simpa using hn)
      _ < 2 := by norm_num

/-- The signed-gap criterion for RH can keep its unfolded width fixed. -/
theorem cofinal_sampled_gap_critical_line_iff_RH {R : ℝ} (hR : 0 < R) :
    (∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ 1 < T ∧ ∃ n : ℕ, 0 < n ∧
      (T * Real.log T / (2 * Real.pi)) *
        (sineHoleTriangle R + shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n) -
        (analyticPairCount T : ℝ) < 2) ↔ RiemannHypothesis := by
  rw [← MontgomeryFormFactor.cofinal_fejer_critical_line_iff_RH,
    MontgomeryFormFactor.cofinal_fejer_critical_line_iff]
  constructor
  · intro h H ρ hρ
    obtain ⟨T, hHT, hT, hn⟩ := h H
    obtain ⟨hz, hi, hheight⟩ := mem_cutoff.mp hρ
    exact (sampled_gap_critical_line_iff hT hR).mp hn ρ
      (mem_cutoff.mpr ⟨hz, hi, hheight.trans hHT⟩)
  · intro h H
    let T := max H 2
    have hT : 1 < T := lt_of_lt_of_le (by norm_num) (le_max_right H 2)
    exact ⟨T, le_max_left H 2, hT, (sampled_gap_critical_line_iff hT hR).mpr (h T)⟩

theorem sampledIntegratedGapDeficit_le_of_pointwise {T R η : ℝ} (hR : 0 < R) {n : ℕ}
    (hn : 0 < n)
    (hmesh : ∀ k : ℕ, k < n → sineGapMass ((k : ℝ) * (R / n)) - η ≤
      positiveGapMass T ((k : ℝ) * (R / n))) :
    sampledIntegratedGapDeficit T R n ≤ 2 * (R / n) + 2 * η := by
  let d := R / (n : ℝ)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 ≤ d := div_nonneg hR.le hn'.le
  have hmodel := (integral_sub_gapMeshSum_bounds sineGapMass_mono hR.le hn).2
  have hmodel' : (∫ u in (0 : ℝ)..R, sineGapMass u) - gapMeshSum sineGapMass R n ≤ d * R :=
    hmodel.trans (mul_le_mul_of_nonneg_left
      (by simpa using (sineGapMass_increment_bounds hR.le).2) hd)
  have hdiff : gapMeshSum sineGapMass R n - gapMeshSum (positiveGapMass T) R n ≤ R * η := by
    have hsum := Finset.sum_le_sum (fun k hk => hmesh k (Finset.mem_range.mp hk))
    rw [Finset.sum_sub_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hs : (∑ k ∈ Finset.range n, sineGapMass ((k : ℝ) * d)) -
        (∑ k ∈ Finset.range n, positiveGapMass T ((k : ℝ) * d)) ≤ (n : ℝ) * η := by
      linarith only [hsum]
    unfold gapMeshSum
    change d * (∑ k ∈ Finset.range n, sineGapMass ((k : ℝ) * d)) -
      d * (∑ k ∈ Finset.range n, positiveGapMass T ((k : ℝ) * d)) ≤ R * η
    rw [← mul_sub]
    calc
      _ ≤ d * ((n : ℝ) * η) := mul_le_mul_of_nonneg_left hs hd
      _ = _ := by dsimp [d]; field_simp [hn'.ne']
  unfold sampledIntegratedGapDeficit
  calc
    _ ≤ (2 / R) * (d * R + R * η) :=
      mul_le_mul_of_nonneg_left (by linarith only [hmodel', hdiff]) (by positivity)
    _ = _ := by
      change _ = 2 * d + 2 * η
      field_simp [hR.ne']

/-- Fixed-width sampled deficit budgets suffice for density one. -/
theorem density_one_of_sampledGapDeficits
    (h : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∃ n : ℕ, 0 < n ∧
      ∀ᶠ T : ℝ in atTop, shortWindowMomentDeficit T R + sampledIntegratedGapDeficit T R n ≤ ε) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  apply density_one_of_integratedGapDeficits
  intro ε hε
  obtain ⟨R, hR, n, hn, hsampled⟩ := h ε hε
  refine ⟨R, hR, ?_⟩
  filter_upwards [hsampled, eventually_gt_atTop (1 : ℝ)] with T hbudget hT
  linarith only [hbudget, integratedGapDeficit_le_sampled hT (zero_lt_one.trans_le hR) hn]

/-- Only pointwise lower pair correlation at each fixed positive gap is needed
in the signed route, given the independent short-window second moment. -/
theorem density_one_of_pointwise_positiveGap_lower
    (h : ∀ u : ℝ, 0 < u → ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop,
      sineGapMass u - η ≤ positiveGapMass T u)
    (hm : ShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  apply density_one_of_sampledGapDeficits
  intro ε hε
  let η := ε / 6
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨R, hR, hmoment⟩ := hm η hη
  have hR0 := zero_lt_one.trans_le hR
  obtain ⟨n, hn⟩ := exists_nat_gt (R / η)
  have hn' : 0 < (n : ℝ) := (div_pos hR0 hη).trans hn
  have hn0 : 0 < n := Nat.cast_pos.mp hn'
  let d := R / (n : ℝ)
  have hd : 0 < d := div_pos hR0 hn'
  have hdη : d < η := (div_lt_iff₀ hn').mpr (by
    rw [mul_comm η]
    exact (div_lt_iff₀ hη).mp hn)
  have hnode (k : ℕ) : ∀ᶠ T : ℝ in atTop,
      sineGapMass ((k : ℝ) * d) - η ≤ positiveGapMass T ((k : ℝ) * d) := by
    by_cases hk : k = 0
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      simp only [hk, Nat.cast_zero, zero_mul, sineGapMass, intervalIntegral.integral_same, zero_sub]
      exact (neg_nonpos.mpr hη.le).trans (positiveGapMass_nonneg hT 0)
    · exact h _ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) hd) η hη
  have hnodes (m : ℕ) : ∀ᶠ T : ℝ in atTop, ∀ k : ℕ, k < m →
      sineGapMass ((k : ℝ) * d) - η ≤ positiveGapMass T ((k : ℝ) * d) := by
    induction m with
    | zero => exact Eventually.of_forall (by simp)
    | succ m ih =>
        filter_upwards [ih, hnode m] with T hprev hlast
        intro k hk
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk' | rfl
        · exact hprev k hk'
        · exact hlast
  refine ⟨R, hR, n, hn0, ?_⟩
  filter_upwards [hmoment, hnodes n] with T hwindow hgrid
  have hM : shortWindowMomentDeficit T R ≤ η := by
    unfold shortWindowMomentDeficit
    exact (div_le_iff₀ hR0).mpr (by linarith only [hwindow])
  have hgridBound : sampledIntegratedGapDeficit T R n ≤ 2 * d + 2 * η :=
    sampledIntegratedGapDeficit_le_of_pointwise hR0 hn0 hgrid
  dsimp [η] at hM hgridBound hdη
  linarith only [hM, hgridBound, hdη, hε]

/-- Monotonicity and the sine-model increment bound reduce the one-sided
pair-correlation input further to positive rational unfolded gaps. -/
theorem density_one_of_rational_positiveGap_lower
    (h : ∀ u : ℚ, 0 < u → ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop,
      sineGapMass (u : ℝ) - η ≤ positiveGapMass T (u : ℝ))
    (hm : ShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  apply density_one_of_pointwise_positiveGap_lower ?_ hm
  intro u hu η hη
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (max_lt hu (by linarith : u - η / 2 < u))
  have hqpos : (0 : ℝ) < (q : ℝ) := (le_max_left _ _).trans_lt hqlo
  have hq : 0 < q := by exact_mod_cast hqpos
  have hclose : u - η / 2 < (q : ℝ) := (le_max_right _ _).trans_lt hqlo
  filter_upwards [h q hq (η / 2) (by positivity), eventually_gt_atTop (1 : ℝ)] with T hs hT
  have hinc := (sineGapMass_increment_bounds hqhi.le).2
  have hP := positiveGapMass_mono hT hqhi.le
  linarith only [hs, hinc, hP, hclose]

end RiemannResearch.Analysis.MontgomeryPositiveGap
