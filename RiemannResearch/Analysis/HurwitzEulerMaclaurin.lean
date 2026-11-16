/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Convex
/-!
# Euler--Maclaurin continuation and actual Hurwitz strip growth

The finite identity retains both endpoint terms. Passing to infinity in the
Dirichlet-series half-plane identifies the formula with Mathlib's actual
Hurwitz zeta. The bounded Bernoulli kernel is a Mellin transform, so analytic
continuation gives the identity for real part greater than -1 off the real axis.

The resulting quadratic bound is uniform in the real strip coordinate. The
constant depends on the positive representative of the additive-circle
parameter, the strip, and any fixed complex shift. It is not asserted uniform
in a growing rational denominator or in a vanishing damping parameter.

Concrete RH-program consumer: the polynomial-growth input in
ConreyBaluyotEstermannHurwitzGrowth and ConreyBaluyotEstermannMellinGrowth.

Source: NIST DLMF 25.11.6, corrected Euler--Maclaurin formula:
https://dlmf.nist.gov/25.11.E6
This supplies the classical identity and proof strategy, not a new density
theorem. UniformSelbergDensity still requires the uniform mollified moment.
-/

open Complex Set MeasureTheory
noncomputable section
namespace RiemannResearch.Analysis.HurwitzEulerMaclaurin
def bernoulliRemainder (x : ℝ) : ℝ := Int.fract x * (Int.fract x - 1)

theorem abs_bernoulliRemainder_le (x : ℝ) :
    |bernoulliRemainder x| ≤ 1 / 4 := by
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  rw [bernoulliRemainder, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h0 (by linarith))]
  nlinarith [sq_nonneg (Int.fract x - 1 / 2)]

theorem measurable_bernoulliRemainder : Measurable bernoulliRemainder :=
  measurable_fract.mul (measurable_fract.sub_const 1)

def remainderIntegral (q : ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi q, (bernoulliRemainder (x - q) : ℂ) * (x : ℂ) ^ (-s - 2)

theorem norm_remainderIntegrand_le (q x : ℝ) (s : ℂ) (hx : 0 < x) :
    ‖(bernoulliRemainder (x - q) : ℂ) * (x : ℂ) ^ (-s - 2)‖ ≤
      (1 / 4 : ℝ) * x ^ (-s.re - 2) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num only [sub_re, neg_re, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (abs_bernoulliRemainder_le _) (Real.rpow_nonneg hx.le _)

theorem integrable_remainderIntegrand {q : ℝ} (hq : 0 < q) {s : ℂ}
    (hs : -1 < s.re) :
    IntegrableOn (fun x : ℝ => (bernoulliRemainder (x - q) : ℂ) *
      (x : ℂ) ^ (-s - 2)) (Ioi q) := by
  apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 2 < -1) hq).const_mul
    (1 / 4 : ℝ)).mono'
  · exact ((Complex.measurable_ofReal.comp
      (measurable_bernoulliRemainder.comp (measurable_id.sub_const q))).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact norm_remainderIntegrand_le q x s (hq.trans hx)

theorem norm_remainderIntegral_le {q : ℝ} (hq : 0 < q) {s : ℂ}
    (hs : -1 < s.re) :
    ‖remainderIntegral q s‖ ≤ q ^ (-s.re - 1) / (4 * (s.re + 1)) := by
  have he : -s.re - 2 < -1 := by linarith
  have hb := norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt he hq).const_mul (1 / 4 : ℝ))
    (show ∀ᵐ x : ℝ ∂volume.restrict (Ioi q),
      ‖(bernoulliRemainder (x - q) : ℂ) * (x : ℂ) ^ (-s - 2)‖ ≤
      (1 / 4 : ℝ) * x ^ (-s.re - 2) from by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact norm_remainderIntegrand_le q x s (hq.trans hx))
  unfold remainderIntegral
  refine hb.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt he hq]
  have hs0 : s.re + 1 ≠ 0 := ne_of_gt (by linarith)
  have heq : -s.re - 2 + 1 = -(s.re + 1) := by ring
  rw [heq]
  have hexp : -(s.re + 1) = -s.re - 1 := by ring
  rw [hexp]
  have hneg : -s.re - 1 ≠ 0 := by linarith
  field_simp [hs0, hneg]
  ring

def eulerMaclaurinValue (q : ℝ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) * (1 / 2 + q / (s - 1)) -
    (s * (s + 1) / 2) * remainderIntegral q s

theorem norm_eulerMaclaurinValue_le {q : ℝ} (hq : 0 < q) {s : ℂ}
    (hs : -1 < s.re) :
    ‖eulerMaclaurinValue q s‖ ≤
      q ^ (-s.re) * (1 / 2 + q / ‖s - 1‖) +
      (‖s‖ * ‖s + 1‖ / 8) * (q ^ (-s.re - 1) / (s.re + 1)) := by
  unfold eulerMaclaurinValue
  calc
    _ ≤ ‖(q : ℂ) ^ (-s) * (1 / 2 + q / (s - 1))‖ +
        ‖(s * (s + 1) / 2) * remainderIntegral q s‖ := norm_sub_le _ _
    _ ≤ q ^ (-s.re) * (1 / 2 + q / ‖s - 1‖) +
        (‖s‖ * ‖s + 1‖ / 2) * (q ^ (-s.re - 1) / (4 * (s.re + 1))) := by
      simp only [norm_mul, norm_div, norm_ofNat,
        Complex.norm_cpow_eq_rpow_re_of_pos hq, neg_re]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hq.le _)
        have hh := norm_add_le (1 / 2 : ℂ) ((q : ℂ) / (s - 1))
        simpa only [norm_div, norm_one, norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hq] using hh
      · exact mul_le_mul_of_nonneg_left (norm_remainderIntegral_le hq hs) (by positivity)
    _ = _ := by field_simp; ring

theorem norm_eulerMaclaurinValue_strip_le {q a b r t : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (ha : -1 < a)
    (hr : r ∈ Icc a b) (ht : 1 ≤ |t|) :
    ‖eulerMaclaurinValue q ((r : ℂ) + t * I)‖ ≤
      (q ^ (-b) * (1 / 2 + q) +
        ((max |a| |b| + 1) * (max |a| |b| + 2) / 8) *
          (q ^ (-b - 1) / (a + 1))) * |t| ^ 2 := by
  have hr1 : 0 < r + 1 := by linarith [hr.1]
  have ha1 : 0 < a + 1 := by linarith
  let R : ℝ := max |a| |b|
  have hR : 0 ≤ R := (abs_nonneg a).trans (le_max_left _ _)
  have hrR : |r| ≤ R := by
    apply abs_le.mpr
    constructor
    · have := le_max_left |a| |b|
      have := neg_abs_le a
      dsimp [R]
      linarith [hr.1]
    · have := le_max_right |a| |b|
      have := le_abs_self b
      dsimp [R]
      linarith [hr.2]
  have hre : ((r : ℂ) + t * I).re = r := by simp
  have him : ((r : ℂ) + t * I - 1).im = t := by simp
  have hden : 1 ≤ ‖(r : ℂ) + t * I - 1‖ := by
    have := Complex.abs_im_le_norm ((r : ℂ) + t * I - 1)
    rw [him] at this
    exact ht.trans this
  have hn : ‖(r : ℂ) + t * I‖ ≤ (R + 1) * |t| := by
    calc
      _ ≤ |r| + |t| := by simpa using norm_add_le (r : ℂ) ((t : ℂ) * I)
      _ ≤ R + |t| := by linarith
      _ ≤ (R + 1) * |t| := by nlinarith
  have hn1 : ‖(r : ℂ) + t * I + 1‖ ≤ (R + 2) * |t| := by
    have hh := norm_add_le ((r : ℂ) + t * I) (1 : ℂ)
    simp only [norm_one] at hh
    nlinarith
  have hqpow : q ^ (-r) ≤ q ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith [hr.2])
  have hqpow1 : q ^ (-r - 1) ≤ q ^ (-b - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hq hq1 (by linarith [hr.2])
  have hqdiv : q / ‖(r : ℂ) + t * I - 1‖ ≤ q := by
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr (by nlinarith)
  have htail : q ^ (-r - 1) / (r + 1) ≤ q ^ (-b - 1) / (a + 1) := by
    apply div_le_div₀ (Real.rpow_nonneg hq.le _) hqpow1 (by linarith) (by linarith [hr.1])
  have hbnd := norm_eulerMaclaurinValue_le hq
    (s := (r : ℂ) + t * I) (by simpa using ha.trans_le hr.1)
  rw [hre] at hbnd
  refine hbnd.trans ?_
  have hprod : ‖(r : ℂ) + t * I‖ * ‖(r : ℂ) + t * I + 1‖ ≤
      (R + 1) * (R + 2) * |t| ^ 2 := by
    calc
      _ ≤ ((R + 1) * |t|) * ((R + 2) * |t|) := by gcongr
      _ = _ := by ring
  have hm0 : 0 ≤ q ^ (-b) * (1 / 2 + q) := by positivity
  have ht2 : 1 ≤ |t| ^ 2 := by nlinarith
  calc
    _ ≤ q ^ (-b) * (1 / 2 + q) +
        ((R + 1) * (R + 2) * |t| ^ 2 / 8) *
          (q ^ (-b - 1) / (a + 1)) := by
      apply add_le_add
      · exact mul_le_mul hqpow (by linarith) (by positivity) (by positivity)
      · exact mul_le_mul (div_le_div_of_nonneg_right hprod (by norm_num)) htail
          (by positivity) (by positivity)
    _ ≤ _ := by
      dsimp [R] at *
      nlinarith [mul_le_mul_of_nonneg_left ht2 hm0]

/-- The exact one-cell trapezoidal remainder, proved by two integrations by parts. -/
theorem trapezoid_sub_integral_eq {q : ℝ} {f f' f'' : ℝ → ℂ}
    (hf : ∀ x ∈ uIcc q (q + 1), HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc q (q + 1), HasDerivAt f' (f'' x) x)
    (hfi : IntervalIntegrable f'' volume q (q + 1)) :
    (f q + f (q + 1)) / 2 - (∫ x in q..q + 1, f x) =
      -(1 / 2 : ℂ) * ∫ x in q..q + 1,
        ((x : ℂ) - q) * ((x : ℂ) - q - 1) * f'' x := by
  have hd0 (x : ℝ) : HasDerivAt
      (fun x : ℝ => ((x : ℂ) - q) * ((x : ℂ) - q - 1))
      (2 * ((x : ℂ) - q) - 1) x := by
    convert! (((hasDerivAt_id x).ofReal_comp.sub_const (q : ℂ)).mul
      (((hasDerivAt_id x).ofReal_comp.sub_const (q : ℂ)).sub_const 1)) using 1
    simp [id_eq]
    ring
  have hd1 (x : ℝ) : HasDerivAt
      (fun x : ℝ => 2 * ((x : ℂ) - q) - 1) (2 : ℂ) x := by
    convert! (((hasDerivAt_id x).ofReal_comp.sub_const (q : ℂ)).const_mul 2).sub_const 1
      using 1
    simp
  have hfi' : IntervalIntegrable f' volume q (q + 1) :=
    (show ContinuousOn f' (uIcc q (q + 1)) from
      fun x hx => (hf' x hx).continuousAt.continuousWithinAt).intervalIntegrable
  have h0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := q) (b := q + 1) (fun x _ => hd0 x) hf'
    (by exact (by fun_prop : Continuous (fun x : ℝ =>
      (2 : ℂ) * ((x : ℂ) - q) - 1)).intervalIntegrable _ _) hfi
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := q) (b := q + 1) (fun x _ => hd1 x) hf
    (by exact (continuous_const : Continuous (fun _ : ℝ => (2 : ℂ))).intervalIntegrable _ _)
    hfi'
  simp only [ofReal_add, ofReal_one] at h0 h1
  have he0 : (q : ℂ) + 1 - q = 1 := by ring
  simp only [he0, sub_self, mul_zero, zero_mul, zero_sub] at h0
  have he1 : (2 : ℂ) * 1 - 1 = 1 := by norm_num
  simp only [he0, sub_self, mul_zero, zero_sub, he1, one_mul, neg_one_mul,
    sub_neg_eq_add, intervalIntegral.integral_const_mul] at h1
  rw [h0, h1]
  ring

private theorem hasDerivAt_real_cpow {x : ℝ} (hx : x ≠ 0) (z : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ z) (z * (x : ℂ) ^ (z - 1)) x := by
  by_cases hz : z = 0
  · subst z
    simpa using (hasDerivAt_const x (1 : ℂ))
  · exact hasDerivAt_ofReal_cpow_const hx hz

/-- Exact one-cell identity for the actual power function, for every complex exponent. -/
theorem cpow_trapezoid_sub_integral {q : ℝ} (hq : 0 < q) (s : ℂ) :
    ((q : ℂ) ^ (-s) + ((q + 1 : ℝ) : ℂ) ^ (-s)) / 2 -
        (∫ x : ℝ in q..q + 1, (x : ℂ) ^ (-s)) =
      -(s * (s + 1) / 2) * ∫ x : ℝ in q..q + 1,
        ((x : ℂ) - q) * ((x : ℂ) - q - 1) * (x : ℂ) ^ (-s - 2) := by
  have hxpos : ∀ x ∈ uIcc q (q + 1), 0 < x := by
    rw [uIcc_of_le (by linarith)]
    intro x hx
    exact hq.trans_le hx.1
  have hf (x : ℝ) (hx : x ∈ uIcc q (q + 1)) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        (-s * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_real_cpow (ne_of_gt (hxpos x hx)) (-s)
  have hf' (x : ℝ) (hx : x ∈ uIcc q (q + 1)) :
      HasDerivAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1))
        (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
    convert! (hasDerivAt_real_cpow (ne_of_gt (hxpos x hx)) (-s - 1)).const_mul (-s)
      using 1
    rw [show -s - 1 - 1 = -s - 2 by ring]
    ring
  have hi : IntervalIntegrable (fun x : ℝ =>
      s * (s + 1) * (x : ℂ) ^ (-s - 2)) volume q (q + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (continuousAt_const.mul
      (Complex.continuousAt_ofReal_cpow_const x (-s - 2)
        (Or.inr (ne_of_gt (hxpos x hx))))).continuousWithinAt
  rw [trapezoid_sub_integral_eq hf hf' hi]
  have he : (fun x : ℝ =>
      ((x : ℂ) - q) * ((x : ℂ) - q - 1) *
        (s * (s + 1) * (x : ℂ) ^ (-s - 2))) =
      (fun x : ℝ => (s * (s + 1)) *
        (((x : ℂ) - q) * ((x : ℂ) - q - 1) * (x : ℂ) ^ (-s - 2))) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_const_mul]
  ring


/-- On each integer cell, the periodic Bernoulli remainder equals its quadratic piece. -/
theorem bernoulliRemainder_on_cell (q : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (q + n) (q + n + 1)) :
    bernoulliRemainder (x - q) = (x - (q + n)) * (x - (q + n) - 1) := by
  have hfr : Int.fract (x - q) = x - (q + n) := by
    calc
      _ = Int.fract ((x - (q + n)) + n) := congrArg _ (by ring)
      _ = Int.fract (x - (q + n)) := Int.fract_add_natCast _ _
      _ = x - (q + n) := Int.fract_eq_self.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simp only [bernoulliRemainder, hfr]

theorem cpow_trapezoid_sub_integral_periodic {q : ℝ} (hq : 0 < q) (s : ℂ) (n : ℕ) :
    (((q + n : ℝ) : ℂ) ^ (-s) + ((q + n + 1 : ℝ) : ℂ) ^ (-s)) / 2 -
        (∫ x : ℝ in q + n..q + n + 1, (x : ℂ) ^ (-s)) =
      -(s * (s + 1) / 2) * ∫ x : ℝ in q + n..q + n + 1,
        (bernoulliRemainder (x - q) : ℂ) * (x : ℂ) ^ (-s - 2) := by
  rw [cpow_trapezoid_sub_integral (by positivity : 0 < q + (n : ℝ))]
  congr 1
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  rw [uIoo_of_lt (by linarith)] at hx
  dsimp only
  rw [bernoulliRemainder_on_cell q n hx]
  push_cast
  ring

private theorem intervalIntegrable_cpow_pos {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (s : ℂ) : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ s) volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [uIcc_of_le huv] at hx
  exact (Complex.continuousAt_ofReal_cpow_const x s
    (Or.inr (ne_of_gt (hu.trans_le hx.1)))).continuousWithinAt

private theorem intervalIntegrable_remainder {q u v : ℝ} (hq : 0 < q)
    (hqu : q ≤ u) (huv : u ≤ v) {s : ℂ} (hs : -1 < s.re) :
    IntervalIntegrable (fun x : ℝ => (bernoulliRemainder (x - q) : ℂ) *
      (x : ℂ) ^ (-s - 2)) volume u v := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
  exact (integrable_remainderIntegrand hq hs).mono_set
    (fun x hx => lt_of_le_of_lt hqu hx.1)

/-- Finite Euler--Maclaurin identity with both endpoint terms retained. -/
theorem sum_range_cpow_eq {q : ℝ} (hq : 0 < q) {s : ℂ} (hs : -1 < s.re) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((q + n : ℝ) : ℂ) ^ (-s)) =
      ((q : ℂ) ^ (-s) - ((q + N : ℝ) : ℂ) ^ (-s)) / 2 +
      (∫ x : ℝ in q..q + N, (x : ℂ) ^ (-s)) -
      (s * (s + 1) / 2) * ∫ x : ℝ in q..q + N,
        (bernoulliRemainder (x - q) : ℂ) * (x : ℂ) ^ (-s - 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_succ, ← add_assoc]
    have hcell := cpow_trapezoid_sub_integral_periodic hq s N
    have hp := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cpow_pos hq (le_add_of_nonneg_right (Nat.cast_nonneg N)) (-s))
      (intervalIntegrable_cpow_pos (by positivity : 0 < q + (N : ℝ))
        (by linarith : q + (N : ℝ) ≤ q + N + 1) (-s))
    have hR := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_remainder hq le_rfl (le_add_of_nonneg_right (Nat.cast_nonneg N)) hs)
      (intervalIntegrable_remainder hq (le_add_of_nonneg_right (Nat.cast_nonneg N))
        (by linarith : q + (N : ℝ) ≤ q + N + 1) hs)
    rw [← hp, ← hR]
    linear_combination ih + hcell


open Filter Topology in
/-- Identification with Mathlib's Hurwitz zeta in the Dirichlet-series half-plane. -/
theorem hurwitzZeta_eq_eulerMaclaurinValue_of_one_lt_re {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta q s = eulerMaclaurinValue q s := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hseq : Tendsto (fun N : ℕ => q + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop q tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => ((q + N : ℝ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    convert! ((tendsto_rpow_neg_atTop (by linarith : 0 < s.re)).comp hseq) using 1
    funext N
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    rfl
  have hpint := intervalIntegral_tendsto_integral_Ioi q
    (integrableOn_Ioi_cpow_of_lt (a := -s) (by simpa using (show -s.re < -1 by linarith)) hq) hseq
  have hRint := intervalIntegral_tendsto_integral_Ioi q
    (integrable_remainderIntegrand hq (by linarith : -1 < s.re)) hseq
  have hsum : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N, ((q + n : ℝ) : ℂ) ^ (-s))
      atTop (𝓝 (HurwitzZeta.hurwitzZeta q s)) := by
    have hh := (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨hq.le, hq1⟩ hs).tendsto_sum_nat
    convert! hh using 1
    funext N
    apply Finset.sum_congr rfl
    intro n _
    simp only [ofReal_add, ofReal_natCast, Complex.cpow_neg, one_div]
    rw [add_comm]
  have hc : Tendsto (fun _ : ℕ => (q : ℂ) ^ (-s)) atTop (𝓝 ((q : ℂ) ^ (-s))) :=
    tendsto_const_nhds
  have hlim := (((hc.sub hpow).div_const (2 : ℂ)).add hpint).sub
    (hRint.const_mul (s * (s + 1) / 2))
  have heq := tendsto_nhds_unique hsum
    (hlim.congr' (Filter.Eventually.of_forall (fun N =>
      (sum_range_cpow_eq hq (by linarith : -1 < s.re) N).symm)))
  rw [heq, integral_Ioi_cpow_of_lt (a := -s) (by simpa using (show -s.re < -1 by linarith)) hq]
  unfold eulerMaclaurinValue remainderIntegral
  rw [Complex.cpow_add (-s) 1 hq0, Complex.cpow_one]
  have hs0 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, one_re, zero_re] at this
    linarith
  have hs1 : -s + 1 ≠ 0 := by
    intro h
    apply hs0
    linear_combination -h
  field_simp
  ring


/-- The bounded Bernoulli kernel cut off below the positive starting point. -/
def cutoffKernel (q : ℝ) : ℝ → ℂ :=
  (Ioi q).indicator (fun x => (bernoulliRemainder (x - q) : ℂ))

theorem measurable_cutoffKernel (q : ℝ) : Measurable (cutoffKernel q) :=
  (Complex.measurable_ofReal.comp
    (measurable_bernoulliRemainder.comp (measurable_id.sub_const q))).indicator measurableSet_Ioi

theorem norm_cutoffKernel_le (q x : ℝ) : ‖cutoffKernel q x‖ ≤ 1 / 4 := by
  by_cases hx : x ∈ Ioi q
  · simpa only [cutoffKernel, indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
      using abs_bernoulliRemainder_le (x - q)
  · simp [cutoffKernel, indicator_of_notMem hx]

theorem mellin_cutoffKernel_eq {q : ℝ} (hq : 0 < q) (s : ℂ) :
    mellin (cutoffKernel q) (-s - 1) = remainderIntegral q s := by
  simp_rw [mellin, cutoffKernel, ← indicator_smul, smul_eq_mul,
    integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hq.le)]
  unfold remainderIntegral
  congr 1
  funext x
  rw [show -s - 1 - 1 = -s - 2 by ring]
  exact mul_comm _ _

open Filter Topology Asymptotics in
theorem differentiableAt_remainderIntegral {q : ℝ} (hq : 0 < q) {s : ℂ}
    (hs : -1 < s.re) : DifferentiableAt ℂ (remainderIntegral q) s := by
  have hloc : LocallyIntegrable (cutoffKernel q) volume := by
    refine (locallyIntegrable_const (1 / 4 : ℝ)).mono
      (measurable_cutoffKernel q).aestronglyMeasurable ?_
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] using
      norm_cutoffKernel_le q x
  have htop : cutoffKernel q =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound (1 / 4) (Eventually.of_forall fun x => ?_)
    simpa using norm_cutoffKernel_le q x
  have hbot : cutoffKernel q =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-s.re - 2))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq)] with x hx
    have hn : x ∉ Ioi q := by
      change ¬q < x
      exact not_lt.mpr (le_of_lt hx)
    simp [cutoffKernel, indicator_of_notMem hn]
  have hm := mellin_differentiableAt_of_isBigO_rpow (s := -s - 1)
    (hloc.locallyIntegrableOn _) htop (by change -s.re - 1 < 0; linarith) hbot (by simp)
  have heq : remainderIntegral q = (fun z : ℂ => mellin (cutoffKernel q) (-z - 1)) :=
    funext (fun z => (mellin_cutoffKernel_eq hq z).symm)
  rw [heq]
  exact DifferentiableAt.comp (f := fun z : ℂ => -z - 1) s hm (by fun_prop)

theorem differentiableAt_eulerMaclaurinValue {q : ℝ} (hq : 0 < q) {s : ℂ}
    (hs : -1 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (eulerMaclaurinValue q) s := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hq0)
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) / (z - 1)) s :=
    (differentiableAt_const (q : ℂ)).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)
  exact (hpow.mul ((differentiableAt_const (1 / 2 : ℂ)).add hdiv)).sub
    (((differentiableAt_id.mul (differentiableAt_id.add_const 1)).div_const 2).mul
      (differentiableAt_remainderIntegral hq hs))


open Filter Topology in
private theorem hurwitzZeta_eq_eulerMaclaurinValue_on {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUdom : ∀ z ∈ U, -1 < z.re ∧ z ≠ 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hz₀re : 1 < z₀.re) :
    EqOn (HurwitzZeta.hurwitzZeta q) (eulerMaclaurinValue q) U := by
  have hf : DifferentiableOn ℂ (HurwitzZeta.hurwitzZeta q) U :=
    fun z hz => (HurwitzZeta.differentiableAt_hurwitzZeta q (hUdom z hz).2).differentiableWithinAt
  have hg : DifferentiableOn ℂ (eulerMaclaurinValue q) U :=
    fun z hz => (differentiableAt_eulerMaclaurinValue hq
      (hUdom z hz).1 (hUdom z hz).2).differentiableWithinAt
  apply (hf.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hU) hUc hz₀
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀re] with z hz
  exact hurwitzZeta_eq_eulerMaclaurinValue_of_one_lt_re hq hq1 hz

/-- Actual Hurwitz-zeta Euler--Maclaurin identity off the real axis, throughout
the half-plane needed for the shifted Mellin contours. -/
theorem hurwitzZeta_eq_eulerMaclaurinValue {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {s : ℂ} (hs : -1 < s.re) (him : s.im ≠ 0) :
    HurwitzZeta.hurwitzZeta q s = eulerMaclaurinValue q s := by
  rcases lt_or_gt_of_ne him with him | him
  · have hh := hurwitzZeta_eq_eulerMaclaurinValue_on hq hq1
      ({z : ℂ | -1 < z.re} ∩ {z : ℂ | z.im < 0})
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const))
      ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_im_lt 0)).isPreconnected
      (fun z hz => ⟨hz.1, by
        intro he
        have := hz.2
        simp [he] at this⟩)
      (z₀ := 2 - I) (by constructor <;> norm_num) (by norm_num)
    exact hh ⟨hs, him⟩
  · have hh := hurwitzZeta_eq_eulerMaclaurinValue_on hq hq1
      ({z : ℂ | -1 < z.re} ∩ {z : ℂ | 0 < z.im})
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im))
      ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_im_gt 0)).isPreconnected
      (fun z hz => ⟨hz.1, by
        intro he
        have := hz.2
        simp [he] at this⟩)
      (z₀ := 2 + I) (by constructor <;> norm_num) (by norm_num)
    exact hh ⟨hs, him⟩

/-- An explicit quadratic vertical-strip bound for the actual Hurwitz zeta,
with no growth hypothesis. -/
theorem norm_hurwitzZeta_strip_le {q a b r t : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (ha : -1 < a)
    (hr : r ∈ Icc a b) (ht : 1 ≤ |t|) :
    ‖HurwitzZeta.hurwitzZeta q ((r : ℂ) + t * I)‖ ≤
      (q ^ (-b) * (1 / 2 + q) +
        ((max |a| |b| + 1) * (max |a| |b| + 2) / 8) *
          (q ^ (-b - 1) / (a + 1))) * |t| ^ 2 := by
  rw [hurwitzZeta_eq_eulerMaclaurinValue hq hq1
    (by simpa using ha.trans_le hr.1) (by
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, add_zero, zero_add]
      intro he
      norm_num [he] at ht)]
  exact norm_eulerMaclaurinValue_strip_le hq hq1 ha hr ht


/-- Quadratic growth for every additive-circle parameter and every fixed
complex shift. Constants depend on the parameter, shift, and closed strip. -/
theorem exists_hurwitzZeta_shifted_strip_bound (c : UnitAddCircle) (α : ℂ) {a b : ℝ}
    (ha : -1 < a + α.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Icc a b, ∀ t : ℝ,
      2 * (1 + |α.im|) ≤ |t| →
      ‖HurwitzZeta.hurwitzZeta c ((r : ℂ) + t * I + α)‖ ≤ C * |t| ^ 2 := by
  obtain ⟨q, hq, hqc⟩ := AddCircle.eq_coe_Ioc c
  have hqpos : 0 < q := hq.1
  let B : ℝ := q ^ (-(b + α.re)) * (1 / 2 + q) +
    ((max |a + α.re| |b + α.re| + 1) *
      (max |a + α.re| |b + α.re| + 2) / 8) *
        (q ^ (-(b + α.re) - 1) / (a + α.re + 1))
  have ha1 : 0 < a + α.re + 1 := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(B + 1) * (1 + |α.im|) ^ 2, by positivity, ?_⟩
  intro r hr t ht
  have ht1 : 1 ≤ |t| := by nlinarith [abs_nonneg α.im]
  have hlow : 1 ≤ |t + α.im| := by
    have hh : |t| ≤ |t + α.im| + |α.im| := by
      simpa using abs_sub (t + α.im) α.im
    nlinarith [abs_nonneg α.im]
  have hupp : |t + α.im| ≤ (1 + |α.im|) * |t| := by
    have hh := abs_add_le t α.im
    nlinarith [abs_nonneg α.im]
  have hid : (r : ℂ) + t * I + α =
      ((r + α.re : ℝ) : ℂ) + ((t + α.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  rw [hid, ← hqc]
  have hbnd := norm_hurwitzZeta_strip_le (a := a + α.re) (b := b + α.re) hq.1 hq.2 ha
    (r := r + α.re) (t := t + α.im) ⟨by linarith [hr.1], by linarith [hr.2]⟩ hlow
  change ‖HurwitzZeta.hurwitzZeta q
    ((↑(r + α.re) : ℂ) + (↑(t + α.im) : ℂ) * I)‖ ≤ B * |t + α.im| ^ 2 at hbnd
  refine hbnd.trans ?_
  calc
    _ ≤ (B + 1) * ((1 + |α.im|) * |t|) ^ 2 := by gcongr <;> linarith
    _ = _ := by ring

end RiemannResearch.Analysis.HurwitzEulerMaclaurin
