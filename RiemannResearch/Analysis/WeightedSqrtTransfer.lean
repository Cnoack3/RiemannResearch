/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Weighted square-root transfer for signed integral pairings

The exact signed polarization is retained before Young's inequality.
The final convergence theorem needs an averaged defect and a bounded
reference pairing, rather than pointwise uniform convergence.
Source: elementary square-root polarization and Young's inequality,
assembled for the user's Montgomery transfer obligation. No asymptotic
or number-theoretic assumption enters these general inequalities.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.WeightedSqrtTransfer

theorem abs_sub_le_of_sqrt {r s d : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (h : |Real.sqrt r - Real.sqrt s| ≤ Real.sqrt d) :
    |r-s| ≤ d + 2 * Real.sqrt s * Real.sqrt d := by
  have ha : Real.sqrt r ≤ Real.sqrt s + Real.sqrt d := by
    have := (abs_le.mp h).2
    linarith
  calc
    |r-s| = |Real.sqrt r - Real.sqrt s| * (Real.sqrt r + Real.sqrt s) := by
      rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
        ← abs_mul]
      congr 1
      nlinarith [Real.sq_sqrt hr, Real.sq_sqrt hs]
    _ ≤ Real.sqrt d * (2 * Real.sqrt s + Real.sqrt d) := by
      apply mul_le_mul h
      · linarith
      · positivity
      · positivity
    _ = _ := by nlinarith [Real.sq_sqrt hd]

theorem abs_sub_le_young {r s d : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (h : |Real.sqrt r - Real.sqrt s| ≤ Real.sqrt d) {ε : ℝ} (hε : 0 < ε) :
    |r-s| ≤ ε*s + (1 + 1/ε)*d := by
  have hc : 2 * Real.sqrt s * Real.sqrt d ≤ ε*s + d/ε := by
    apply (mul_le_mul_iff_right₀ hε).mp
    have he : ε * (ε*s + d/ε) = ε^2*s+d := by field_simp [hε.ne']
    rw [he]
    nlinarith [sq_nonneg (ε * Real.sqrt s - Real.sqrt d),
      Real.sq_sqrt hs, Real.sq_sqrt hd]
  have hb := abs_sub_le_of_sqrt hr hs hd h
  simp only [div_eq_mul_inv] at hc ⊢
  nlinarith

theorem pairing_difference_eq (f r s : ℝ → ℝ)
    (hr : Integrable (fun x => f x * r x))
    (hs : Integrable (fun x => f x * s x)) :
    (∫ x, f x * r x) - (∫ x, f x * s x) = ∫ x, f x * (r x - s x) := by
  rw [← integral_sub hr hs]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem square_difference_exact {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    r-s = 2 * Real.sqrt s * (Real.sqrt r - Real.sqrt s) +
      (Real.sqrt r - Real.sqrt s)^2 := by
  nlinarith [Real.sq_sqrt hr, Real.sq_sqrt hs]

theorem pairing_difference_exact (f r s : ℝ → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hr : Continuous r) (hs : Continuous s)
    (hr0 : ∀ x, 0 ≤ r x) (hs0 : ∀ x, 0 ≤ s x) :
    (∫ x, f x * r x) - (∫ x, f x * s x) =
      2 * (∫ x, f x * Real.sqrt (s x) * (Real.sqrt (r x) - Real.sqrt (s x))) +
      (∫ x, f x * (Real.sqrt (r x) - Real.sqrt (s x))^2) := by
  have hir : Integrable (fun x => f x * r x) :=
    (hf.mul hr).integrable_of_hasCompactSupport hfc.mul_right
  have his : Integrable (fun x => f x * s x) :=
    (hf.mul hs).integrable_of_hasCompactSupport hfc.mul_right
  have hic : Integrable (fun x => f x * Real.sqrt (s x) *
      (Real.sqrt (r x) - Real.sqrt (s x))) :=
    ((hf.mul hs.sqrt).mul (hr.sqrt.sub hs.sqrt)).integrable_of_hasCompactSupport
      hfc.mul_right.mul_right
  have hiq : Integrable (fun x => f x * (Real.sqrt (r x) - Real.sqrt (s x))^2) :=
    (hf.mul ((hr.sqrt.sub hs.sqrt).pow 2)).integrable_of_hasCompactSupport hfc.mul_right
  rw [pairing_difference_eq f r s hir his, ← integral_const_mul,
    ← integral_add (hic.const_mul 2) hiq]
  apply integral_congr_ae
  filter_upwards with x
  rw [square_difference_exact (hr0 x) (hs0 x)]
  ring

theorem pairing_error_le_young (f r s d : ℝ → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hr : Continuous r) (hs : Continuous s) (hd : Continuous d)
    (hr0 : ∀ x, 0 ≤ r x) (hs0 : ∀ x, 0 ≤ s x) (hd0 : ∀ x, 0 ≤ d x)
    (h : ∀ x, |Real.sqrt (r x) - Real.sqrt (s x)| ≤ Real.sqrt (d x))
    {ε : ℝ} (hε : 0 < ε) :
    |(∫ x, f x * r x) - (∫ x, f x * s x)| ≤
      ε * (∫ x, |f x| * s x) + (1+1/ε) * (∫ x, |f x| * d x) := by
  have hir : Integrable (fun x => f x * r x) :=
    (hf.mul hr).integrable_of_hasCompactSupport hfc.mul_right
  have his : Integrable (fun x => f x * s x) :=
    (hf.mul hs).integrable_of_hasCompactSupport hfc.mul_right
  have hias : Integrable (fun x => |f x| * s x) :=
    (hf.abs.mul hs).integrable_of_hasCompactSupport hfc.abs.mul_right
  have hiad : Integrable (fun x => |f x| * d x) :=
    (hf.abs.mul hd).integrable_of_hasCompactSupport hfc.abs.mul_right
  rw [← integral_sub hir his]
  calc
    _ ≤ ∫ x, |f x * r x - f x * s x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, ε * (|f x| * s x) + (1+1/ε) * (|f x| * d x) := by
      apply integral_mono (hir.sub his).abs
        ((hias.const_mul ε).add (hiad.const_mul (1+1/ε)))
      intro x
      change |f x * r x - f x * s x| ≤
        ε * (|f x| * s x) + (1+1/ε) * (|f x| * d x)
      rw [← mul_sub, abs_mul]
      have hx := mul_le_mul_of_nonneg_left
        (abs_sub_le_young (hr0 x) (hs0 x) (hd0 x) (h x) hε) (abs_nonneg (f x))
      nlinarith
    _ = _ := by
      rw [integral_add (hias.const_mul ε) (hiad.const_mul (1+1/ε)),
        integral_const_mul, integral_const_mul]

theorem tendsto_zero_of_young_bounds (e S D : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hS : ∀ᶠ T in atTop, S T ≤ M)
    (hD : Tendsto D atTop (nhds 0))
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
      |e T| ≤ ε * S T + (1+1/ε) * D T) :
    Tendsto e atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let ε := δ / (2 * (M+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ε*M < δ/2 := by
    have heq : ε*(M+1) = δ/2 := by dsimp [ε]; field_simp
    nlinarith
  have hlim : Tendsto (fun T => (1+1/ε) * D T) atTop (nhds 0) := by
    simpa using hD.const_mul (1+1/ε)
  filter_upwards [hS, hbound ε hε, hlim.eventually_lt_const (by linarith : 0 < δ/2)]
    with T hST hb hDT
  have hh : |e T| < δ := by nlinarith
  simpa only [Real.dist_eq, sub_zero] using hh

end RiemannResearch.Analysis.WeightedSqrtTransfer
