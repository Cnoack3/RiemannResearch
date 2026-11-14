/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermannDampedSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Integral exchange for Estermann Mellin representations

The actual absolutely convergent double series admits termwise integration
against any integrable vertical kernel. Exact vertical term norms supply the
majorant, and scalar inversion then identifies the actual damped series.

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
proof of Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the Mellin strategy. These general kernel statements
separate the Fubini argument from the scalar exponential inversion theorem.
-/

open Complex MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The actual Gamma–Estermann kernel, with a fixed complex damping parameter. -/
def estermannMellinKernel {K : ℕ} [NeZero K] (h : ZMod K) (α β lam s : ℂ) : ℂ :=
  Gamma s * lam ^ (-s) * estermann h (s + α) (s + β)

/-- Exact norm invariance along a shared vertical line. -/
theorem norm_estermannTerm_vertical {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (c t : ℝ) (p : ℕ × ℕ) :
    ‖estermannTerm h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β) p‖ =
      ‖estermannTerm h ((c : ℂ) + α) ((c : ℂ) + β) p‖ := by
  by_cases hm : p.1 = 0
  · simp [estermannTerm, LSeries.term_def, hm]
  by_cases hn : p.2 = 0
  · simp [estermannTerm, LSeries.term_def, hn]
  have hm' : 0 < (p.1 : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hn' : 0 < (p.2 : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simp [estermannTerm, hm, hn,
    ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hm',
    Complex.norm_cpow_eq_rpow_re_of_pos hn', Complex.mul_re]

/-- Each individual term varies continuously on the vertical line. -/
theorem continuous_estermannTerm_vertical {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (c : ℝ) (p : ℕ × ℕ) :
    Continuous (fun t : ℝ =>
      estermannTerm h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β) p) := by
  by_cases hm : p.1 = 0
  · simpa only [estermannTerm, LSeries.term_def, hm, ↓reduceIte, zero_mul, mul_zero]
      using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  by_cases hn : p.2 = 0
  · simpa only [estermannTerm, LSeries.term_def, hn, ↓reduceIte, zero_mul, mul_zero]
      using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  have hm' : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (p.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [estermannTerm, LSeries.term_def, hm, hn, if_false]
  apply Continuous.mul continuous_const
  apply Continuous.mul
  · apply Continuous.div continuous_const
    · exact (by fun_prop : Continuous (fun t : ℝ => (c : ℂ) + I * t + α)).const_cpow (.inl hm')
    · intro t; rw [Complex.cpow_def_of_ne_zero hm']; exact Complex.exp_ne_zero _
  · apply Continuous.div continuous_const
    · exact (by fun_prop : Continuous (fun t : ℝ => (c : ℂ) + I * t + β)).const_cpow (.inl hn')
    · intro t; rw [Complex.cpow_def_of_ne_zero hn']; exact Complex.exp_ne_zero _

/-- Every term is integrable against an arbitrary integrable kernel. -/
theorem integrable_mul_estermannTerm_vertical {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (c : ℝ) (p : ℕ × ℕ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ => f t *
      estermannTerm h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β) p) := by
  refine (hf.norm.mul_const ‖estermannTerm h ((c : ℂ) + α) ((c : ℂ) + β) p‖).mono'
    (hf.aestronglyMeasurable.mul
      (continuous_estermannTerm_vertical h α β c p).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun t => by
    rw [norm_mul, norm_estermannTerm_vertical]

/-- Absolute convergence justifies exchanging the vertical integral and double sum. -/
theorem integral_mul_estermann_eq_tsum_integral {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {c : ℝ} (hα : 1 < c + α.re) (hβ : 1 < c + β.re)
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ t : ℝ, f t * estermann h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β)) =
    ∑' p : ℕ × ℕ, ∫ t : ℝ, f t *
      estermannTerm h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β) p := by
  have ha : 1 < ((c : ℂ) + α).re := by simpa using hα
  have hb : 1 < ((c : ℂ) + β).re := by simpa using hβ
  have hint := integrable_mul_estermannTerm_vertical h α β c (f := f) (hf := hf)
  have hsum : Summable (fun p : ℕ × ℕ => ∫ t : ℝ, ‖f t *
      estermannTerm h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β) p‖) := by
    simp_rw [norm_mul, norm_estermannTerm_vertical, integral_mul_const]
    exact (summable_norm_estermannTerm h ha hb).mul_left _
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [← estermannSeries_eq_estermann h (by simpa using hα) (by simpa using hβ)]
    exact (tsum_mul_left).symm


/-- Exact common-shift factorization, also valid when an index is zero. -/
theorem estermannTerm_add_shift {K : ℕ} [NeZero K] (h : ZMod K)
    (s α β : ℂ) (p : ℕ × ℕ) :
    estermannTerm h (s + α) (s + β) p =
      ((p.1 : ℂ) * (p.2 : ℂ)) ^ (-s) * estermannTerm h α β p := by
  by_cases hm : p.1 = 0
  · simp [estermannTerm, LSeries.term_def, hm]
  by_cases hn : p.2 = 0
  · simp [estermannTerm, LSeries.term_def, hn]
  have hm' : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : (p.2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [estermannTerm, LSeries.term_def, hm, hn, if_false,
    Complex.cpow_add _ _ hm', Complex.cpow_add _ _ hn',
    Complex.natCast_mul_natCast_cpow, Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The continued function is continuous on a vertical line of absolute convergence. -/
theorem continuous_estermann_vertical {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {c : ℝ} (hα : 1 < c + α.re) (hβ : 1 < c + β.re) :
    Continuous (fun t : ℝ =>
      estermann h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hne (a : ℂ) (ha : 1 < c + a.re) : (c : ℂ) + I * t + a ≠ 1 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self, add_zero,
      Complex.one_re] at he'
    linarith
  have ha : ContinuousAt (fun s : ℂ => estermann h (s + α) (s + β))
      ((c : ℂ) + I * t) :=
    (analyticAt_estermann_shifted h α β (hne α hα) (hne β hβ)).continuousAt
  have hb : ContinuousAt (fun y : ℝ => (c : ℂ) + I * y) t := by fun_prop
  exact ha.comp (f := fun y : ℝ => (c : ℂ) + I * y) hb

/-- A constant vertical majorant given by the absolutely convergent norm sum. -/
theorem norm_estermann_vertical_le {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {c : ℝ} (hα : 1 < c + α.re) (hβ : 1 < c + β.re) (t : ℝ) :
    ‖estermann h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β)‖ ≤
      ∑' p : ℕ × ℕ, ‖estermannTerm h ((c : ℂ) + α) ((c : ℂ) + β) p‖ := by
  rw [← estermannSeries_eq_estermann h (by simpa using hα) (by simpa using hβ)]
  unfold estermannSeries
  calc
    _ ≤ ∑' p : ℕ × ℕ,
        ‖estermannTerm h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β) p‖ :=
      norm_tsum_le_tsum_norm (summable_norm_estermannTerm h
        (by simpa using hα) (by simpa using hβ))
    _ = _ := tsum_congr fun p => norm_estermannTerm_vertical h α β c t p

/-- The full continued Estermann function is integrable against the kernel. -/
theorem integrable_mul_estermann_vertical {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {c : ℝ} (hα : 1 < c + α.re) (hβ : 1 < c + β.re)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun t : ℝ =>
      f t * estermann h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β)) := by
  refine (hf.norm.mul_const
    (∑' p : ℕ × ℕ, ‖estermannTerm h ((c : ℂ) + α) ((c : ℂ) + β) p‖)).mono'
      (hf.aestronglyMeasurable.mul
        (continuous_estermann_vertical h α β hα hβ).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_estermann_vertical_le h α β hα hβ t) (norm_nonneg _)

/-- Scalar inversion and proved Fubini identify the actual damped double series. -/
theorem estermannDampedSeries_eq_integral_of_inversion {K : ℕ} [NeZero K] (h : ZMod K)
    (α β w : ℂ) {c : ℝ} (hα : 1 < c + α.re) (hβ : 1 < c + β.re)
    {f : ℝ → ℂ} (hf : Integrable f) (A : ℂ)
    (hinv : ∀ x : ℝ, 0 < x →
      exp (2 * (Real.pi : ℂ) * I * x * w) =
        A * ∫ t : ℝ, f t * (x : ℂ) ^ (-((c : ℂ) + I * t))) :
    estermannDampedSeries h α β w =
      A * ∫ t : ℝ, f t * estermann h ((c : ℂ) + I * t + α) ((c : ℂ) + I * t + β) := by
  rw [integral_mul_estermann_eq_tsum_integral h α β hα hβ hf, ← tsum_mul_left]
  unfold estermannDampedSeries
  apply tsum_congr
  intro p
  by_cases hm : p.1 = 0
  · simp [estermannDampedTerm, estermannTerm, LSeries.term_def, hm]
  by_cases hn : p.2 = 0
  · simp [estermannDampedTerm, estermannTerm, LSeries.term_def, hn]
  have hx : 0 < (p.1 : ℝ) * (p.2 : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  simp_rw [estermannTerm_add_shift, ← mul_assoc, integral_mul_const]
  unfold estermannDampedTerm
  have hi := hinv ((p.1 : ℝ) * (p.2 : ℝ)) hx
  push_cast at hi
  rw [← mul_assoc, ← hi]
  congr 2
  ring

end RiemannResearch.Analysis.ConreyBaluyot
