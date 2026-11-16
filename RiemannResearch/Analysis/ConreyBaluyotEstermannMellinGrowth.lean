/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DampedGammaStripBounds
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinShift
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Polynomial-growth reduction for the Estermann Mellin shift

The Gamma/damping factor is now supplied by a proved arbitrary-order strip
bound. Any polynomial bound on the continued Estermann factor yields the
exact Cauchy tail required by the global contour theorem.

This is a conditional research reduction: the actual Estermann/Hurwitz
polynomial strip-growth provider remains open. Neither cofinal uniformity
nor the collision contour identity is assumed to follow automatically.

Source: the contour strategy of Baluyot, *On the Zeros of Riemann's
Zeta-function* (2017), Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
-/
open Complex Set
noncomputable section

namespace RiemannResearch.Analysis.ConreyBaluyot
/-- A polynomial Estermann bound plus the proved Gamma bound gives the actual kernel tail.
No assumption on distinctness of the shifts is needed for this implication. -/
theorem exists_estermannMellinKernel_tail_bound_of_polynomial_growth
    {K : ℕ} [NeZero K] (h : ZMod K) (α β : ℂ) {lam : ℂ}
    (hlam : 0 < lam.re) {a b C T₀ : ℝ} (ha : -1 < a)
    (n : ℕ) (hC : 0 ≤ C)
    (hgrowth : ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖estermann h ((r : ℂ) + t*I + α) ((r : ℂ) + t*I + β)‖ ≤ C * |t|^n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc a b, ∀ t : ℝ, max 1 T₀ ≤ |t| →
      ‖estermannMellinKernel h α β lam ((r : ℂ) + t*I)‖ ≤ B*(1+t^2)⁻¹ := by
  have hn : 0 < a + (n+2 : ℕ) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  obtain ⟨M, hM, hgamma⟩ := Complex.exists_gamma_mul_cpow_neg_strip_pow_bound
    hlam (b := b) (n+2) hn
  refine ⟨2*M*C, by positivity, ?_⟩
  intro r hr t ht
  have ht1 : 1 ≤ |t| := (le_max_left 1 T₀).trans ht
  have ht0 : t ≠ 0 := by intro he; norm_num [he] at ht1
  have htT : T₀ ≤ |t| := (le_max_right 1 T₀).trans ht
  have hg := hgamma r hr t ht0
  have hd := hgrowth r hr t htT
  have hsq : 1+t^2 ≤ 2*|t|^2 := by nlinarith [sq_abs t]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
  simp only [estermannMellinKernel, norm_mul]
  calc
    _ ≤ (‖Gamma ((r : ℂ)+t*I)‖ * ‖lam^(-((r : ℂ)+t*I))‖) *
        (C*|t|^n) * (2*|t|^2) := by gcongr
    _ = 2*C * (‖Gamma ((r : ℂ)+t*I) *
        lam^(-((r : ℂ)+t*I))‖ * |t|^(n+2)) := by
      rw [norm_mul, pow_add]; ring
    _ ≤ 2*C*M := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 2*M*C := by ring

/-- Conditional global shift whose sole substantive analytic input is polynomial
growth of the continued Estermann function on the closed strip. -/
theorem estermannDampedSeries_eq_residues_add_mellinIntegral_of_polynomial_growth
    {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) {α β w : ℂ}
    (hα : α.re < 1) (hβ : β.re < 1) (hne : α ≠ β) (hw : 0 < w.im)
    {a b C T₀ : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hbα : 1 < b + α.re) (hbβ : 1 < b + β.re) (n : ℕ) (hC : 0 ≤ C)
    (hgrowth : ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
      ‖estermann (h : ZMod K) ((r : ℂ)+t*I+α) ((r : ℂ)+t*I+β)‖ ≤ C*|t|^n) :
    estermannDampedSeries (h : ZMod K) α β w =
      estermannMellinResidueSum (h : ZMod K) α β (-2*(Real.pi : ℂ)*I*w) +
        (1/(2*(Real.pi : ℂ))) *
          ∫ t : ℝ, estermannMellinKernel (h : ZMod K) α β
            (-2*(Real.pi : ℂ)*I*w) ((a : ℂ)+I*t) := by
  have hlam : 0 < (-2*(Real.pi : ℂ)*I*w).re := by
    have he : (-2*(Real.pi : ℂ)*I*w).re = 2*Real.pi*w.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [he]
    positivity
  obtain ⟨B, _, hB⟩ := exists_estermannMellinKernel_tail_bound_of_polynomial_growth
    (h : ZMod K) α β hlam ha n hC hgrowth
  exact estermannDampedSeries_eq_residues_add_mellinIntegral_of_tail_bound
    h hα hβ hne hw ha ha0 hbα hbβ hB
end RiemannResearch.Analysis.ConreyBaluyot
