/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexMellinExponential
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Arbitrary-order bounds for the damped Gamma kernel on closed strips

For Re(lam)>0, the complex Laplace integral and the exact Gamma recurrence
give inverse-power decay of every sufficiently high integer order, uniformly
in the real coordinate on any fixed bounded strip. No Stirling estimate is
assumed. The strip may extend left of zero; the estimate excludes t=0.

The RH consumer is the Estermann Mellin shift in Baluyot, *On the Zeros of
Riemann's Zeta-function* (2017), Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supplies the contour setting. The recurrence proof here is an
independent formal derivation using the proved complex Laplace integral.
-/

open Complex Set
noncomputable section
namespace Complex

/-- Exact one-step recurrence, valid off zero without a real-part restriction. -/
theorem gamma_mul_cpow_neg_add_one_of_ne_zero {lam s : ℂ}
    (hlam : lam ≠ 0) (hs : s ≠ 0) :
    lam * (Gamma (s + 1) * lam ^ (-(s + 1))) =
      s * (Gamma s * lam ^ (-s)) := by
  have hp : lam * lam ^ (-(s + 1)) = lam ^ (-s) := by
    calc
      _ = lam ^ (1 : ℂ) * lam ^ (-(s + 1)) := by rw [cpow_one]
      _ = _ := by rw [← cpow_add _ _ hlam]; congr 1; ring
  rw [Gamma_add_one s hs]
  calc
    _ = s * Gamma s * (lam * lam ^ (-(s + 1))) := by ring
    _ = _ := by rw [hp]; ring

/-- Every recurrence step supplies one factor of the imaginary height. -/
theorem gamma_mul_cpow_neg_im_pow_bound {lam s : ℂ}
    (hlam : 0 < lam.re) (hsim : s.im ≠ 0) (n : ℕ)
    (hs : 0 < s.re + n) :
    ‖Gamma s * lam ^ (-s)‖ * |s.im| ^ n ≤
      ‖lam‖ ^ n * ((1 / lam.re) ^ (s.re + n) * Real.Gamma (s.re + n)) := by
  induction n generalizing s with
  | zero =>
      simpa using gamma_mul_cpow_neg_norm_le (s := s) (by simpa using hs) hlam
  | succ n ih =>
      have hlam0 : lam ≠ 0 := by intro h; simp [h] at hlam
      have hs0 : s ≠ 0 := by intro h; simp [h] at hsim
      have hs' : 0 < (s + 1).re + n := by
        simp only [add_re, one_re, Nat.cast_add, Nat.cast_one] at *
        linarith
      have hsim' : (s + 1).im ≠ 0 := by simpa using hsim
      have hb := ih hsim' hs'
      have he := congrArg norm (gamma_mul_cpow_neg_add_one_of_ne_zero hlam0 hs0)
      have he' : ‖lam‖ * ‖Gamma (s + 1) * lam ^ (-(s + 1))‖ =
          ‖s‖ * ‖Gamma s * lam ^ (-s)‖ := by simpa only [norm_mul] using he
      have harg : (s + 1).re + (n : ℝ) = s.re + (n + 1 : ℕ) := by
        simp; ring
      rw [harg] at hb
      calc
        _ = (|s.im| * ‖Gamma s * lam ^ (-s)‖) * |s.im| ^ n := by
          rw [pow_succ]; ring
        _ ≤ (‖s‖ * ‖Gamma s * lam ^ (-s)‖) * |s.im| ^ n := by
          gcongr
          exact abs_im_le_norm s
        _ = ‖lam‖ * (‖Gamma (s + 1) * lam ^ (-(s + 1))‖ * |(s+1).im| ^ n) := by
          rw [← he']; simp only [add_im, one_im, add_zero]; ring
        _ ≤ ‖lam‖ * (‖lam‖ ^ n *
            ((1 / lam.re) ^ (s.re + (n+1 : ℕ)) * Real.Gamma (s.re + (n+1 : ℕ)))) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := by rw [pow_succ]; ring

/-- Uniform inverse-power control on a fixed strip. The constants may depend on the
strip, damping, and order. Choosing larger n gives arbitrarily strong tail decay. -/
theorem exists_gamma_mul_cpow_neg_strip_pow_bound {lam : ℂ}
    (hlam : 0 < lam.re) {a b : ℝ} (n : ℕ) (ha : 0 < a + n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc a b, ∀ t : ℝ, t ≠ 0 →
      ‖Gamma ((r : ℂ) + t * I) * lam ^ (-((r : ℂ) + t * I))‖ * |t| ^ n ≤ C := by
  let f : ℝ → ℝ := fun r =>
    ‖lam‖ ^ n * ((1 / lam.re) ^ (r + n) * Real.Gamma (r + n))
  have hc : ContinuousOn f (Icc a b) := by
    intro r hr
    have hpos : 0 < r + n := by linarith [hr.1]
    have hg : ContinuousAt (fun x : ℝ => Real.Gamma (x + n)) r := by
      change ContinuousAt (fun x : ℝ => (Gamma ((x + n : ℝ) : ℂ)).re) r
      apply continuous_re.continuousAt.comp
      apply (continuousAt_Gamma _ ?_).comp (by fun_prop)
      intro m hm
      have hm' := congrArg Complex.re hm
      simp at hm'
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hp : ContinuousAt (fun x : ℝ => (1 / lam.re) ^ (x + n)) r := by
      apply ContinuousAt.rpow (by fun_prop) (by fun_prop)
      exact Or.inl (by positivity)
    exact (continuousAt_const.mul (hp.mul hg)).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr t ht
  have hb := gamma_mul_cpow_neg_im_pow_bound (s := (r:ℂ)+t*I) hlam
    (by simpa using ht) n (by
      simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
      linarith [hr.1])
  calc
    _ ≤ f r := by simpa [f] using hb
    _ ≤ ‖f r‖ := le_abs_self _
    _ ≤ C := hC r hr
    _ ≤ max C 0 := le_max_left _ _
end Complex
