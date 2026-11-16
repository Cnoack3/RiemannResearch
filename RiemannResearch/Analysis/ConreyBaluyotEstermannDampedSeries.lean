/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import RiemannResearch.Analysis.ConreyBaluyotEstermann

/-!
# Absolute convergence of the damped Estermann series

S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
equation (3.1.6), p. 95, defines the damped series on the upper half-plane.
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

For arbitrary complex shifts, a natural-number shift moves both exponents
into the absolute-convergence region. The exponential absorbs the resulting
powers by a factorial bound.
-/

open Complex
open scoped BigOperators

noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Terms of the exponentially damped Estermann series on the upper half-plane. -/
def estermannDampedTerm {K : ℕ} [NeZero K] (h : ZMod K) (α β w : ℂ) (p : ℕ × ℕ) : ℂ :=
  exp (2 * (Real.pi : ℂ) * I * (p.1 : ℂ) * (p.2 : ℂ) * w) * estermannTerm h α β p

/-- Baluyot's damped series S(w, α, β, H/K). -/
def estermannDampedSeries {K : ℕ} [NeZero K] (h : ZMod K) (α β w : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, estermannDampedTerm h α β w p

private theorem estermannTerm_shift_nat {K : ℕ} [NeZero K] (h : ZMod K) (α β : ℂ)
    (p : ℕ × ℕ) (N : ℕ) :
    estermannTerm h α β p = estermannTerm h (α + (N : ℂ)) (β + (N : ℂ)) p *
      ((p.1 : ℂ) ^ N * (p.2 : ℂ) ^ N) := by
  have hshift (u : ℂ) (m : ℕ) :
      LSeries.term (fun _ => (1 : ℂ)) u m =
        LSeries.term (fun _ => (1 : ℂ)) (u + (N : ℂ)) m * (m : ℂ) ^ N := by
    by_cases hm : m = 0
    · simp [hm]
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    simp only [LSeries.term_def, hm, if_false]
    rw [Complex.cpow_add _ _ hm', Complex.cpow_natCast, ← div_div,
      div_mul_cancel₀ _ (pow_ne_zero _ hm')]
  unfold estermannTerm
  rw [hshift α p.1, hshift β p.2]
  ring

private theorem norm_exp_estermannDamping (w : ℂ) (m n : ℕ) :
    ‖exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (n : ℂ) * w)‖ =
      Real.exp (-(2 * Real.pi * w.im * (m : ℝ) * (n : ℝ))) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem pow_mul_damping_le {r : ℝ} (hr : 0 < r) (m n N : ℕ) :
    (m : ℝ) ^ N * (n : ℝ) ^ N * Real.exp (-(r * (m : ℝ) * (n : ℝ))) ≤
      (N.factorial : ℝ) / r ^ N := by
  let x : ℝ := r * (m : ℝ) * (n : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hn : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hh := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp x hx N)
  have hx' := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg (-x))
  have hcancel : Real.exp x * (N.factorial : ℝ) * Real.exp (-x) = N.factorial := by
    calc
      _ = (N.factorial : ℝ) * (Real.exp x * Real.exp (-x)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [hcancel] at hx'
  apply (le_div_iff₀ (pow_pos hr N)).mpr
  calc
    _ = x ^ N * Real.exp (-x) := by dsimp [x]; rw [mul_pow, mul_pow]; ring
    _ ≤ N.factorial := hx'

/-- Absolute convergence of S for all shifts when the damping lies in the upper half-plane. -/
theorem summable_norm_estermannDampedTerm {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {w : ℂ} (hw : 0 < w.im) :
    Summable (fun p => ‖estermannDampedTerm h α β w p‖) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 - α.re) (1 - β.re))
  have hu : 1 < (α + (N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [(le_max_left (1 - α.re) (1 - β.re)).trans_lt hN]
  have hv : 1 < (β + (N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [(le_max_right (1 - α.re) (1 - β.re)).trans_lt hN]
  let r : ℝ := 2 * Real.pi * w.im
  have hr : 0 < r := by dsimp [r]; positivity
  have hs := (summable_norm_estermannTerm h hu hv).mul_right ((N.factorial : ℝ) / r ^ N)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hs
  calc
    ‖estermannDampedTerm h α β w p‖ =
        ‖estermannTerm h (α + (N : ℂ)) (β + (N : ℂ)) p‖ *
          ((p.1 : ℝ) ^ N * (p.2 : ℝ) ^ N *
            Real.exp (-(r * (p.1 : ℝ) * (p.2 : ℝ)))) := by
      unfold estermannDampedTerm
      rw [norm_mul, norm_exp_estermannDamping, estermannTerm_shift_nat h α β p N]
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_damping_le hr p.1 p.2 N) (norm_nonneg _)

/-- The actual damped double series can be summed in either order. -/
theorem estermannDampedSeries_eq_iterated_tsum {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {w : ℂ} (hw : 0 < w.im) :
    estermannDampedSeries h α β w = ∑' m : ℕ, ∑' n : ℕ, estermannDampedTerm h α β w (m, n) :=
  (summable_norm_estermannDampedTerm h α β hw).of_norm.tsum_prod


/-- Quantitative damping bound, uniform as Im(w) tends to zero.
The factor (Im(w))^(-N) is explicit; no compact-set lower bound is assumed. -/
theorem norm_estermannDampedTerm_le_shift {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) {w : ℂ} (hw : 0 < w.im) (p : ℕ × ℕ) (N : ℕ) :
    ‖estermannDampedTerm h α β w p‖ ≤
      ‖estermannTerm h (α+(N:ℂ)) (β+(N:ℂ)) p‖ *
        ((N.factorial : ℝ)/(2*Real.pi*w.im)^N) := by
  let r : ℝ := 2*Real.pi*w.im
  have hr : 0 < r := by dsimp [r]; positivity
  calc
    ‖estermannDampedTerm h α β w p‖ =
        ‖estermannTerm h (α+(N:ℂ)) (β+(N:ℂ)) p‖ *
          ((p.1 : ℝ)^N*(p.2 : ℝ)^N *
            Real.exp (-(r*(p.1 : ℝ)*(p.2 : ℝ)))) := by
      unfold estermannDampedTerm
      rw [norm_mul, norm_exp_estermannDamping, estermannTerm_shift_nat h α β p N]
      simp only [norm_mul, norm_pow, Complex.norm_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_mul_damping_le hr p.1 p.2 N) (norm_nonneg _)

end RiemannResearch.Analysis.ConreyBaluyot
