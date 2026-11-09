/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueCriticalGram
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import RiemannResearch.Analysis.GrowingFourierGramBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative critical-line Gram bounds on complete residue classes

The checked progression comparison reduces the error to the actual first
Mellin differences in one period. A second derivative bounds the cell-slope
error. The exact phase telescoping identity keeps the inverse ordinate-gap
term visible. The coefficient-weighted bound allows a moving family with
an explicit budget tending to zero.

Burnol's *A lower bound in an approximation problem involving the zeros of
the Riemann zeta function*, §5, motivates the finite Gram comparison.
The quantitative progression estimate here uses the repository's own
weighted residue coordinates. https://arxiv.org/abs/math/0103058
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

open Set
open RiemannResearch.Analysis.Cesaro (power_hasDerivAt)

/-- A uniform first-order Taylor estimate for the actual dimensionless slope,
including purely imaginary exponents used by the phase telescoping identity. -/
theorem cellSlope_sub_le (s : ℂ) (hs : 0 ≤ s.re) (n : ℕ) :
    ‖cellSlope s n - s‖ ≤ ‖s‖ * ‖s + 1‖ / ((n : ℝ) + 1) := by
  let h : ℝ := 1 / ((n : ℝ) + 1)
  have hh : 0 < h := by dsimp [h]; positivity
  have hs1 : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hp (x : ℝ) (hx : 1 ≤ x) :
      ‖(x : ℂ) ^ (-(s + 1)) - 1‖ ≤ ‖s + 1‖ * (x - 1) := by
    have hd : ∀ y ∈ Icc 1 x,
        HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (-(s + 1)))
          (-(s + 1) * (y : ℂ) ^ (-(s + 1) - 1)) (Icc 1 x) y :=
      fun y hy => (power_hasDerivAt (s + 1) hs1 y
        (zero_lt_one.trans_le hy.1)).hasDerivWithinAt
    have hb : ∀ y ∈ Ico 1 x, ‖-(s + 1) * (y : ℂ) ^ (-(s + 1) - 1)‖ ≤ ‖s + 1‖ := by
      intro y hy
      rw [norm_mul, norm_neg,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hy.1)]
      apply mul_le_of_le_one_right (norm_nonneg _)
      apply Real.rpow_le_one_of_one_le_of_nonpos hy.1
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    simpa only [Complex.ofReal_one, Complex.one_cpow] using
      norm_image_sub_le_of_norm_deriv_le_segment' hd hb x ⟨hx, le_rfl⟩
  let g (x : ℝ) : ℂ := 1 - (x : ℂ) ^ (-s) - s * ((x : ℂ) - 1)
  have hd (x : ℝ) (hx : x ∈ Icc 1 (1 + h)) :
      HasDerivWithinAt g (s * ((x : ℂ) ^ (-(s + 1)) - 1)) (Icc 1 (1 + h)) x := by
    have hx0 := zero_lt_one.trans_le hx.1
    have hw : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        (-s * (x : ℂ) ^ (-s - 1)) x := by
      by_cases hzero : s = 0
      · simp [hzero, hasDerivAt_const]
      · exact hasDerivAt_ofReal_cpow_const hx0.ne' (neg_ne_zero.mpr hzero)
    have hlin : HasDerivAt (fun y : ℝ => s * ((y : ℂ) - 1)) s x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).sub_const (1 : ℂ)).const_mul s
    have hdg := (((hasDerivAt_const x (1 : ℂ)).sub hw).sub hlin).hasDerivWithinAt
      (s := Icc 1 (1 + h))
    have he : (0 : ℂ) - -s * (x : ℂ) ^ (-s - 1) - s =
        s * ((x : ℂ) ^ (-(s + 1)) - 1) := by
      rw [show -(s + 1) = -s - 1 by ring]
      ring
    rw [he] at hdg
    exact hdg
  have hb (x : ℝ) (hx : x ∈ Ico 1 (1 + h)) :
      ‖s * ((x : ℂ) ^ (-(s + 1)) - 1)‖ ≤ ‖s‖ * ‖s + 1‖ * h := by
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((hp x hx.1).trans (mul_le_mul_of_nonneg_left (by linarith [hx.2]) (norm_nonneg _)))
      (norm_nonneg _)
  have hg := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + h) ⟨by linarith, le_rfl⟩
  have hg1 : g 1 = 0 := by simp [g]
  rw [hg1, sub_zero, add_sub_cancel_left] at hg
  have hcast : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hm : cellSlope s n - s = ((n : ℂ) + 1) * g (1 + h) := by
    have hhC : ((n : ℂ) + 1) * (h : ℂ) = 1 := by
      dsimp only [h]
      push_cast
      field_simp
    have he : g (1 + h) = 1 - (((1 + h : ℝ) : ℂ) ^ (-s)) - s * (h : ℂ) := by
      dsimp only [g]
      push_cast
      ring
    rw [he, mul_sub, mul_left_comm ((n : ℂ) + 1) s, hhC, mul_one]
    rfl
  rw [hm, norm_mul, hcast]
  calc
    _ ≤ ((n : ℝ) + 1) * (‖s‖ * ‖s + 1‖ * h * h) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by dsimp only [h]; field_simp

/-- Summable error constant in the quantitative logarithmic cross bounds. -/
def reciprocalSquareMass : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2

private theorem reciprocalSquare_summable :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : -(2 : ℝ) < -1))
  refine h.congr (fun n => ?_)
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_two, one_div]

private theorem sum_reciprocalSquare_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ^ 2) ≤ reciprocalSquareMass :=
  reciprocalSquare_summable.sum_le_tsum _ (fun n _ => by positivity)

/-- The summable phase discretization error, with its vanishing frequency factor. -/
theorem phaseSlopeError_sum_bound (v : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phaseSlopeError v n / ((n : ℂ) + 1)‖ ≤
      |v| * ‖(v : ℂ) * Complex.I + 1‖ * reciprocalSquareMass := by
  let s : ℂ := (v : ℂ) * Complex.I
  have hs : s.re = 0 := by simp [s, Complex.mul_re]
  have hn : ‖s‖ = |v| := by simp [s, Real.norm_eq_abs]
  have he (n : ℕ) :
      ‖phaseSlopeError v n / ((n : ℂ) + 1)‖ ≤
        (|v| * ‖s + 1‖) * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hc : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [norm_div, hc, phaseSlopeError, norm_mul, powerPhase_norm, one_mul]
    change ‖cellSlope s n - s‖ / ((n : ℝ) + 1) ≤ _
    calc
      _ ≤ (‖s‖ * ‖s + 1‖ / ((n : ℝ) + 1)) / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_right (cellSlope_sub_le s hs.ge n) (by positivity)
      _ = _ := by rw [hn, div_div, ← pow_two, div_eq_mul_inv, one_div]
  have hsum : ‖∑ n ∈ Finset.range N, phaseSlopeError v n / ((n : ℂ) + 1)‖ ≤
      |v| * ‖s + 1‖ * reciprocalSquareMass := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖phaseSlopeError v n / ((n : ℂ) + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N,
          (|v| * ‖s + 1‖) * (1 / ((n : ℝ) + 1) ^ 2) :=
        Finset.sum_le_sum (fun n _ => he n)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_reciprocalSquare_le N) (by positivity)
  exact hsum

def phaseSumBudget (v : ℝ) : ℝ :=
  if v = 0 then 1 else 2 / |v| + reciprocalSquareMass * ‖(v : ℂ) * Complex.I + 1‖

/-- Explicit frequency dependence of the finite harmonic phase sums.
The small-gap cost is inverse linear, and the large-frequency cost is linear. -/
theorem harmonicPhaseSum_sub_diag_le (v : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - (v : ℂ) * Complex.I)) -
        (if v = 0 then (Real.log ((N : ℝ) + 1) : ℂ) else 0)‖ ≤ phaseSumBudget v := by
  by_cases hv : v = 0
  · subst v
    have hH : (∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹) = (harmonic N : ℝ) := by
      simp [harmonic]
    have hC : (∑ n ∈ Finset.range N, ((n : ℂ) + 1)⁻¹) = ((harmonic N : ℝ) : ℂ) := by
      rw [← hH]
      push_cast
      rfl
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, Complex.cpow_neg_one,
      phaseSumBudget, ite_true, hC, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hlo : Real.log ((N : ℝ) + 1) ≤ (harmonic N : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
    have hhi := harmonic_le_one_add_log N
    have hm : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) := by
      by_cases hN : N = 0
      · simp [hN]
      · exact Real.log_le_log (by positivity : 0 < (N : ℝ)) (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  · rw [if_neg hv, sub_zero, phaseSumBudget, if_neg hv]
    have hsum := phaseSlopeError_sum_bound v N
    have ht : ‖(1 : ℂ) - powerPhase v N‖ ≤ 2 := by
      simpa only [norm_one, powerPhase_norm, one_add_one_eq_two] using
        norm_sub_le (1 : ℂ) (powerPhase v N)
    have h := (norm_sub_le ((1 : ℂ) - powerPhase v N) _).trans (add_le_add ht hsum)
    have hnorm : ‖(v : ℂ) * Complex.I‖ = |v| := by simp [Real.norm_eq_abs]
    rw [← phase_sum_exact, norm_mul, hnorm] at h
    by_contra! hbad
    change 2 / |v| + reciprocalSquareMass * ‖(v : ℂ) * Complex.I + 1‖ < _ at hbad
    have heq : |v| * (2 / |v| + reciprocalSquareMass * ‖(v : ℂ) * Complex.I + 1‖) =
        2 + |v| * ‖(v : ℂ) * Complex.I + 1‖ * reciprocalSquareMass := by
      field_simp [(abs_pos.mpr hv).ne']
    have hbad' := mul_lt_mul_of_pos_left hbad (abs_pos.mpr hv)
    rw [heq] at hbad'
    exact (not_lt_of_ge h) hbad'

end RiemannResearch.RH.Pareto.SpectralObstruction

namespace RiemannResearch.RH.Pareto.ResidueMellin
open SpectralObstruction
open MellinFrequency (criticalPoint)

private theorem norm_nat_succ_complex (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

private theorem crossSlope_sub_le (t u : ℝ) (n : ℕ) :
    ‖crossSlope t u n - criticalPoint t * star (criticalPoint u)‖ ≤
      ‖criticalPoint t‖ * ‖criticalPoint u‖ *
        (1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖) / ((n : ℝ) + 1) := by
  let s := criticalPoint t
  let v := criticalPoint u
  let a := cellSlope s n
  let b := cellSlope v n
  let x := (n : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have ha : ‖a‖ ≤ ‖s‖ := cellSlope_norm_le s (by simp [s]) n
  have hb : ‖b‖ ≤ ‖v‖ := cellSlope_norm_le v (by simp [v]) n
  have hd :
      crossSlope t u n - s * star v =
        a * star b / ((n : ℂ) + 1) + ((a - s) * star b + s * star (b - v)) := by
    rw [crossSlope, star_sub]
    change (1 + 1 / ((n : ℂ) + 1)) * a * star b - s * star v = _
    ring
  have h₁ : ‖a * star b / ((n : ℂ) + 1)‖ ≤ ‖s‖ * ‖v‖ / x := by
    rw [norm_div, norm_mul, norm_star, norm_nat_succ_complex]
    exact div_le_div_of_nonneg_right (mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)) hx.le
  have h₂ : ‖(a - s) * star b‖ ≤ (‖s‖ * ‖s + 1‖ / x) * ‖v‖ := by
    rw [norm_mul, norm_star]
    exact mul_le_mul (cellSlope_sub_le s (by simp [s]) n) hb (norm_nonneg _) (by positivity)
  have h₃ : ‖s * star (b - v)‖ ≤ ‖s‖ * (‖v‖ * ‖v + 1‖ / x) := by
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (cellSlope_sub_le v (by simp [v]) n) (norm_nonneg _)
  rw [hd]
  calc
    _ ≤ ‖a * star b / ((n : ℂ) + 1)‖ + (‖(a - s) * star b‖ + ‖s * star (b - v)‖) :=
      (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_add_le _ _))
    _ ≤ ‖s‖ * ‖v‖ / x + ((‖s‖ * ‖s + 1‖ / x) * ‖v‖ +
        ‖s‖ * (‖v‖ * ‖v + 1‖ / x)) := add_le_add h₁ (add_le_add h₂ h₃)
    _ = _ := by change _ = ‖s‖ * ‖v‖ * (1 + ‖s + 1‖ + ‖v + 1‖) / x; ring

private theorem crossSlopeError_sum_le (t u : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, crossSlopeError t u n / ((n : ℂ) + 1)‖ ≤
      ‖criticalPoint t‖ * ‖criticalPoint u‖ *
        (1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖) * reciprocalSquareMass := by
  let A := ‖criticalPoint t‖ * ‖criticalPoint u‖ *
    (1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖)
  have hterm (n : ℕ) :
      ‖crossSlopeError t u n / ((n : ℂ) + 1)‖ ≤ A * (1 / ((n : ℝ) + 1) ^ 2) := by
    rw [norm_div, norm_nat_succ_complex, crossSlopeError, norm_mul, powerPhase_norm, one_mul]
    exact (div_le_div_of_nonneg_right (crossSlope_sub_le t u n) (by positivity)).trans_eq
      (by rw [div_div, ← pow_two, div_eq_mul_inv, one_div])
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖crossSlopeError t u n / ((n : ℂ) + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, A * (1 / ((n : ℝ) + 1) ^ 2) :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_reciprocalSquare_le N) (by dsimp [A]; positivity)

/-- The complete progression Gram differs from the oscillatory harmonic
model by a summable error. This version retains the full phase sum. -/
theorem classCrossSum_sub_phaseSum_le (t u : ℝ) (N : ℕ) :
    ‖classCrossSum t u N - (criticalPoint t * star (criticalPoint u)) *
      (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - ((t - u : ℝ) : ℂ) * Complex.I))‖ ≤
      ‖criticalPoint t‖ * ‖criticalPoint u‖ *
        (2 * (1 + criticalTailMass) ^ 2 +
          reciprocalSquareMass * (1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖)) := by
  let a := criticalPoint t * star (criticalPoint u)
  let W := fun n : ℕ => ((n : ℂ) + 1) ^ (-1 - ((t - u : ℝ) : ℂ) * Complex.I)
  have hterm (n : ℕ) : firstCrossTerm t u n =
      a * W n + crossSlopeError t u n / ((n : ℂ) + 1) := by
    rw [firstCrossTerm_eq, criticalCross_term_eq]
    dsimp only [W, a]
    rw [powerPhase_div, crossSlopeError]
    ring
  have hraw : (∑ n ∈ Finset.range N, firstCrossTerm t u n) =
      a * (∑ n ∈ Finset.range N, W n) +
        ∑ n ∈ Finset.range N, crossSlopeError t u n / ((n : ℂ) + 1) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  change ‖classCrossSum t u N - a * ∑ n ∈ Finset.range N, W n‖ ≤ _
  rw [show classCrossSum t u N - a * ∑ n ∈ Finset.range N, W n =
      (classCrossSum t u N - ∑ n ∈ Finset.range N, firstCrossTerm t u n) +
        ∑ n ∈ Finset.range N, crossSlopeError t u n / ((n : ℂ) + 1) by rw [hraw]; ring]
  exact ((norm_add_le _ _).trans (add_le_add (classCrossSum_firstPeriod_bound t u N)
    (crossSlopeError_sum_le t u N))).trans_eq (by ring)

/-- Explicit complete-period error budget for two critical ordinates. -/
def criticalCrossBudget (t u : ℝ) : ℝ :=
  2 * (1 + criticalTailMass) ^ 2 +
    reciprocalSquareMass * (1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖) +
    phaseSumBudget (t - u)

/-- Quantitative version of the grouped cross-Gram limit. It is uniform in the
modulus and retains its explicit dependence on height and ordinate separation. -/
theorem classCrossSum_sub_diag_le (t u : ℝ) (N : ℕ) :
    ‖classCrossSum t u N -
      (if t = u then criticalPoint t * star (criticalPoint u) else 0) *
        (Real.log ((N : ℝ) + 1) : ℂ)‖ ≤
      ‖criticalPoint t‖ * ‖criticalPoint u‖ * criticalCrossBudget t u := by
  let a := criticalPoint t * star (criticalPoint u)
  let W := fun n : ℕ => ((n : ℂ) + 1) ^ (-1 - ((t - u : ℝ) : ℂ) * Complex.I)
  let logL : ℂ := (Real.log ((N : ℝ) + 1) : ℂ)
  let diag := if t = u then logL else 0
  have hd : (if t = u then a else 0) * logL = a * diag := by
    by_cases h : t = u <;> simp [h, diag]
  have hphase : ‖(∑ n ∈ Finset.range N, W n) - diag‖ ≤ phaseSumBudget (t - u) := by
    simpa only [W, diag, logL, sub_eq_zero] using harmonicPhaseSum_sub_diag_le (t - u) N
  have hmul : ‖a * ((∑ n ∈ Finset.range N, W n) - diag)‖ ≤
      ‖criticalPoint t‖ * ‖criticalPoint u‖ * phaseSumBudget (t - u) := by
    rw [norm_mul, show ‖a‖ = ‖criticalPoint t‖ * ‖criticalPoint u‖ by simp [a]]
    exact mul_le_mul_of_nonneg_left hphase (by positivity)
  change ‖classCrossSum t u N - (if t = u then a else 0) * logL‖ ≤ _
  rw [hd, show classCrossSum t u N - a * diag =
      (classCrossSum t u N - a * ∑ n ∈ Finset.range N, W n) +
      a * ((∑ n ∈ Finset.range N, W n) - diag) by ring]
  refine ((norm_add_le _ _).trans
    (add_le_add (classCrossSum_sub_phaseSum_le t u N) hmul)).trans_eq ?_
  unfold criticalCrossBudget
  ring

theorem classCross_error_le (t u : ℝ) (N : ℕ) (hN : 0 < N) :
    ‖classCross t u N - (if t = u then criticalPoint t * star (criticalPoint u) else 0)‖ ≤
      ‖criticalPoint t‖ * ‖criticalPoint u‖ * criticalCrossBudget t u /
        Real.log ((N : ℝ) + 1) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  have hC := Complex.ofReal_ne_zero.mpr hlog.ne'
  have h := classCrossSum_sub_diag_le t u N
  have he (x y : ℂ) : x / (Real.log ((N : ℝ) + 1) : ℂ) - y =
      (x - y * (Real.log ((N : ℝ) + 1) : ℂ)) / (Real.log ((N : ℝ) + 1) : ℂ) := by
    field_simp [hC]
  rw [classCross, he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  simpa only [mul_comm (Real.log ((N : ℝ) + 1) : ℂ)] using
    div_le_div_of_nonneg_right h hlog.le

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin
open Filter
open MellinFrequency (criticalPoint)
open RiemannResearch.Fourier (finiteGramErrorPairing)

variable {ι : Type*}

/-- The absolute coefficient-weighted error budget for the actual grouped
complex Gram. Its double sum keeps the individual near-frequency costs. -/
def criticalGramWeightedBudget (s : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ s, ∑ j ∈ s, ‖a i‖ * ‖a j‖ *
    (‖criticalPoint (u i)‖ * ‖criticalPoint (u j)‖ * criticalCrossBudget (u i) (u j))) /
    Real.log ((N : ℝ) + 1)

theorem critical_gram_pairing_error_le (s : Finset ι) (a : ι → ℂ)
    (u : ι → ℝ) (N : ℕ) (hN : 0 < N) :
    ‖finiteGramErrorPairing s a (fun i j => classCross (u i) (u j) N -
        (if u i = u j then criticalPoint (u i) * star (criticalPoint (u j)) else 0))‖ ≤
      criticalGramWeightedBudget s a u N := by
  unfold finiteGramErrorPairing
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (a i) *
        (classCross (u i) (u j) N -
          (if u i = u j then criticalPoint (u i) * star (criticalPoint (u j)) else 0)) * a j‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ criticalGramWeightedBudget s a u N := by
      unfold criticalGramWeightedBudget
      simp only [Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_star]
      have hb := classCross_error_le (u i) (u j) N hN
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring)

/-- A moving finite collection can grow with the cutoff. The sufficient
hypothesis is decay of its explicit weighted Gram budget. -/
theorem growing_critical_gram_pairing_error_tendsto_zero (s : ℕ → Finset ι)
    (a : ℕ → ι → ℂ) (u : ℕ → ι → ℝ) (N : ℕ → ℕ)
    (hN : ∀ᶠ k in atTop, 0 < N k)
    (hB : Tendsto (fun k => criticalGramWeightedBudget (s k) (a k) (u k) (N k)) atTop (𝓝 0)) :
    Tendsto (fun k => finiteGramErrorPairing (s k) (a k) (fun i j =>
        classCross (u k i) (u k j) (N k) -
          (if u k i = u k j then criticalPoint (u k i) * star (criticalPoint (u k j)) else 0)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (hN.mono (fun k hk => critical_gram_pairing_error_le (s k) (a k) (u k) (N k) hk)) hB

end RiemannResearch.RH.Pareto.ResidueMellin
