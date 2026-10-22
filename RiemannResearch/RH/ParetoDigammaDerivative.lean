/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoProgressionDigamma
import RiemannResearch.RH.ParetoProgressionMidpoint
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Identifying the Pareto midpoint series with the actual digamma derivative

Source: user-provided argument, 11 September 2026; standard digamma series
and recurrence, https://dlmf.nist.gov/5.15 and https://dlmf.nist.gov/5.5#E2.
All identifications use the actual `Complex.digamma` restricted to the real axis.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The actual derivative equals the concrete convergent reciprocal-square
series on the half-line containing every pole-removed CRT midpoint. -/
theorem hasDerivAt_re_digamma_reciprocalSquareSeries {x : ℝ} (hx : 1 / 2 < x) :
    HasDerivAt (fun y : ℝ => (Complex.digamma (y : ℂ)).re)
      (reciprocalSquareSeries x) x := by
  let g : ℕ → ℝ → ℝ := fun n y => 1 / ((n : ℝ) + y) - 1 / ((n : ℝ) + 1)
  let g' : ℕ → ℝ → ℝ := fun n y => -(1 / ((n : ℝ) + y)^2)
  let u : ℕ → ℝ := fun n => 4 * (1 / ((n : ℝ) + 1)^2)
  have hu : Summable u := (positivePSeries_summable 2 le_rfl).mul_left 4
  have hg (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioi (1 / 2 : ℝ)) :
      HasDerivAt (g n) (g' n y) y := by
    have hny : (n : ℝ) + y ≠ 0 := by
      have : 0 < y := lt_trans (by norm_num) hy
      positivity
    have hd := (((hasDerivAt_id y).const_add (n : ℝ)).inv hny).sub_const
      (1 / ((n : ℝ) + 1))
    convert hd using 1 <;> try rfl
    · funext t
      simp only [g, one_div, Pi.inv_apply, id_eq]
    · dsimp only [g', id_eq]
      ring
  have hbound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioi (1 / 2 : ℝ)) :
      ‖g' n y‖ ≤ u n := by
    have hy0 : 0 < y := lt_trans (by norm_num) hy
    have hny : 0 < (n : ℝ) + y := by positivity
    have hn1 : 0 < (n : ℝ) + 1 := by positivity
    change ‖-(1 / ((n : ℝ) + y)^2)‖ ≤ 4 * (1 / ((n : ℝ) + 1)^2)
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hny) (sq_pos_of_pos hn1)).mpr
    have hh : (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + y) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hy' : (1 / 2 : ℝ) < y := hy
      linarith
    nlinarith [sq_nonneg (2 * ((n : ℝ) + y) - ((n : ℝ) + 1))]
  have hs0 : Summable (fun n => g n x) :=
    (hasSum_reciprocal_difference_positive (lt_trans (by norm_num) hx)).summable
  have hds := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi
    (convex_Ioi (1 / 2 : ℝ)).isPreconnected hg hbound hx hs0 hx
  have hds' : HasDerivAt (fun y : ℝ => ∑' n : ℕ, g n y)
      (-(reciprocalSquareSeries x)) x := by
    simpa only [g', tsum_neg, reciprocalSquareSeries] using hds
  have hneg : HasDerivAt (fun y : ℝ => -(∑' n : ℕ, g n y) -
      Real.eulerMascheroniConstant) (reciprocalSquareSeries x) x := by
    convert hds'.neg.sub_const Real.eulerMascheroniConstant using 1 <;> try rfl
    simp only [neg_neg]
  apply hneg.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds (lt_trans (by norm_num) hx : (0 : ℝ) < x)]
    with y hy
  have he := (hasSum_reciprocal_difference_positive hy).tsum_eq
  change (Complex.digamma (y : ℂ)).re = -(∑' n : ℕ, g n y) -
    Real.eulerMascheroniConstant
  dsimp only [g]
  linarith

/-- The midpoint series is the derivative of the actual real restriction of ψ. -/
theorem reciprocalSquareSeries_eq_deriv_re_digamma {x : ℝ} (hx : 1 / 2 < x) :
    reciprocalSquareSeries x =
      deriv (fun y : ℝ => (Complex.digamma (y : ℂ)).re) x :=
  (hasDerivAt_re_digamma_reciprocalSquareSeries hx).deriv.symm

/-- Uniform midpoint Taylor formula using the actual digamma derivative,
with the exact first atom and the proved signed remainder. -/
theorem progressionWeight_uniform_digamma_midpoint (Q r : ℕ) (hQ : 0 < Q) :
    progressionWeight Q r = positiveWeight r +
      deriv (fun y : ℝ => (Complex.digamma (y : ℂ)).re)
        (1 + ((r : ℝ) + 1/2) / Q) / (Q : ℝ)^2 +
      progressionMidpointRemainder Q r ∧
    0 < progressionMidpointRemainder Q r ∧
    progressionMidpointRemainder Q r ≤ Real.pi^4 / (360 * (Q : ℝ)^4) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmid : (1 / 2 : ℝ) < 1 + ((r : ℝ) + 1/2) / Q := by
    have hp : 0 < ((r : ℝ) + 1/2) / Q := by positivity
    linarith
  have h := progressionWeight_uniform_midpoint Q r hQ
  rw [reciprocalSquareSeries_eq_deriv_re_digamma hmid] at h
  exact h

end
end RiemannResearch.RH.Pareto
