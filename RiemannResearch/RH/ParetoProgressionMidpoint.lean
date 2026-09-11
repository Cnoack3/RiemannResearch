/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoProgressionTaylor

/-!
# A uniform midpoint approximation for Pareto progression weights

Source: the user discussion of the Pareto/CRT weights, 11 September 2026.
Removing the first Pareto atom before taking a midpoint gives a uniform
inverse-fourth-power error. The proof is an exact reciprocal-product identity,
so it does not assume any unproved identification with a digamma derivative.
`reciprocalSquareSeries` is the standard positive trigamma series, used here
only through its explicit convergent definition.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The positive reciprocal-square series appearing in the midpoint formula. -/
def reciprocalSquareSeries (x : ℝ) : ℝ := ∑' j : ℕ, 1 / ((j : ℝ) + x)^2

/-- Convergence on the interval used in the pole-removed midpoint formula. -/
theorem reciprocalSquareSeries_summable {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun j : ℕ => 1 / ((j : ℝ) + x)^2) := by
  apply Summable.of_nonneg_of_le (fun j => by positivity) _
    (positivePSeries_summable 2 le_rfl)
  intro j
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

private theorem midpoint_kernel_difference (A r : ℝ) (hA : 0 < A) (hr : 0 ≤ r) :
    1 / ((A+r)*(A+r+1)) - 1 / (A+r+1/2)^2 =
      1 / (4 * (A+r+1/2)^2 * ((A+r)*(A+r+1))) := by
  have h0 : A+r ≠ 0 := by positivity
  have h1 : A+r+1 ≠ 0 := by positivity
  have hm : A+r+1/2 ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem midpoint_kernel_difference_pos (A r : ℝ) (hA : 0 < A)
    (hr : 0 ≤ r) :
    0 < 1 / ((A+r)*(A+r+1)) - 1 / (A+r+1/2)^2 := by
  rw [midpoint_kernel_difference A r hA hr]
  positivity

private theorem midpoint_kernel_difference_le (A r : ℝ) (hA : 0 < A)
    (hr : 0 ≤ r) :
    1 / ((A+r)*(A+r+1)) - 1 / (A+r+1/2)^2 ≤ (1/4) * (1 / A^4) := by
  rw [midpoint_kernel_difference A r hA hr]
  have h0 : A^2 ≤ (A+r+1/2)^2 := by nlinarith
  have h1 : A^2 ≤ (A+r)*(A+r+1) := by nlinarith
  have h2 := mul_le_mul h0 h1 (sq_nonneg A) (by positivity : 0 ≤ (A+r+1/2)^2)
  have hd : 4*A^4 ≤ 4*(A+r+1/2)^2*((A+r)*(A+r+1)) := by nlinarith [h2]
  calc
    _ ≤ 1 / (4*A^4) := one_div_le_one_div_of_le (by positivity) hd
    _ = _ := by ring

private def progressionMidpointTerm (Q r j : ℕ) : ℝ :=
  1 / ((Q : ℝ)*((j : ℝ)+1) + r + 1/2)^2

private theorem progressionMidpointTerm_summable (Q r : ℕ) (hQ : 0 < Q) :
    Summable (progressionMidpointTerm Q r) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hs : Summable (fun j : ℕ => 1 / ((Q : ℝ)*((j : ℝ)+1))^2) := by
    apply ((positivePSeries_summable 2 le_rfl).mul_left (1 / (Q : ℝ)^2)).congr
    intro j
    change (1 / (Q : ℝ)^2) * (1 / ((j : ℝ)+1)^2) =
      1 / ((Q : ℝ)*((j : ℝ)+1))^2
    rw [mul_pow]
    exact one_div_mul_one_div _ _
  apply Summable.of_nonneg_of_le (fun j => by unfold progressionMidpointTerm; positivity) _ hs
  intro j
  unfold progressionMidpointTerm
  apply one_div_le_one_div_of_le (by positivity)
  have hA : 0 < (Q : ℝ)*((j : ℝ)+1) := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

private theorem progressionMidpointTerm_tsum (Q r : ℕ) (hQ : 0 < Q) :
    (∑' j, progressionMidpointTerm Q r j) =
      reciprocalSquareSeries (1 + ((r : ℝ)+1/2)/Q) / (Q : ℝ)^2 := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have he (j : ℕ) : progressionMidpointTerm Q r j =
      (1 / (Q : ℝ)^2) * (1 / ((j : ℝ) + (1 + ((r : ℝ)+1/2)/Q))^2) := by
    unfold progressionMidpointTerm
    have h1 : (Q : ℝ)*((j : ℝ)+1)+(r : ℝ)+1/2 ≠ 0 := by positivity
    have h2 : (j : ℝ)+(1+((r : ℝ)+1/2)/Q) ≠ 0 := by positivity
    field_simp
    <;> ring
  simp_rw [he]
  rw [tsum_mul_left]
  unfold reciprocalSquareSeries
  ring

/-- The error after preserving the first atom and taking the midpoint of the
remaining reciprocal-difference series. -/
def progressionMidpointRemainder (Q r : ℕ) : ℝ :=
  progressionWeight Q r - positiveWeight r -
    reciprocalSquareSeries (1 + ((r : ℝ)+1/2)/Q) / (Q : ℝ)^2

private def progressionMidpointErrorTerm (Q r j : ℕ) : ℝ :=
  positiveWeight (r+Q+Q*j) - progressionMidpointTerm Q r j

private theorem progressionMidpointErrorTerm_summable (Q r : ℕ) (hQ : 0 < Q) :
    Summable (progressionMidpointErrorTerm Q r) :=
  (progressionWeight_summable Q (r+Q) hQ).sub
    (progressionMidpointTerm_summable Q r hQ)

private theorem progressionMidpointErrorTerm_formula (Q r j : ℕ) :
    progressionMidpointErrorTerm Q r j =
      1 / (((Q : ℝ)*((j : ℝ)+1)+r)*((Q : ℝ)*((j : ℝ)+1)+r+1)) -
      1 / ((Q : ℝ)*((j : ℝ)+1)+r+1/2)^2 := by
  unfold progressionMidpointErrorTerm progressionMidpointTerm positiveWeight
  push_cast
  congr 2 <;> ring

private theorem progressionMidpointRemainder_tsum (Q r : ℕ) (hQ : 0 < Q) :
    progressionMidpointRemainder Q r = ∑' j, progressionMidpointErrorTerm Q r j := by
  unfold progressionMidpointRemainder progressionMidpointErrorTerm
  rw [Summable.tsum_sub (progressionWeight_summable Q (r+Q) hQ)
    (progressionMidpointTerm_summable Q r hQ), progressionMidpointTerm_tsum Q r hQ]
  change progressionWeight Q r - positiveWeight r - _ = progressionWeight Q (r+Q) - _
  rw [progressionWeight_split Q r hQ]
  ring

/-- The midpoint error is positive and uniformly bounded independently of r.
In particular this is valid simultaneously over every residue of a growing CRT chart. -/
theorem progressionMidpointRemainder_bounds (Q r : ℕ) (hQ : 0 < Q) :
    0 < progressionMidpointRemainder Q r ∧
      progressionMidpointRemainder Q r ≤ Real.pi^4 / (360*(Q : ℝ)^4) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hterm (j : ℕ) : 0 < progressionMidpointErrorTerm Q r j := by
    rw [progressionMidpointErrorTerm_formula]
    exact midpoint_kernel_difference_pos _ _ (by positivity) (by positivity)
  rw [progressionMidpointRemainder_tsum Q r hQ]
  constructor
  · have hle := (progressionMidpointErrorTerm_summable Q r hQ).sum_le_tsum
      ({0} : Finset ℕ) (fun j _ => (hterm j).le)
    have hle' : progressionMidpointErrorTerm Q r 0 ≤
        ∑' j, progressionMidpointErrorTerm Q r j := by simpa using hle
    exact (hterm 0).trans_le hle'
  · have hs : Summable (fun j : ℕ => (1/4 : ℝ)*(1 / ((Q : ℝ)*((j : ℝ)+1))^4)) := by
      apply ((positivePSeries_summable 4 (by omega)).mul_left
        ((1/4)*(1/(Q : ℝ)^4))).congr
      intro j
      change ((1/4 : ℝ)*(1/(Q : ℝ)^4)) * (1 / ((j : ℝ)+1)^4) =
        (1/4 : ℝ)*(1 / ((Q : ℝ)*((j : ℝ)+1))^4)
      rw [mul_assoc]
      congr 1
      rw [mul_pow]
      exact one_div_mul_one_div _ _
    calc
      _ ≤ ∑' j : ℕ, (1/4 : ℝ)*(1 / ((Q : ℝ)*((j : ℝ)+1))^4) := by
        apply Summable.tsum_le_tsum _ (progressionMidpointErrorTerm_summable Q r hQ) hs
        intro j
        rw [progressionMidpointErrorTerm_formula]
        exact midpoint_kernel_difference_le _ _ (by positivity) (by positivity)
      _ = (1/4 : ℝ)*(positivePSeries 4 / (Q : ℝ)^4) := by
        simp only [mul_pow, one_div, mul_inv_rev, tsum_mul_left, tsum_mul_right, positivePSeries]
        ring
      _ = _ := by rw [positivePSeries_four]; ring

/-- Uniform midpoint approximation with exact first Pareto atom and a
completely explicit signed error. No derivative or RH hypothesis occurs. -/
theorem progressionWeight_uniform_midpoint (Q r : ℕ) (hQ : 0 < Q) :
    progressionWeight Q r = positiveWeight r +
      reciprocalSquareSeries (1 + ((r : ℝ)+1/2)/Q) / (Q : ℝ)^2 +
      progressionMidpointRemainder Q r ∧
    0 < progressionMidpointRemainder Q r ∧
    progressionMidpointRemainder Q r ≤ Real.pi^4 / (360*(Q : ℝ)^4) := by
  refine ⟨?_, progressionMidpointRemainder_bounds Q r hQ⟩
  unfold progressionMidpointRemainder
  ring

end
end RiemannResearch.RH.Pareto
