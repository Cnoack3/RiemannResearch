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

/- Source: user-provided dyadic-block/CRT argument, 20 September 2026,
Section 5. Relative control is uniform in the residue and all coefficients. -/

/-- First Pareto atom retained exactly, followed by the midpoint trigamma series. -/
def progressionMidpointWeight (Q r : ℕ) : ℝ :=
  positiveWeight r +
    reciprocalSquareSeries (1 + ((r : ℝ)+1/2)/Q) / (Q : ℝ)^2

private theorem progressionMidpointErrorTerm_relative_bound
    (Q r j : ℕ) (hQ : 0 < Q) (hr : 0 < r) :
    progressionMidpointErrorTerm Q r j ≤
      (1 / (2*(Q : ℝ)+3)^2) * positiveWeight (r+Q+Q*j) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.succ_le_of_lt hr)
  let t : ℝ := (Q : ℝ)*((j : ℝ)+1)+r
  have ht : 0 < t := by dsimp [t]; positivity
  have htQ : (Q : ℝ)+1 ≤ t := by
    dsimp [t]
    nlinarith [mul_nonneg hq.le (Nat.cast_nonneg (α := ℝ) j)]
  have hw : positiveWeight (r+Q+Q*j) = 1 / (t*(t+1)) := by
    dsimp [t]
    unfold positiveWeight
    push_cast
    congr 1 <;> ring
  have he : progressionMidpointErrorTerm Q r j =
      (1 / (2*t+1)^2) * (1 / (t*(t+1))) := by
    rw [progressionMidpointErrorTerm_formula,
      midpoint_kernel_difference _ _ (by positivity) (by positivity)]
    rw [one_div_mul_one_div]
    congr 1
    dsimp [t]
    ring
  have hdiff : 0 ≤ (2*t+1) - (2*(Q : ℝ)+3) := by linarith
  have hsum : 0 ≤ (2*t+1) + (2*(Q : ℝ)+3) := by positivity
  have hsq : (2*(Q : ℝ)+3)^2 ≤ (2*t+1)^2 := by
    nlinarith [mul_nonneg hdiff hsum]
  have hrec : 1 / (2*t+1)^2 ≤ 1 / (2*(Q : ℝ)+3)^2 :=
    one_div_le_one_div_of_le (by positivity) hsq
  rw [he, ← hw]
  exact mul_le_mul_of_nonneg_right hrec (positiveWeight_nonneg _)

/-- The midpoint remainder is bounded relative to the complete tail mass,
uniformly over every positive residue and every coefficient choice. -/
theorem progressionMidpointRemainder_relative_bound
    (Q r : ℕ) (hQ : 0 < Q) (hr : 0 < r) :
    progressionMidpointRemainder Q r ≤
      (1 / (2*(Q : ℝ)+3)^2) *
        (progressionWeight Q r - positiveWeight r) := by
  rw [progressionMidpointRemainder_tsum Q r hQ]
  calc
    (∑' j, progressionMidpointErrorTerm Q r j) ≤
        ∑' j, (1 / (2*(Q : ℝ)+3)^2) * positiveWeight (r+Q+Q*j) := by
      apply Summable.tsum_le_tsum
        (fun j => progressionMidpointErrorTerm_relative_bound Q r j hQ hr)
        (progressionMidpointErrorTerm_summable Q r hQ)
        ((progressionWeight_summable Q (r+Q) hQ).mul_left _)
    _ = (1 / (2*(Q : ℝ)+3)^2) * progressionWeight Q (r+Q) := by
      rw [tsum_mul_left]
      rfl
    _ = _ := by
      rw [progressionWeight_split Q r hQ]
      ring

/-- Multiplicative comparison of the exact and midpoint progression weights.
The factor does not depend on the residue. -/
theorem progressionMidpointWeight_relative_bounds
    (Q r : ℕ) (hQ : 0 < Q) (hr : 0 < r) :
    (1 - 1 / (2*(Q : ℝ)+3)^2) * progressionWeight Q r ≤
        progressionMidpointWeight Q r ∧
      progressionMidpointWeight Q r ≤ progressionWeight Q r := by
  have he : progressionMidpointWeight Q r + progressionMidpointRemainder Q r =
      progressionWeight Q r := by
    unfold progressionMidpointWeight progressionMidpointRemainder
    ring
  have hrem : 0 ≤ progressionMidpointRemainder Q r :=
    (progressionMidpointRemainder_bounds Q r hQ).1.le
  have hrel := progressionMidpointRemainder_relative_bound Q r hQ hr
  have hrel' : progressionMidpointRemainder Q r ≤
      (1 / (2*(Q : ℝ)+3)^2) * progressionWeight Q r := by
    exact hrel.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (positiveWeight_nonneg r)) (by positivity))
  constructor
  · nlinarith
  · linarith

/-- The relative factor stays strictly positive even at the smallest modulus. -/
theorem progressionMidpoint_relative_factor_pos (Q : ℕ) :
    0 < 1 - 1 / (2*(Q : ℝ)+3)^2 := by
  have hsq : 1 < (2*(Q : ℝ)+3)^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) Q]
  have hlt : 1 / (2*(Q : ℝ)+3)^2 < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    simpa using hsq
  linarith

/-- Full finite quadratic-form comparison. Values may contain arbitrary signed
linear combinations; squaring occurs before multiplying by the weights. -/
theorem progressionMidpoint_quadratic_comparison
    (Q : ℕ) (hQ : 0 < Q) (I : Finset ℕ)
    (hI : ∀ r ∈ I, 0 < r) (v : ℕ → ℝ) :
    (1 - 1 / (2*(Q : ℝ)+3)^2) *
        (∑ r ∈ I, progressionWeight Q r * (v r)^2) ≤
      (∑ r ∈ I, progressionMidpointWeight Q r * (v r)^2) ∧
    (∑ r ∈ I, progressionMidpointWeight Q r * (v r)^2) ≤
      (∑ r ∈ I, progressionWeight Q r * (v r)^2) := by
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have h := mul_le_mul_of_nonneg_right
      (progressionMidpointWeight_relative_bounds Q r hQ (hI r hr)).1
      (sq_nonneg (v r))
    simpa only [mul_assoc] using h
  · apply Finset.sum_le_sum
    intro r hr
    exact mul_le_mul_of_nonneg_right
      (progressionMidpointWeight_relative_bounds Q r hQ (hI r hr)).2
      (sq_nonneg (v r))

/-- The comparison survives optimization. The hypotheses only specify actual
minimizers; finite-dimensional projection theorems provide those independently.
The exact and midpoint problems may have different minimizing coefficients. -/
theorem progressionMidpoint_minimum_comparison
    {κ : Type*} (Q : ℕ) (hQ : 0 < Q) (I : Finset ℕ)
    (hI : ∀ r ∈ I, 0 < r) (v : κ → ℕ → ℝ) (cExact cMid : κ)
    (hExact : ∀ c, (∑ r ∈ I, progressionWeight Q r * (v cExact r)^2) ≤
      (∑ r ∈ I, progressionWeight Q r * (v c r)^2))
    (hMid : ∀ c, (∑ r ∈ I, progressionMidpointWeight Q r * (v cMid r)^2) ≤
      (∑ r ∈ I, progressionMidpointWeight Q r * (v c r)^2)) :
    (1 - 1 / (2*(Q : ℝ)+3)^2) *
        (∑ r ∈ I, progressionWeight Q r * (v cExact r)^2) ≤
      (∑ r ∈ I, progressionMidpointWeight Q r * (v cMid r)^2) ∧
    (∑ r ∈ I, progressionMidpointWeight Q r * (v cMid r)^2) ≤
      (∑ r ∈ I, progressionWeight Q r * (v cExact r)^2) := by
  constructor
  · exact (mul_le_mul_of_nonneg_left (hExact cMid)
      (progressionMidpoint_relative_factor_pos Q).le).trans
      (progressionMidpoint_quadratic_comparison Q hQ I hI (v cMid)).1
  · exact (hMid cExact).trans
      (progressionMidpoint_quadratic_comparison Q hQ I hI (v cExact)).2

/-- Positive integer moduli give the uniform global factor 24/25. -/
theorem progressionMidpoint_relative_factor_lower (Q : ℕ) (hQ : 0 < Q) :
    (24/25 : ℝ) ≤ 1 - 1 / (2*(Q : ℝ)+3)^2 := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.succ_le_of_lt hQ
  have hsq : (25 : ℝ) ≤ (2*(Q : ℝ)+3)^2 := by
    nlinarith [sq_nonneg ((Q : ℝ)-1)]
  have hrec : 1 / (2*(Q : ℝ)+3)^2 ≤ 1 / (25 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hsq
  linarith

/-- Exact and midpoint full quadratic energies vanish along exactly the same
parameter limits. No restriction on growth of the periods, charts, or signed
coefficient families is required, beyond positivity of each modulus/residue. -/
theorem progressionMidpoint_quadratic_tendsto_zero_iff
    {α : Type*} (l : Filter α) (Q : α → ℕ) (hQ : ∀ a, 0 < Q a)
    (I : α → Finset ℕ) (hI : ∀ a, ∀ r ∈ I a, 0 < r) (v : α → ℕ → ℝ) :
    Filter.Tendsto (fun a => ∑ r ∈ I a, progressionWeight (Q a) r * (v a r)^2)
        l (nhds 0) ↔
      Filter.Tendsto
        (fun a => ∑ r ∈ I a, progressionMidpointWeight (Q a) r * (v a r)^2)
        l (nhds 0) := by
  let E : α → ℝ := fun a => ∑ r ∈ I a, progressionWeight (Q a) r * (v a r)^2
  let M : α → ℝ := fun a =>
    ∑ r ∈ I a, progressionMidpointWeight (Q a) r * (v a r)^2
  change Filter.Tendsto E l (nhds 0) ↔ Filter.Tendsto M l (nhds 0)
  have hEn (a) : 0 ≤ E a := by
    dsimp [E]
    exact Finset.sum_nonneg (fun r _ =>
      mul_nonneg (progressionWeight_nonneg _ _) (sq_nonneg _))
  have hcompare (a) : (24/25 : ℝ)*E a ≤ M a ∧ M a ≤ E a := by
    have h := progressionMidpoint_quadratic_comparison (Q a) (hQ a) (I a) (hI a) (v a)
    change (1 - 1 / (2*(Q a : ℝ)+3)^2)*E a ≤ M a ∧ M a ≤ E a at h
    exact ⟨(mul_le_mul_of_nonneg_right
      (progressionMidpoint_relative_factor_lower (Q a) (hQ a)) (hEn a)).trans h.1, h.2⟩
  have hMn (a) : 0 ≤ M a :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24/25) (hEn a)).trans (hcompare a).1
  constructor
  · intro hE
    exact squeeze_zero hMn (fun a => (hcompare a).2) hE
  · intro hM
    have hScaled : Filter.Tendsto (fun a => (25/24 : ℝ)*M a) l (nhds 0) := by
      simpa only [mul_zero] using hM.const_mul (25/24 : ℝ)
    apply squeeze_zero hEn _ hScaled
    intro a
    have h := (hcompare a).1
    linarith

end
end RiemannResearch.RH.Pareto
