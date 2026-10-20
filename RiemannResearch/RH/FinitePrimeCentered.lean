/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FinitePrimeDivisibilityMoments
import RiemannResearch.RH.FinitePrimeLikelihood
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered finite Bernoulli products

Source: user-provided argument and user-directed derivation of the prime
divisibility coordinates for the zeta(2) research program.

Exact identities for the explicit finite Boolean product law.  No assertion
identifying this law with the integer Zipf law is made here.  In particular,
orthogonality of these differentiated coordinates supplies no bound for their
discrete antiderivatives in the complete-Q norm.

The formulas are algebraic for every parameter different from one.  They
describe a probability inner product when the parameters lie in `[0, 1]`.
The coordinates are normalized to equal one on success, not to have unit norm;
the exact non-unit diagonal is retained in `normalizedMonomial_gram`.
Dividing by the square root of this diagonal gives `unitMonomial`, whose Gram
matrix is the identity for parameters strictly between zero and one.  No
completeness or identification with the full integer Hilbert space is asserted.
-/

namespace RiemannResearch.RH.FinitePrimeCentered

open scoped BigOperators
open RiemannResearch.RH.FinitePrimeLikelihood

noncomputable section

/-- A centered Bernoulli coordinate normalized to equal one on success. -/
def normalizedCoordinate (q : ℝ) (b : Bool) : ℝ :=
  (boolIndicator b - q) / (1 - q)

theorem expect_normalizedCoordinate (q : ℝ) (hq : 1 - q ≠ 0) :
    bernoulliExpectation q (normalizedCoordinate q) = 0 := by
  change q * ((1 - q) / (1 - q)) + (1 - q) * ((0 - q) / (1 - q)) = 0
  (field_simp [hq]; ring)

theorem expect_normalizedCoordinate_sq (q : ℝ) (hq : 1 - q ≠ 0) :
    bernoulliExpectation q (fun b => normalizedCoordinate q b ^ 2)
      = q / (1 - q) := by
  change q * ((1 - q) / (1 - q)) ^ 2 +
    (1 - q) * ((0 - q) / (1 - q)) ^ 2 = q / (1 - q)
  (field_simp [hq]; ring)

theorem expect_indicator_mul_normalizedCoordinate (q : ℝ) (hq : 1 - q ≠ 0) :
    bernoulliExpectation q
      (fun b => boolIndicator b * normalizedCoordinate q b) = q := by
  change q * (1 * ((1 - q) / (1 - q))) +
    (1 - q) * (0 * ((0 - q) / (1 - q))) = q
  (field_simp [hq]; ring)

theorem expect_failure_mul_normalizedCoordinate (q : ℝ) (hq : 1 - q ≠ 0) :
    bernoulliExpectation q
      (fun b => (1 - boolIndicator b) * normalizedCoordinate q b) = -q := by
  change q * ((1 - 1) * ((1 - q) / (1 - q))) +
    (1 - q) * ((1 - 0) * ((0 - q) / (1 - q))) = -q
  (field_simp [hq]; ring)

theorem expect_failure (q : ℝ) :
    bernoulliExpectation q (fun b => 1 - boolIndicator b) = 1 - q := by
  simp [bernoulliExpectation, boolIndicator]

section FiniteTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product of the centered coordinates selected by a finite subset. -/
def normalizedMonomial (q : ι → ℝ) (A : Finset ι) : (ι → Bool) → ℝ :=
  tensorFunction (fun i b => if i ∈ A then normalizedCoordinate (q i) b else 1)

/-- The full finite centered Gram matrix is diagonal. -/
theorem normalizedMonomial_gram (q : ι → ℝ) (hq : ∀ i, 1 - q i ≠ 0)
    (A B : Finset ι) :
    tensorExpectation q (fun b => normalizedMonomial q A b * normalizedMonomial q B b)
      = if A = B then (∏ i ∈ A, q i / (1 - q i)) else 0 := by
  have hpoint :
      (fun b => normalizedMonomial q A b * normalizedMonomial q B b) =
      tensorFunction (fun i b =>
        (if i ∈ A then normalizedCoordinate (q i) b else 1) *
        (if i ∈ B then normalizedCoordinate (q i) b else 1)) := by
    funext b
    simp only [normalizedMonomial, tensorFunction, Finset.prod_mul_distrib]
  rw [hpoint, tensorExpectation_tensorFunction]
  have hcoord (i : ι) :
      bernoulliExpectation (q i) (fun b =>
        (if i ∈ A then normalizedCoordinate (q i) b else 1) *
        (if i ∈ B then normalizedCoordinate (q i) b else 1)) =
      if i ∈ A then (if i ∈ B then q i / (1 - q i) else 0)
      else (if i ∈ B then 0 else 1) := by
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B
    · simpa only [hA, hB, ↓reduceIte, pow_two] using
        expect_normalizedCoordinate_sq (q i) (hq i)
    · simpa only [hA, hB, ↓reduceIte, mul_one] using
        expect_normalizedCoordinate (q i) (hq i)
    · simpa only [hA, hB, ↓reduceIte, one_mul] using
        expect_normalizedCoordinate (q i) (hq i)
    · simpa only [hA, hB, ↓reduceIte, one_mul] using
        bernoulliExpectation_one (q i)
  simp_rw [hcoord]
  by_cases hAB : A = B
  · subst B
    rw [if_pos rfl]
    calc
      (∏ i, if i ∈ A then (if i ∈ A then q i / (1 - q i) else 0)
        else (if i ∈ A then 0 else 1)) =
          ∏ i, if i ∈ A then q i / (1 - q i) else 1 := by
            apply Finset.prod_congr rfl
            intro i _
            by_cases hi : i ∈ A <;> simp [hi]
      _ = ∏ i ∈ A, q i / (1 - q i) :=
        Fintype.prod_extend_by_one A (fun i => q i / (1 - q i))
  · rw [if_neg hAB]
    have hdiff : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
      by_contra h
      apply hAB
      apply Finset.ext
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp_all

theorem normalizedMonomial_orthogonal (q : ι → ℝ) (hq : ∀ i, 1 - q i ≠ 0)
    {A B : Finset ι} (hAB : A ≠ B) :
    tensorExpectation q (fun b => normalizedMonomial q A b * normalizedMonomial q B b)
      = 0 := by
  rw [normalizedMonomial_gram q hq, if_neg hAB]

theorem normalizedMonomial_sq (q : ι → ℝ) (hq : ∀ i, 1 - q i ≠ 0)
    (A : Finset ι) :
    tensorExpectation q (fun b => normalizedMonomial q A b ^ 2)
      = ∏ i ∈ A, q i / (1 - q i) := by
  simpa [pow_two] using normalizedMonomial_gram q hq A A

/-- Exact squared norm of the centered product indexed by `A`. -/
def monomialVariance (q : ι → ℝ) (A : Finset ι) : ℝ :=
  ∏ i ∈ A, q i / (1 - q i)

omit [Fintype ι] [DecidableEq ι] in
theorem monomialVariance_pos (q : ι → ℝ) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (A : Finset ι) : 0 < monomialVariance q A := by
  unfold monomialVariance
  exact Finset.prod_pos (fun i _ => div_pos (hq0 i) (sub_pos.mpr (hq1 i)))

/-- The centered finite product divided by its positive standard deviation. -/
def unitMonomial (q : ι → ℝ) (A : Finset ι) (b : ι → Bool) : ℝ :=
  (1 / Real.sqrt (monomialVariance q A)) * normalizedMonomial q A b

/-- Identity Gram matrix in the explicit finite probability law. -/
theorem unitMonomial_gram (q : ι → ℝ) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (A B : Finset ι) :
    tensorExpectation q (fun b => unitMonomial q A b * unitMonomial q B b)
      = if A = B then 1 else 0 := by
  have hq : ∀ i, 1 - q i ≠ 0 :=
    fun i => ne_of_gt (sub_pos.mpr (hq1 i))
  have hpoint : (fun b => unitMonomial q A b * unitMonomial q B b) =
      fun b => ((1 / Real.sqrt (monomialVariance q A)) *
        (1 / Real.sqrt (monomialVariance q B))) *
        (normalizedMonomial q A b * normalizedMonomial q B b) := by
    funext b
    unfold unitMonomial
    ring
  rw [hpoint, tensorExpectation_smul, normalizedMonomial_gram q hq]
  change ((1 / Real.sqrt (monomialVariance q A)) *
      (1 / Real.sqrt (monomialVariance q B))) *
      (if A = B then monomialVariance q A else 0) = if A = B then 1 else 0
  by_cases hAB : A = B
  · subst B
    simp only [↓reduceIte]
    have hv := monomialVariance_pos q hq0 hq1 A
    have hs : Real.sqrt (monomialVariance q A) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hv)
    (field_simp [hs]; nlinarith [Real.sq_sqrt hv.le])
  · simp only [if_neg hAB, mul_zero]

theorem unitMonomial_sq (q : ι → ℝ) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1) (A : Finset ι) :
    tensorExpectation q (fun b => unitMonomial q A b ^ 2) = 1 := by
  simpa [pow_two] using unitMonomial_gram q hq0 hq1 A A

/-- Only one selected coordinate succeeds; all the others fail. -/
def isolatedSuccess (i₀ : ι) : (ι → Bool) → ℝ :=
  tensorFunction (fun i b => if i = i₀ then boolIndicator b else 1 - boolIndicator b)

/-- Exact coefficients against the orthogonal centered products. -/
theorem isolatedSuccess_centered_coefficient (q : ι → ℝ)
    (hq : ∀ i, 1 - q i ≠ 0) (i₀ : ι) (A : Finset ι) :
    tensorExpectation q (fun b => isolatedSuccess i₀ b * normalizedMonomial q A b)
      = ∏ i, if i = i₀ then q i else (if i ∈ A then -(q i) else 1 - q i) := by
  have hpoint :
      (fun b => isolatedSuccess i₀ b * normalizedMonomial q A b) =
      tensorFunction (fun i b =>
        (if i = i₀ then boolIndicator b else 1 - boolIndicator b) *
        (if i ∈ A then normalizedCoordinate (q i) b else 1)) := by
    funext b
    simp only [isolatedSuccess, normalizedMonomial, tensorFunction,
      Finset.prod_mul_distrib]
  rw [hpoint, tensorExpectation_tensorFunction]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = i₀ <;> by_cases hA : i ∈ A
  · simpa only [if_pos hi, if_pos hA] using
      expect_indicator_mul_normalizedCoordinate (q i) (hq i)
  · simpa only [if_pos hi, if_neg hA, mul_one] using expect_boolIndicator (q i)
  · simpa only [if_neg hi, if_pos hA] using
      expect_failure_mul_normalizedCoordinate (q i) (hq i)
  · simpa only [if_neg hi, if_neg hA, mul_one] using expect_failure (q i)

end FiniteTensor

/-- The centered-coordinate variance at the prime divisibility parameter. -/
theorem primeParameter_centered_variance (p : ℝ) (hp0 : p ≠ 0)
    (hp2 : p ^ 2 - 1 ≠ 0) :
    primeParameter p / (1 - primeParameter p) = 1 / (p ^ 2 - 1) := by
  unfold primeParameter
  have hq : 1 - 1 / p ^ 2 ≠ 0 := by
    intro h
    apply hp2
    have hpw : p ^ 2 ≠ 0 := pow_ne_zero _ hp0
    have hh : p ^ 2 = 1 := by
      have heq := (eq_div_iff hpw).mp (sub_eq_zero.mp h)
      simpa using heq
    exact sub_eq_zero.mpr hh
  field_simp [hp0, hp2, hq]

end

end RiemannResearch.RH.FinitePrimeCentered
