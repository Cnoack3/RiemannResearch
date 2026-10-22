import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Boolean prime likelihood ratios

This module expresses the finite product law explicitly, rather than assuming
probabilistic independence.  For natural primes, instantiate the real parameter
`p i` with the corresponding prime cast.  The algebra only needs `p i ≥ 1`.

Source: user-provided argument, Section 6 of
`Independent_Primes_Squarefree_Approximation_2026-10-07.pdf`. This reference
supports the finite likelihood identities; see
`IndependentPrimeResearchContinuation20261007.md` for their interpretation.

No infinite-product, measure-theoretic, or RH conclusion is asserted here.
-/

namespace RiemannResearch.RH.FinitePrimeLikelihood

open scoped BigOperators

noncomputable section

/-- Explicit mass of a Bernoulli configuration. -/
def bernoulliMass (q : ℝ) (b : Bool) : ℝ :=
  if b then q else 1 - q

/-- An explicit two-point expectation, with `true` representing success. -/
def bernoulliExpectation (q : ℝ) (f : Bool → ℝ) : ℝ :=
  q * f true + (1 - q) * f false

def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- The success probability under the zeta(2) product law. -/
def primeParameter (p : ℝ) : ℝ := 1 / p ^ 2

/-- Changes Bernoulli success probability from `p⁻²` to `p⁻¹`. -/
def primeLikelihood (p : ℝ) (b : Bool) : ℝ :=
  if b then p else p / (p + 1)

theorem bernoulliExpectation_eq_sum (q : ℝ) (f : Bool → ℝ) :
    bernoulliExpectation q f = ∑ b : Bool, bernoulliMass q b * f b := by
  simp [bernoulliExpectation, bernoulliMass]

@[simp] theorem bernoulliExpectation_one (q : ℝ) :
    bernoulliExpectation q (fun _ => 1) = 1 := by
  unfold bernoulliExpectation
  ring

theorem bernoulliMass_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (b : Bool) : 0 ≤ bernoulliMass q b := by
  cases b <;> simp [bernoulliMass] <;> linarith

theorem primeParameter_mem_unitInterval {p : ℝ} (hp : 1 ≤ p) :
    0 ≤ primeParameter p ∧ primeParameter p ≤ 1 := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp2 : 0 < p ^ 2 := by positivity
  have hp2one : 1 ≤ p ^ 2 := by nlinarith
  constructor
  · unfold primeParameter
    positivity
  · unfold primeParameter
    exact (div_le_one hp2).2 hp2one

theorem primeLikelihood_factor {p : ℝ} (hp1 : p + 1 ≠ 0) (b : Bool) :
    primeLikelihood p b = p / (p + 1) * (1 + p * boolIndicator b) := by
  cases b <;> simp [primeLikelihood, boolIndicator]
  (field_simp [hp1]; ring)

theorem expect_primeLikelihood {p : ℝ} (hp0 : p ≠ 0) (hp1 : p + 1 ≠ 0) :
    bernoulliExpectation (primeParameter p) (primeLikelihood p) = 1 := by
  change (1 / p ^ 2) * p + (1 - 1 / p ^ 2) * (p / (p + 1)) = 1
  (field_simp [hp0, hp1]; ring)

theorem expect_primeLikelihood_sq {p : ℝ} (hp0 : p ≠ 0) (hp1 : p + 1 ≠ 0) :
    bernoulliExpectation (primeParameter p) (fun b => primeLikelihood p b ^ 2)
      = 2 * p / (p + 1) := by
  change (1 / p ^ 2) * p ^ 2 +
    (1 - 1 / p ^ 2) * (p / (p + 1)) ^ 2 = 2 * p / (p + 1)
  (field_simp [hp0, hp1]; ring)

theorem expect_primeLikelihood_indicator {p : ℝ} (hp0 : p ≠ 0) :
    bernoulliExpectation (primeParameter p)
      (fun b => primeLikelihood p b * boolIndicator b) = 1 / p := by
  change (1 / p ^ 2) * (p * 1) +
    (1 - 1 / p ^ 2) * ((p / (p + 1)) * 0) = 1 / p
  simp only [mul_one, mul_zero, add_zero]
  field_simp [hp0]

/-- This pointwise equality is the exact change of Bernoulli law. -/
theorem bernoulliMass_mul_primeLikelihood {p : ℝ}
    (hp0 : p ≠ 0) (hp1 : p + 1 ≠ 0) (b : Bool) :
    bernoulliMass (primeParameter p) b * primeLikelihood p b
      = bernoulliMass (1 / p) b := by
  cases b <;> simp [bernoulliMass, primeParameter, primeLikelihood]
  all_goals field_simp [hp0, hp1]
  all_goals ring

section FiniteTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite product mass, making independence explicit. -/
def productMass (q : ι → ℝ) (b : ι → Bool) : ℝ :=
  ∏ i, bernoulliMass (q i) (b i)

def tensorExpectation (q : ι → ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  ∑ b : ι → Bool, productMass q b * f b

def tensorFunction (f : ι → Bool → ℝ) (b : ι → Bool) : ℝ :=
  ∏ i, f i (b i)

/-- Finite product expectation factorization follows from the explicit mass. -/
theorem tensorExpectation_tensorFunction (q : ι → ℝ) (f : ι → Bool → ℝ) :
    tensorExpectation q (tensorFunction f)
      = ∏ i, bernoulliExpectation (q i) (f i) := by
  unfold tensorExpectation productMass tensorFunction
  calc
    (∑ b : ι → Bool,
        (∏ i, bernoulliMass (q i) (b i)) * ∏ i, f i (b i))
        = ∑ b : ι → Bool, ∏ i, bernoulliMass (q i) (b i) * f i (b i) := by
          simp only [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool, bernoulliMass (q i) b * f i b :=
      (Fintype.prod_sum (fun i b => bernoulliMass (q i) b * f i b)).symm
    _ = ∏ i, bernoulliExpectation (q i) (f i) := by
      simp only [← bernoulliExpectation_eq_sum]

theorem tensorExpectation_one (q : ι → ℝ) :
    tensorExpectation q (fun _ => 1) = 1 := by
  have hpoint : (fun _ : ι → Bool => (1 : ℝ)) =
      tensorFunction (fun _ _ => 1) := by
    funext b
    simp [tensorFunction]
  rw [hpoint, tensorExpectation_tensorFunction]
  simp

theorem productMass_sum_one (q : ι → ℝ) :
    (∑ b : ι → Bool, productMass q b) = 1 := by
  simpa [tensorExpectation] using tensorExpectation_one q

omit [DecidableEq ι] in
theorem productMass_nonneg (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (b : ι → Bool) :
    0 ≤ productMass q b := by
  exact Finset.prod_nonneg
    (fun i _ => bernoulliMass_nonneg (hq0 i) (hq1 i) (b i))

def finiteLikelihood (p : ι → ℝ) : (ι → Bool) → ℝ :=
  tensorFunction (fun i => primeLikelihood (p i))

def baseRatio (p : ι → ℝ) : ℝ := ∏ i, p i / (p i + 1)

/-- The divisibility monomial attached to a subset of prime coordinates. -/
def finiteMonomial (A : Finset ι) (b : ι → Bool) : ℝ :=
  ∏ i, if i ∈ A then boolIndicator (b i) else 1

variable (p : ι → ℝ) (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)

include hp0 hp1

theorem expect_finiteLikelihood :
    tensorExpectation (fun i => primeParameter (p i)) (finiteLikelihood p) = 1 := by
  rw [finiteLikelihood, tensorExpectation_tensorFunction]
  simp_rw [expect_primeLikelihood (hp0 _) (hp1 _)]
  simp

theorem expect_finiteLikelihood_sq :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => finiteLikelihood p b ^ 2)
      = 2 ^ Fintype.card ι * baseRatio p := by
  have hpoint : (fun b => finiteLikelihood p b ^ 2) =
      tensorFunction (fun i b => primeLikelihood (p i) b ^ 2) := by
    funext b
    simp only [finiteLikelihood, tensorFunction, pow_two, Finset.prod_mul_distrib]
  rw [hpoint, tensorExpectation_tensorFunction]
  simp_rw [expect_primeLikelihood_sq (hp0 _) (hp1 _)]
  calc
    (∏ i, 2 * p i / (p i + 1)) = ∏ i, 2 * (p i / (p i + 1)) := by
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = 2 ^ Fintype.card ι * baseRatio p := by
      simp [Finset.prod_mul_distrib, baseRatio]

theorem expect_finiteLikelihood_monomial (A : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => finiteLikelihood p b * finiteMonomial A b)
      = 1 / (∏ i ∈ A, p i) := by
  have hpoint : (fun b => finiteLikelihood p b * finiteMonomial A b) =
      tensorFunction (fun i b =>
        primeLikelihood (p i) b * (if i ∈ A then boolIndicator b else 1)) := by
    funext b
    simp only [finiteLikelihood, finiteMonomial, tensorFunction,
      Finset.prod_mul_distrib]
  rw [hpoint, tensorExpectation_tensorFunction]
  have hcoord (i : ι) :
      bernoulliExpectation (primeParameter (p i))
        (fun b => primeLikelihood (p i) b *
          (if i ∈ A then boolIndicator b else 1))
        = if i ∈ A then 1 / p i else 1 := by
    by_cases hi : i ∈ A
    · simpa only [hi, ↓reduceIte] using
        expect_primeLikelihood_indicator (hp0 i)
    · simpa only [hi, ↓reduceIte, mul_one] using
        expect_primeLikelihood (hp0 i) (hp1 i)
  simp_rw [hcoord]
  rw [Fintype.prod_extend_by_one]
  simp

omit [DecidableEq ι] in
theorem productMass_mul_finiteLikelihood (b : ι → Bool) :
    productMass (fun i => primeParameter (p i)) b * finiteLikelihood p b
      = productMass (fun i => 1 / p i) b := by
  unfold productMass finiteLikelihood tensorFunction
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact bernoulliMass_mul_primeLikelihood (hp0 i) (hp1 i) (b i)

/-- Multiplying by the likelihood ratio changes every success parameter to `p⁻¹`. -/
theorem tensorExpectation_tilt (f : (ι → Bool) → ℝ) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => finiteLikelihood p b * f b)
      = tensorExpectation (fun i => 1 / p i) f := by
  unfold tensorExpectation
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, productMass_mul_finiteLikelihood p hp0 hp1 b]

end FiniteTensor

end

end RiemannResearch.RH.FinitePrimeLikelihood
