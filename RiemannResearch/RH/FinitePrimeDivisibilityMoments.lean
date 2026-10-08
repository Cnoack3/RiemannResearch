import RiemannResearch.RH.FinitePrimeLikelihood

/-!
# Finite Boolean divisibility moments and differentiated Gram entries

Source: user-directed research continuation; see
`IndependentPrimeResearchContinuation20261007.md` for the statements
and their mathematical interpretation.


These are exact finite identities for the explicitly defined Boolean product
mass in `FinitePrimeLikelihood`.  Identifying this finite law with the pushforward
of the zeta(2) integer law is a separate arithmetic/probability bridge; it is not
assumed or proved in this module.

For distinct prime parameters, `subsetProduct p A` represents the squarefree
conductor indexed by `A`, and `A ∪ B` represents the least common multiple.

-/

namespace RiemannResearch.RH.FinitePrimeLikelihood

open scoped BigOperators

noncomputable section

@[simp] theorem expect_boolIndicator (q : ℝ) :
    bernoulliExpectation q boolIndicator = q := by
  simp [bernoulliExpectation, boolIndicator]

section FiniteTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def subsetProduct (p : ι → ℝ) (A : Finset ι) : ℝ := ∏ i ∈ A, p i

theorem tensorExpectation_add (q : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    tensorExpectation q (fun b => f b + g b)
      = tensorExpectation q f + tensorExpectation q g := by
  unfold tensorExpectation
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

theorem tensorExpectation_sub (q : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    tensorExpectation q (fun b => f b - g b)
      = tensorExpectation q f - tensorExpectation q g := by
  unfold tensorExpectation
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem tensorExpectation_smul (q : ι → ℝ) (c : ℝ) (f : (ι → Bool) → ℝ) :
    tensorExpectation q (fun b => c * f b) = c * tensorExpectation q f := by
  unfold tensorExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorExpectation_const (q : ι → ℝ) (c : ℝ) :
    tensorExpectation q (fun _ => c) = c := by
  unfold tensorExpectation
  rw [← Finset.sum_mul, productMass_sum_one, one_mul]

/-- A divisibility monomial has expectation equal to the product of parameters. -/
theorem expect_finiteMonomial (q : ι → ℝ) (A : Finset ι) :
    tensorExpectation q (finiteMonomial A) = ∏ i ∈ A, q i := by
  have hpoint : finiteMonomial A =
      tensorFunction (fun i b => if i ∈ A then boolIndicator b else 1) := rfl
  rw [hpoint, tensorExpectation_tensorFunction]
  have hcoord (i : ι) :
      bernoulliExpectation (q i)
        (fun b => if i ∈ A then boolIndicator b else 1)
        = if i ∈ A then q i else 1 := by
    by_cases hi : i ∈ A
    · simp only [hi, ↓reduceIte, expect_boolIndicator]
    · simp only [hi, ↓reduceIte, bernoulliExpectation_one]
  simp_rw [hcoord]
  exact Fintype.prod_extend_by_one A q

/-- Idempotence of Boolean indicators turns multiplication into set union. -/
theorem finiteMonomial_mul (A B : Finset ι) (b : ι → Bool) :
    finiteMonomial A b * finiteMonomial B b = finiteMonomial (A ∪ B) b := by
  unfold finiteMonomial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    cases b i <;> simp [hA, hB, boolIndicator]

theorem expect_prime_finiteMonomial (p : ι → ℝ) (A : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i)) (finiteMonomial A)
      = 1 / subsetProduct p A ^ 2 := by
  rw [expect_finiteMonomial]
  unfold primeParameter subsetProduct
  rw [Finset.prod_div_distrib, Finset.prod_pow]
  simp

theorem expect_prime_finiteMonomial_mul (p : ι → ℝ) (A B : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => finiteMonomial A b * finiteMonomial B b)
      = 1 / subsetProduct p (A ∪ B) ^ 2 := by
  have hpoint : (fun b => finiteMonomial A b * finiteMonomial B b)
      = finiteMonomial (A ∪ B) := by
    funext b
    exact finiteMonomial_mul A B b
  rw [hpoint, expect_prime_finiteMonomial]

/-- The finite Boolean representative of a differentiated residue atom. -/
def finiteDerivativeAtom (p : ι → ℝ) (A : Finset ι) (b : ι → Bool) : ℝ :=
  1 / subsetProduct p A - finiteMonomial A b

theorem expect_finiteDerivativeAtom (p : ι → ℝ) (A : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i)) (finiteDerivativeAtom p A)
      = 1 / subsetProduct p A - 1 / subsetProduct p A ^ 2 := by
  unfold finiteDerivativeAtom
  rw [tensorExpectation_sub, tensorExpectation_const, expect_prime_finiteMonomial]

/-- Exact differentiated Gram entry, expressed using the union conductor. -/
theorem finiteDerivativeGram (p : ι → ℝ) (A B : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => finiteDerivativeAtom p A b * finiteDerivativeAtom p B b)
      = 1 / (subsetProduct p A * subsetProduct p B)
        - 1 / (subsetProduct p A * subsetProduct p B ^ 2)
        - 1 / (subsetProduct p A ^ 2 * subsetProduct p B)
        + 1 / subsetProduct p (A ∪ B) ^ 2 := by
  have hpoint :
      (fun b => finiteDerivativeAtom p A b * finiteDerivativeAtom p B b) =
      (fun b =>
        (1 / subsetProduct p A) * (1 / subsetProduct p B)
        - (1 / subsetProduct p A) * finiteMonomial B b
        - (1 / subsetProduct p B) * finiteMonomial A b
        + finiteMonomial A b * finiteMonomial B b) := by
    funext b
    unfold finiteDerivativeAtom
    ring
  rw [hpoint, tensorExpectation_add, tensorExpectation_sub,
    tensorExpectation_sub, tensorExpectation_const,
    tensorExpectation_smul, tensorExpectation_smul,
    expect_prime_finiteMonomial, expect_prime_finiteMonomial,
    expect_prime_finiteMonomial_mul]
  simp only [one_div, mul_inv_rev]
  ring

/-- The diagonal simplifies to the exact squared derivative norm formula. -/
theorem expect_finiteDerivativeAtom_sq (p : ι → ℝ) (A : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => finiteDerivativeAtom p A b ^ 2)
      = 2 * (subsetProduct p A - 1) / subsetProduct p A ^ 3 := by
  simp only [pow_two]
  rw [finiteDerivativeGram]
  simp only [Finset.union_self]
  by_cases hd : subsetProduct p A = 0
  · simp [hd]
  · field_simp [hd]
    ring

/-- The likelihood vector is orthogonal to every differentiated squarefree atom. -/
theorem likelihood_orthogonal_finiteDerivativeAtom
    (p : ι → ℝ) (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (A : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => finiteLikelihood p b * finiteDerivativeAtom p A b) = 0 := by
  have hpoint :
      (fun b => finiteLikelihood p b * finiteDerivativeAtom p A b) =
      (fun b => (1 / subsetProduct p A) * finiteLikelihood p b -
        finiteLikelihood p b * finiteMonomial A b) := by
    funext b
    unfold finiteDerivativeAtom
    ring
  rw [hpoint, tensorExpectation_sub, tensorExpectation_smul,
    expect_finiteLikelihood p hp0 hp1,
    expect_finiteLikelihood_monomial p hp0 hp1 A]
  simp [subsetProduct]

end FiniteTensor

end

end RiemannResearch.RH.FinitePrimeLikelihood
