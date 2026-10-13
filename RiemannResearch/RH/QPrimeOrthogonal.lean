import RiemannResearch.RH.FinitePrimeLikelihood
import RiemannResearch.RH.ZetaTwoPrimeConsumers
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Orthogonal squarefree divisibility coordinates for the zeta(2) measure

Source: user-provided inverse-Gram research argument. The construction is the
finite product of centered Bernoulli coordinates. The final theorems transport
the finite algebra to the actual probability measure `ZetaTwoProbability.Q`.
These identities diagonalize finite divisibility coordinates, not residue
coordinates; an arithmetic approximation estimate is still needed for RH.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.FinitePrimeLikelihood

/-- The centered divisibility coordinate with variance `p² - 1`. -/
def centeredPrime (p : ℝ) (b : Bool) : ℝ :=
  p ^ 2 * boolIndicator b - 1

theorem expect_centeredPrime {p : ℝ} (hp : p ≠ 0) :
    bernoulliExpectation (primeParameter p) (centeredPrime p) = 0 := by
  change (1 / p ^ 2) * (p ^ 2 * 1 - 1) +
    (1 - 1 / p ^ 2) * (p ^ 2 * 0 - 1) = 0
  field_simp [hp]
  <;> ring

theorem expect_centeredPrime_sq {p : ℝ} (hp : p ≠ 0) :
    bernoulliExpectation (primeParameter p) (fun b => centeredPrime p b ^ 2)
      = p ^ 2 - 1 := by
  change (1 / p ^ 2) * (p ^ 2 * 1 - 1) ^ 2 +
    (1 - 1 / p ^ 2) * (p ^ 2 * 0 - 1) ^ 2 = p ^ 2 - 1
  field_simp [hp]
  <;> ring

section FiniteTensor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squarefree wavelet indexed by the subset `A` of prime coordinates. -/
def primeWavelet (p : ι → ℝ) (A : Finset ι) (b : ι → Bool) : ℝ :=
  ∏ i, if i ∈ A then centeredPrime (p i) (b i) else 1

/-- The squarefree Jordan factor. For actual primes this is `J₂(∏ i ∈ A, p i)`. -/
def primeWaveletWeight (p : ι → ℝ) (A : Finset ι) : ℝ :=
  ∏ i ∈ A, (p i ^ 2 - 1)

@[simp] theorem primeWavelet_empty (p : ι → ℝ) (b : ι → Bool) :
    primeWavelet p ∅ b = 1 := by
  simp [primeWavelet]

theorem primeWavelet_eq_prod (p : ι → ℝ) (A : Finset ι) (b : ι → Bool) :
    primeWavelet p A b = ∏ i ∈ A, centeredPrime (p i) (b i) := by
  unfold primeWavelet
  rw [Fintype.prod_extend_by_one]

/-- Exact diagonal second moment, retaining every prime factor. -/
theorem expect_primeWavelet_sq (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (A : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => primeWavelet p A b ^ 2) = primeWaveletWeight p A := by
  have hpoint : (fun b => primeWavelet p A b ^ 2) =
      tensorFunction (fun i b => (if i ∈ A then centeredPrime (p i) b else 1) ^ 2) := by
    funext b
    simp only [primeWavelet, tensorFunction, pow_two, Finset.prod_mul_distrib]
  rw [hpoint, tensorExpectation_tensorFunction]
  have hcoord (i : ι) :
      bernoulliExpectation (primeParameter (p i))
        (fun b => (if i ∈ A then centeredPrime (p i) b else 1) ^ 2) =
      if i ∈ A then p i ^ 2 - 1 else 1 := by
    by_cases hi : i ∈ A
    · simpa only [hi, ↓reduceIte] using expect_centeredPrime_sq (hp i)
    · simp only [hi, ↓reduceIte, one_pow, bernoulliExpectation_one]
  simp_rw [hcoord]
  unfold primeWaveletWeight
  rw [Fintype.prod_extend_by_one]

/-- Distinct squarefree coordinates are orthogonal. -/
theorem expect_primeWavelet_mul_of_ne (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (A B : Finset ι) (hAB : A ≠ B) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => primeWavelet p A b * primeWavelet p B b) = 0 := by
  have hpoint : (fun b => primeWavelet p A b * primeWavelet p B b) =
      tensorFunction (fun i b =>
        (if i ∈ A then centeredPrime (p i) b else 1) *
        (if i ∈ B then centeredPrime (p i) b else 1)) := by
    funext b
    simp only [primeWavelet, tensorFunction, Finset.prod_mul_distrib]
  rw [hpoint, tensorExpectation_tensorFunction]
  have hdiff : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
    by_contra! h
    exact hAB (Finset.ext h)
  obtain ⟨i, hi⟩ := hdiff
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B
  · exact False.elim (hi (iff_of_true hiA hiB))
  · simpa only [hiA, hiB, ↓reduceIte, mul_one] using expect_centeredPrime (hp i)
  · simpa only [hiA, hiB, ↓reduceIte, one_mul] using expect_centeredPrime (hp i)
  · exact False.elim (hi (iff_of_false hiA hiB))

/-- The complete finite Gram matrix is diagonal in the prime wavelet basis. -/
theorem expect_primeWavelet_mul (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (A B : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun b => primeWavelet p A b * primeWavelet p B b) =
      if A = B then primeWaveletWeight p A else 0 := by
  by_cases h : A = B
  · subst B
    simpa only [↓reduceIte, ← pow_two] using expect_primeWavelet_sq p hp A
  · simpa only [h, ↓reduceIte] using expect_primeWavelet_mul_of_ne p hp A B h

/-- Only the empty squarefree coordinate has nonzero mean. -/
theorem expect_primeWavelet (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (A : Finset ι) :
    tensorExpectation (fun i => primeParameter (p i)) (primeWavelet p A) =
      if A = ∅ then 1 else 0 := by
  by_cases h : A = ∅
  · subst A
    have hpoint : primeWavelet p ∅ = (fun _ : ι → Bool => (1 : ℝ)) := by
      funext b
      exact primeWavelet_empty p b
    simp only [hpoint, tensorExpectation_one, ↓reduceIte]
  · simpa only [primeWavelet_empty, mul_one, h, ↓reduceIte] using
      expect_primeWavelet_mul p hp A ∅

end FiniteTensor
end RiemannResearch.RH.FinitePrimeLikelihood

namespace RiemannResearch.RH.ZetaTwoProbability
open FinitePrimeLikelihood

section FinitePrimes
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)

include hp hinj

/-- Orthogonality for the actual zeta(2) measure, with no assumed independence. -/
theorem integral_primeWavelet_mul (A B : Finset ι) :
    (∫ k : ℕ+, primeWavelet (fun i => (p i : ℝ)) A (primeConfiguration p k) *
      primeWavelet (fun i => (p i : ℝ)) B (primeConfiguration p k) ∂Q) =
      if A = B then ∏ i ∈ A, ((p i : ℝ) ^ 2 - 1) else 0 := by
  rw [integral_primeConfiguration p hp hinj
    (fun b => primeWavelet (fun i => (p i : ℝ)) A b *
      primeWavelet (fun i => (p i : ℝ)) B b)]
  apply expect_primeWavelet_mul
  intro i
  exact_mod_cast (hp i).ne_zero

/-- Actual second moment of a squarefree divisibility wavelet. -/
theorem integral_primeWavelet_sq (A : Finset ι) :
    (∫ k : ℕ+, primeWavelet (fun i => (p i : ℝ)) A (primeConfiguration p k) ^ 2 ∂Q) =
      ∏ i ∈ A, ((p i : ℝ) ^ 2 - 1) := by
  simpa only [← pow_two, ↓reduceIte] using integral_primeWavelet_mul p hp hinj A A

/-- Actual mean of a squarefree divisibility wavelet. -/
theorem integral_primeWavelet (A : Finset ι) :
    (∫ k : ℕ+, primeWavelet (fun i => (p i : ℝ)) A (primeConfiguration p k) ∂Q) =
      if A = ∅ then 1 else 0 := by
  rw [integral_primeConfiguration p hp hinj (primeWavelet (fun i => (p i : ℝ)) A)]
  apply expect_primeWavelet
  intro i
  exact_mod_cast (hp i).ne_zero

end FinitePrimes
end RiemannResearch.RH.ZetaTwoProbability
