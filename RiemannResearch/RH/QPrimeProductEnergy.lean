import RiemannResearch.RH.ZetaTwoPrimeConsumers
import RiemannResearch.RH.FinitePrimeDivisibilityMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact Q energies of finite prime products

Source: user-directed Q candidate research, 13 October 2026.
The finite products below are divisor-side observables. They are not declared
to be legal residue candidates. All moments use the actual inverse-square law.
The mixed product identity retains every cross term before specialization.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.QPrimeProductEnergy
open FinitePrimeLikelihood ZetaTwoProbability

/-- One signed affine divisibility factor. -/
def factor (t : ℝ) (b : Bool) : ℝ := 1 - t * boolIndicator b

theorem expect_factor (q t : ℝ) :
    bernoulliExpectation q (factor t) = 1 - t * q := by
  simp [bernoulliExpectation, factor, boolIndicator]
  ring

/-- Exact local mixed moment, including the signed linear terms. -/
theorem expect_factor_mul (q t u : ℝ) :
    bernoulliExpectation q (fun b => factor t b * factor u b) =
      1 + (t * u - t - u) * q := by
  simp [bernoulliExpectation, factor, boolIndicator]
  ring

section FinitePrimes
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Literal product over a finite family of prime divisibility coordinates. -/
def primeProduct (p : ι → ℕ) (t : ι → ℝ) (k : ℕ+) : ℝ :=
  tensorFunction (fun i => factor (t i)) (primeConfiguration p k)

theorem integrable_primeProduct (p : ι → ℕ) (t : ι → ℝ) :
    Integrable (primeProduct p t) Q :=
  integrable_primeConfiguration p (tensorFunction (fun i => factor (t i)))

theorem integrable_primeProduct_mul (p : ι → ℕ) (t u : ι → ℝ) :
    Integrable (fun k => primeProduct p t k * primeProduct p u k) Q :=
  integrable_primeConfiguration p
    (fun b => tensorFunction (fun i => factor (t i)) b *
      tensorFunction (fun i => factor (u i)) b)

variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)

include hp hinj

theorem integral_primeProduct (t : ι → ℝ) :
    (∫ k : ℕ+, primeProduct p t k ∂Q) =
      ∏ i, (1 - t i / (p i : ℝ) ^ 2) := by
  unfold primeProduct
  rw [integral_primeConfiguration p hp hinj (tensorFunction (fun i => factor (t i))),
    tensorExpectation_tensorFunction]
  simp only [expect_factor, primeParameter, div_eq_mul_inv, one_mul]

/-- Independence gives the full mixed Gram product for arbitrary real weights. -/
theorem integral_primeProduct_mul (t u : ι → ℝ) :
    (∫ k : ℕ+, primeProduct p t k * primeProduct p u k ∂Q) =
      ∏ i, (1 + (t i * u i - t i - u i) / (p i : ℝ) ^ 2) := by
  change (∫ k : ℕ+,
    (tensorFunction (fun i => factor (t i)) (primeConfiguration p k) *
      tensorFunction (fun i => factor (u i)) (primeConfiguration p k)) ∂Q) = _
  rw [integral_primeConfiguration p hp hinj
    (fun b => tensorFunction (fun i => factor (t i)) b *
      tensorFunction (fun i => factor (u i)) b)]
  have hpoint :
      (fun b => tensorFunction (fun i => factor (t i)) b *
        tensorFunction (fun i => factor (u i)) b) =
      tensorFunction (fun i b => factor (t i) b * factor (u i) b) := by
    funext b
    simp only [tensorFunction, Finset.prod_mul_distrib]
  rw [hpoint, tensorExpectation_tensorFunction]
  simp only [expect_factor_mul, primeParameter, div_eq_mul_inv, one_mul]

/-- Exact second moment of a shifted prime product. -/
theorem integral_primeProduct_sub_sq (t : ι → ℝ) (a : ℝ) :
    (∫ k : ℕ+, (primeProduct p t k - a) ^ 2 ∂Q) =
      (∏ i, (1 + (t i * t i - t i - t i) / (p i : ℝ) ^ 2)) -
      2 * a * (∏ i, (1 - t i / (p i : ℝ) ^ 2)) + a ^ 2 := by
  have hpoint : (fun k => (primeProduct p t k - a) ^ 2) =
      (fun k => (primeProduct p t k * primeProduct p t k -
        (2 * a) * primeProduct p t k) + a ^ 2) := by
    funext k
    ring
  have hsub : Integrable
      (fun k => primeProduct p t k * primeProduct p t k - (2 * a) * primeProduct p t k) Q :=
    (integrable_primeProduct_mul p t t).sub
      ((integrable_primeProduct p t).const_mul (2 * a))
  have hlin : Integrable (fun k => (2 * a) * primeProduct p t k) Q :=
    (integrable_primeProduct p t).const_mul (2 * a)
  rw [hpoint, integral_add hsub (integrable_const (μ := Q) (a ^ 2)),
    integral_sub (integrable_primeProduct_mul p t t) hlin,
    integral_const_mul, integral_primeProduct_mul p hp hinj,
    integral_primeProduct p hp hinj]
  simp

/-- Multiplying each Möbius coefficient by its conductor has an exact
dimension-dependent second moment; independence does not give a uniform bound. -/
theorem integral_conductorWeightedProduct_sq :
    (∫ k : ℕ+, primeProduct p (fun i => (p i : ℝ)) k ^ 2 ∂Q) =
      2 ^ Fintype.card ι * (∏ i, (1 - 1 / (p i : ℝ))) := by
  simp only [pow_two]
  rw [integral_primeProduct_mul p hp hinj]
  have hlocal (i : ι) :
      1 + ((p i : ℝ) * (p i : ℝ) - (p i : ℝ) - (p i : ℝ)) /
        (p i : ℝ) ^ 2 = 2 * (1 - 1 / (p i : ℝ)) := by
    have hp0 : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    field_simp [hp0]
    ring
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  simp

/-- The unweighted inclusion-exclusion product has exactly its mean as its
second moment. This is a bounded derivative-side sieve, not a primitive bound. -/
theorem integral_sieve_sq :
    (∫ k : ℕ+, primeProduct p (fun _ => (1 : ℝ)) k ^ 2 ∂Q) =
      ∏ i, (1 - 1 / (p i : ℝ) ^ 2) := by
  simp only [pow_two]
  rw [integral_primeProduct_mul p hp hinj]
  apply Finset.prod_congr rfl
  intro i _
  ring

end FinitePrimes
end RiemannResearch.RH.QPrimeProductEnergy
