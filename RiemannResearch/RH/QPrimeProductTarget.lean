import RiemannResearch.RH.QPrimeProductEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring

/-!
# Exact prime-product error at the derivative target

Source: user-directed Q candidate research, 13 October 2026.
This retains the singleton boundary mass and every signed cross term.
No estimate for the legal primitive is asserted.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.QPrimeProductEnergy
open FinitePrimeLikelihood ZetaTwoProbability

/-- The discrete derivative of the constant-one target. -/
def deltaOne (k : ℕ+) : ℝ := if k = 1 then 1 else 0

theorem integrable_deltaOne : Integrable deltaOne Q := by
  have hpoint : deltaOne = ({1} : Set ℕ+).indicator (fun _ => (1 : ℝ)) := by
    funext k
    simp [deltaOne, Set.indicator]
  rw [hpoint]
  exact (integrable_const (μ := Q) (1 : ℝ)).indicator (measurableSet_singleton 1)

theorem integral_deltaOne : (∫ k : ℕ+, deltaOne k ∂Q) = 1 / zetaTwo := by
  have hZ := zetaTwo_pos
  have hpoint : deltaOne = ({1} : Set ℕ+).indicator (fun _ => (1 : ℝ)) := by
    funext k
    simp [deltaOne, Set.indicator]
  rw [hpoint, integral_indicator_const 1 (measurableSet_singleton 1),
    measureReal_def, measure_singleton,
    ENNReal.toReal_ofReal (by positivity)]
  simp

section FinitePrimes
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, (p i).Prime)

include hp

theorem primeProduct_at_one (t : ι → ℝ) : primeProduct p t 1 = 1 := by
  unfold primeProduct tensorFunction
  apply Finset.prod_eq_one
  intro i _
  simp [factor, primeConfiguration, divisibilityBool, boolIndicator,
    Nat.dvd_one, (hp i).ne_one]

theorem target_error_coordinate (t : ι → ℝ) (a : ℝ) (k : ℕ+) :
    (deltaOne k - (primeProduct p t k - a)) ^ 2 =
      (primeProduct p t k - a) ^ 2 + (2 * a - 1) * deltaOne k := by
  by_cases hk : k = 1
  · subst k
    rw [primeProduct_at_one p hp]
    simp only [deltaOne, ↓reduceIte]
    ring
  · simp only [deltaOne, if_neg hk]
    ring

variable (hinj : Function.Injective p)
include hinj

/-- Complete physical Q error, including the target's exact singleton mass. -/
theorem integral_target_error (t : ι → ℝ) (a : ℝ) :
    (∫ k : ℕ+, (deltaOne k - (primeProduct p t k - a)) ^ 2 ∂Q) =
      (∏ i, (1 + (t i * t i - t i - t i) / (p i : ℝ) ^ 2)) -
        2 * a * (∏ i, (1 - t i / (p i : ℝ) ^ 2)) + a ^ 2 +
        (2 * a - 1) / zetaTwo := by
  simp_rw [target_error_coordinate p hp]
  have hs : Integrable (fun k => (primeProduct p t k - a) ^ 2) Q :=
    integrable_primeConfiguration p
      (fun b => (tensorFunction (fun i => factor (t i)) b - a) ^ 2)
  rw [integral_add hs (integrable_deltaOne.const_mul _),
    integral_const_mul, integral_primeProduct_sub_sq p hp hinj,
    integral_deltaOne]
  ring

/-- At Möbius weights one, the exact derivative error is a signed tail-mass
term plus the square of the slope correction. -/
theorem integral_sieve_target_error (a : ℝ) :
    (∫ k : ℕ+, (deltaOne k - (primeProduct p (fun _ => 1) k - a)) ^ 2 ∂Q) =
      (1 - 2 * a) * ((∏ i, (1 - 1 / (p i : ℝ) ^ 2)) - 1 / zetaTwo) + a ^ 2 := by
  rw [integral_target_error p hp hinj]
  have hlocal (i : ι) :
      1 + ((1 : ℝ) * 1 - 1 - 1) / (p i : ℝ) ^ 2 =
        1 - 1 / (p i : ℝ) ^ 2 := by ring
  simp_rw [hlocal]
  ring

end FinitePrimes
end RiemannResearch.RH.QPrimeProductEnergy
