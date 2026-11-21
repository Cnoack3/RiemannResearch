import RiemannResearch.Analysis.LogarithmicPrimePairs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

/-!
# A dyadic lower bound from consecutive prime gaps

Goldston, Pintz and Yıldırım, *Primes in tuples IV: Density of small gaps
between consecutive primes*, Acta Arith. 160 (2013), Theorem 1,
https://doi.org/10.4064/aa160-1-3, supplies a positive lower bound of order
X/log X for the count below at each sufficiently small fixed positive width.
The comparison proved here uses the actual von Mangoldt function and
retains its full weighting. The published counting estimate is a parameter.
-/

noncomputable section
open Filter Finset
open scoped BigOperators ArithmeticFunction Topology

namespace RiemannResearch.Analysis.LogarithmicPrimePairs

/-- Lower primes in (X,2X] whose following prime is at most d log X away. -/
def smallGapStarts (d X : ℝ) : Finset ℕ := by
  classical
  exact (Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter fun p => p.Prime ∧
    ∃ h ∈ Ioc 0 (shiftWidth d X), (p + h).Prime ∧
      ∀ m ∈ Ioo p (p + h), ¬ m.Prime

/-- Each consecutive prime pair contributes at least (log X)^2 to the numerator. -/
theorem smallGapStarts_le_sharp (d X : ℝ) (hX : 1 < X) :
    (smallGapStarts d X).card * Real.log X / X ≤ sharpPairAverage 1 2 d X := by
  classical
  have hx : 0 < X := by linarith
  have hl := Real.log_pos hX
  let total := fun n : ℕ => ∑ h ∈ Ioc 0 (shiftWidth d X), Λ n * Λ (n + h)
  have hrow (p : ℕ) (hp : p ∈ smallGapStarts d X) : (Real.log X)^2 ≤ total p := by
    obtain ⟨hpI, hprime, h, hh, hnext, _⟩ := mem_filter.mp hp
    have hp' : ⌊X⌋₊ + 1 ≤ p := (mem_Ioc.mp hpI).1
    have hpX : X ≤ (p : ℝ) := (Nat.lt_floor_add_one X).le.trans (by exact_mod_cast hp')
    have hpl := Real.log_le_log hx hpX
    have hpq : (p : ℝ) ≤ ((p + h : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right p h
    have hql := Real.log_le_log hx (hpX.trans hpq)
    calc
      (Real.log X)^2 ≤ Real.log p * Real.log ((p + h : ℕ) : ℝ) := by
        rw [pow_two]
        exact mul_le_mul hpl hql hl.le (hl.le.trans hpl)
      _ = Λ p * Λ (p + h) := by simp only [ArithmeticFunction.vonMangoldt_apply_prime hprime,
          ArithmeticFunction.vonMangoldt_apply_prime hnext]
      _ ≤ total p := single_le_sum (fun j _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        ArithmeticFunction.vonMangoldt_nonneg) hh
  have hs : (smallGapStarts d X).card * (Real.log X)^2 ≤
      ∑ n ∈ Ioc ⌊X⌋₊ ⌊2 * X⌋₊, total n := by
    calc
      _ = ∑ _p ∈ smallGapStarts d X, (Real.log X)^2 := by simp
      _ ≤ ∑ p ∈ smallGapStarts d X, total p := sum_le_sum hrow
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ =>
        sum_nonneg fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          ArithmeticFunction.vonMangoldt_nonneg
  unfold sharpPairAverage
  rw [one_mul]
  calc
    _ = ((smallGapStarts d X).card * (Real.log X)^2) / (X * Real.log X) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hs (mul_pos hx hl).le

/-- Specializing with the positive density in GPY IV gives a positive lower bound
for the dyadic statistic. -/
theorem eventually_lower_of_smallGapCount {c d : ℝ}
    (hcount : ∀ᶠ X : ℝ in atTop, c * X / Real.log X ≤ (smallGapStarts d X).card) :
    ∀ᶠ X : ℝ in atTop, c ≤ sharpPairAverage 1 2 d X := by
  filter_upwards [hcount, eventually_gt_atTop (1 : ℝ)] with X hcount hX
  have hx : 0 < X := by linarith
  apply le_trans _ (smallGapStarts_le_sharp d X hX)
  exact (le_div_iff₀ hx).mpr ((div_le_iff₀ (Real.log_pos hX)).mp hcount)

end RiemannResearch.Analysis.LogarithmicPrimePairs
