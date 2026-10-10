import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

Exact algebra of the annular second-Riesz filter from
`RH_Centered_Arithmetic_Zero_Ordinates_20261009.md`.
The actual von Mangoldt weights and lattice correction are retained.
-/

open scoped BigOperators

namespace RiemannResearch.RH

noncomputable def rieszTwoWeight (u : ℝ) : ℝ := (max (1 - u) 0) ^ 2

noncomputable def annularArithmeticWeight (u : ℝ) : ℝ :=
  rieszTwoWeight u - (7 / 4 : ℝ) * rieszTwoWeight (2 * u) +
    (7 / 8 : ℝ) * rieszTwoWeight (4 * u) -
    (1 / 8 : ℝ) * rieszTwoWeight (8 * u)

theorem rieszTwoWeight_of_le_one {u : ℝ} (hu : u ≤ 1) :
    rieszTwoWeight u = (1 - u) ^ 2 := by
  rw [rieszTwoWeight, max_eq_left (by linarith : (0 : ℝ) ≤ 1 - u)]

theorem rieszTwoWeight_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    rieszTwoWeight u = 0 := by
  rw [rieszTwoWeight, max_eq_right (by linarith : 1 - u ≤ (0 : ℝ))]
  ring

theorem annularArithmeticWeight_eq_zero_of_le_eighth {u : ℝ}
    (hu : u ≤ 1 / 8) : annularArithmeticWeight u = 0 := by
  rw [annularArithmeticWeight,
    rieszTwoWeight_of_le_one (by linarith : u ≤ 1),
    rieszTwoWeight_of_le_one (by linarith : 2 * u ≤ 1),
    rieszTwoWeight_of_le_one (by linarith : 4 * u ≤ 1),
    rieszTwoWeight_of_le_one (by linarith : 8 * u ≤ 1)]
  ring

theorem annularArithmeticWeight_first_piece {u : ℝ}
    (hlo : 1 / 8 ≤ u) (hhi : u ≤ 1 / 4) :
    annularArithmeticWeight u = 8 * (u - 1 / 8) ^ 2 := by
  rw [annularArithmeticWeight,
    rieszTwoWeight_of_le_one (by linarith : u ≤ 1),
    rieszTwoWeight_of_le_one (by linarith : 2 * u ≤ 1),
    rieszTwoWeight_of_le_one (by linarith : 4 * u ≤ 1),
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 8 * u)]
  ring

theorem annularArithmeticWeight_middle_piece {u : ℝ}
    (hlo : 1 / 4 ≤ u) (hhi : u ≤ 1 / 2) :
    annularArithmeticWeight u = -(3 / 4 : ℝ) + 5 * u - 6 * u ^ 2 := by
  rw [annularArithmeticWeight,
    rieszTwoWeight_of_le_one (by linarith : u ≤ 1),
    rieszTwoWeight_of_le_one (by linarith : 2 * u ≤ 1),
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 4 * u),
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 8 * u)]
  ring

theorem annularArithmeticWeight_middle_nonnegative_form {u : ℝ}
    (hlo : 1 / 4 ≤ u) (hhi : u ≤ 1 / 2) :
    annularArithmeticWeight u =
      6 * (u - 1 / 4) * (1 / 2 - u) + u / 2 := by
  rw [annularArithmeticWeight_middle_piece hlo hhi]
  ring

theorem annularArithmeticWeight_last_piece {u : ℝ}
    (hlo : 1 / 2 ≤ u) (hhi : u ≤ 1) :
    annularArithmeticWeight u = (1 - u) ^ 2 := by
  rw [annularArithmeticWeight,
    rieszTwoWeight_of_le_one hhi,
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 2 * u),
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 4 * u),
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 8 * u)]
  ring

theorem annularArithmeticWeight_eq_zero_of_one_le {u : ℝ}
    (hu : 1 ≤ u) : annularArithmeticWeight u = 0 := by
  rw [annularArithmeticWeight,
    rieszTwoWeight_of_one_le hu,
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 2 * u),
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 4 * u),
    rieszTwoWeight_of_one_le (by linarith : 1 ≤ 8 * u)]
  ring

theorem annularArithmeticWeight_nonnegative (u : ℝ) :
    0 ≤ annularArithmeticWeight u := by
  by_cases h0 : u ≤ 1 / 8
  · rw [annularArithmeticWeight_eq_zero_of_le_eighth h0]
  · by_cases h1 : u ≤ 1 / 4
    · rw [annularArithmeticWeight_first_piece (by linarith) h1]
      positivity
    · by_cases h2 : u ≤ 1 / 2
      · rw [annularArithmeticWeight_middle_nonnegative_form (by linarith) h2]
        have ha : 0 ≤ u - 1 / 4 := by linarith
        have hb : 0 ≤ 1 / 2 - u := by linarith
        have hu : 0 ≤ u := by linarith
        positivity
      · by_cases h3 : u ≤ 1
        · rw [annularArithmeticWeight_last_piece (by linarith) h3]
          positivity
        · rw [annularArithmeticWeight_eq_zero_of_one_le (by linarith)]

theorem annularArithmeticWeight_zero_outside {u : ℝ}
    (hu : u ≤ 1 / 8 ∨ 1 ≤ u) : annularArithmeticWeight u = 0 := by
  rcases hu with hu | hu
  · exact annularArithmeticWeight_eq_zero_of_le_eighth hu
  · exact annularArithmeticWeight_eq_zero_of_one_le hu

theorem annularArithmeticWeight_middle_completed_square {u : ℝ}
    (hlo : 1 / 4 ≤ u) (hhi : u ≤ 1 / 2) :
    annularArithmeticWeight u = 7 / 24 - 6 * (u - 5 / 12) ^ 2 := by
  rw [annularArithmeticWeight_middle_piece hlo hhi]
  ring

/-- Sharp global pointwise upper bound, useful for uniform Fourier and product bounds. -/
theorem annularArithmeticWeight_le_seven_twentyfourths (u : ℝ) :
    annularArithmeticWeight u ≤ 7 / 24 := by
  by_cases h0 : u ≤ 1 / 8
  · rw [annularArithmeticWeight_eq_zero_of_le_eighth h0]
    norm_num
  · by_cases h1 : u ≤ 1 / 4
    · rw [annularArithmeticWeight_first_piece (by linarith) h1]
      have hp : 0 ≤ (u - 1 / 8) * (1 / 4 - u) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    · by_cases h2 : u ≤ 1 / 2
      · rw [annularArithmeticWeight_middle_completed_square (by linarith) h2]
        nlinarith [sq_nonneg (u - 5 / 12)]
      · by_cases h3 : u ≤ 1
        · rw [annularArithmeticWeight_last_piece (by linarith) h3]
          have hp : 0 ≤ (1 - u) * (u - 1 / 2) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
        · rw [annularArithmeticWeight_eq_zero_of_one_le (by linarith)]
          norm_num

theorem annularArithmeticWeight_at_five_twelfths :
    annularArithmeticWeight (5 / 12) = 7 / 24 := by
  rw [annularArithmeticWeight_middle_completed_square (by norm_num) (by norm_num)]
  norm_num

/-- Exact comparable-scale localization; even the ratio-eight endpoint vanishes. -/
theorem annularArithmeticWeight_mul_eq_zero_of_eight_mul_le
    {a b x : ℝ} (hx : 0 < x) (hab : 8 * b ≤ a) :
    annularArithmeticWeight (a / x) * annularArithmeticWeight (b / x) = 0 := by
  by_cases hxa : x ≤ a
  · have ha : 1 ≤ a / x := (le_div_iff₀ hx).2 (by simpa using hxa)
    rw [annularArithmeticWeight_eq_zero_of_one_le ha]
    ring
  · have hb : b / x ≤ 1 / 8 := (div_le_iff₀ hx).2 (by linarith)
    rw [annularArithmeticWeight_eq_zero_of_le_eighth hb]
    ring

/-- Generic transport version: no analytic domain or division hypotheses are needed. -/
def transportDifference {α : Type*} (T : α → α) (a : ℝ)
    (f : α → ℝ) (x : α) : ℝ := f x - a * f (T x)

theorem transportDifference_triple {α : Type*} (T : α → α)
    (a b c : ℝ) (f : α → ℝ) (x : α) :
    transportDifference T a
      (transportDifference T b (transportDifference T c f)) x =
      f x - (a + b + c) * f (T x) +
        (a * b + a * c + b * c) * f (T (T x)) -
        (a * b * c) * f (T (T (T x))) := by
  simp only [transportDifference]
  ring

theorem transportDifference_annular {α : Type*} (T : α → α)
    (f : α → ℝ) (x : α) :
    transportDifference T 1
      (transportDifference T (1 / 2) (transportDifference T (1 / 4) f)) x =
      f x - (7 / 4 : ℝ) * f (T x) +
        (7 / 8 : ℝ) * f (T (T x)) -
        (1 / 8 : ℝ) * f (T (T (T x))) := by
  rw [transportDifference_triple]
  ring

noncomputable def annularCenteredFinite (s : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ s, (ArithmeticFunction.vonMangoldt n - 1) *
    annularArithmeticWeight (n / x)

noncomputable def annularPrimeFinite (s : Finset ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ s, ArithmeticFunction.vonMangoldt n *
    annularArithmeticWeight (n / x)) - (7 / 64 : ℝ) * x

noncomputable def annularLatticeFinite (s : Finset ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ s, annularArithmeticWeight (n / x)) - (7 / 64 : ℝ) * x

/-- The exact actual arithmetic centering retains the entire lattice correction. -/
theorem annularPrimeFinite_eq_centered_add_lattice (s : Finset ℕ) (x : ℝ) :
    annularPrimeFinite s x = annularCenteredFinite s x + annularLatticeFinite s x := by
  simp only [annularPrimeFinite, annularCenteredFinite, annularLatticeFinite,
    sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

end RiemannResearch.RH
