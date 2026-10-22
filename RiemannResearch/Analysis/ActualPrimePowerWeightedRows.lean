import RiemannResearch.Analysis.ActualLogarithmicCovarianceAssembly
import RiemannResearch.Analysis.PrimePowerCovarianceRowBudget
import RiemannResearch.Analysis.LogarithmicWeightedRowAux
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual arithmetic covariance rows with reciprocal-square-root weights

The exact conjugation identifies the complete signed arithmetic coefficient
with the existing directed entry. Its upward-multiple and downward-divisor
terms are both retained. The elementary project Mertens bound then supplies
the weighted rows without an arithmetic provider premise.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualPrimePowerWeightedRows

open ActualZeroOrdinate ActualDirichletPolynomialGram LogarithmicSamplingBounds
open RiemannResearch.Fourier

def reciprocalSqrtWeight (n : ℕ) : ℝ := 1 / Real.sqrt (n : ℝ)

theorem reciprocalSqrtWeight_nonneg (n : ℕ) : 0 ≤ reciprocalSqrtWeight n :=
  one_div_nonneg.mpr (Real.sqrt_nonneg _)

theorem reciprocalSqrtWeight_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < reciprocalSqrtWeight n := by
  apply one_div_pos.mpr
  apply Real.sqrt_pos.mpr
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)

private theorem downward_sqrt_normalization (a b c l : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    (l / (c * Real.sqrt (a / b))) * (1 / Real.sqrt b) =
      (l / c) * (1 / Real.sqrt a) := by
  rw [Real.sqrt_div ha.le b]
  field_simp [hc, (Real.sqrt_pos.mpr ha).ne', (Real.sqrt_pos.mpr hb).ne']
  <;> ring

private theorem upward_sqrt_normalization (a b c l : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    (l / (c * Real.sqrt (b / a))) * (1 / Real.sqrt b) =
      ((l / (b / a)) / c) * (1 / Real.sqrt a) := by
  rw [Real.sqrt_div hb.le a]
  field_simp [hc, ha.ne', hb.ne',
    (Real.sqrt_pos.mpr ha).ne', (Real.sqrt_pos.mpr hb).ne']
  <;> ring_nf
  <;> simp only [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  <;> ring

theorem norm_signedArithmetic_of_ne {n m : ℕ} (hne : n ≠ m) :
    ‖signedArithmetic n m‖ = rationalLandauMain (max n m) (min n m) := by
  simp only [signedArithmetic, if_neg hne, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (rationalLandauMain_nonneg _ _)]

/-- Exact weighted entry identity. Neither of the two divisibility directions
is discarded, and the diagonal vanishes through `vonMangoldt 1 = 0`. -/
theorem signedArithmetic_weighted_directed {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ‖signedArithmetic n m‖ * reciprocalSqrtWeight m =
      (primePowerCovarianceDirectedEntry n m / (2 * Real.pi)) *
        reciprocalSqrtWeight n := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hpi : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  by_cases hne : n = m
  · subst m
    simp [signedArithmetic, primePowerCovarianceDirectedEntry, Nat.div_self hnpos,
      ArithmeticFunction.vonMangoldt_apply_one]
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hnot : ¬ m ∣ n := Nat.not_dvd_of_pos_of_lt hnpos hlt
      rw [norm_signedArithmetic_of_ne hne, max_eq_right hlt.le, min_eq_left hlt.le,
        rationalLandauMain_eq_vonMangoldt_div_sqrt hn hlt]
      unfold primePowerCovarianceDirectedEntry
      by_cases hd : n ∣ m
      · rw [if_pos hd, if_neg hnot, add_zero]
        have hq : ((m / n : ℕ) : ℝ) = (m : ℝ) / (n : ℝ) := by
          apply (eq_div_iff hnR.ne').mpr
          exact_mod_cast Nat.div_mul_cancel hd
        rw [hq]
        simpa only [reciprocalSqrtWeight, if_pos hd] using
          upward_sqrt_normalization (n : ℝ) (m : ℝ) (2 * Real.pi)
            (ArithmeticFunction.vonMangoldt (m / n)) hnR hmR hpi
      · simp [hd, hnot]
    · have hnot : ¬ n ∣ m := Nat.not_dvd_of_pos_of_lt hmpos hgt
      rw [norm_signedArithmetic_of_ne hne, max_eq_left hgt.le, min_eq_right hgt.le,
        rationalLandauMain_eq_vonMangoldt_div_sqrt hm hgt]
      unfold primePowerCovarianceDirectedEntry
      by_cases hd : m ∣ n
      · rw [if_neg hnot, if_pos hd, zero_add]
        simpa only [reciprocalSqrtWeight, if_pos hd] using
          downward_sqrt_normalization (n : ℝ) (m : ℝ) (2 * Real.pi)
            (ArithmeticFunction.vonMangoldt (n / m)) hnR hmR hpi
      · simp [hd, hnot]

/-- The normalized entry equality in weighted Schur coordinates. -/
theorem signedArithmetic_normalized_weighted_entry {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (‖signedArithmetic n m‖ * reciprocalSqrtWeight m) / reciprocalSqrtWeight n =
      primePowerCovarianceDirectedEntry n m / (2 * Real.pi) := by
  rw [signedArithmetic_weighted_directed hn hm]
  simp [(reciprocalSqrtWeight_pos hn).ne']

/-- Exact row reindexing into the existing full arithmetic budget. -/
theorem signedArithmetic_weighted_row_eq (X n : ℕ) (hn : 1 ≤ n) (hnX : n ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * reciprocalSqrtWeight m) =
      (primePowerCovarianceRowBudget X n / (2 * Real.pi)) *
        reciprocalSqrtWeight n := by
  have hset : (Finset.Icc 1 X : Finset ℕ) = Finset.Ioc 0 X := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    _ = ∑ m ∈ Finset.Icc 1 X,
        (primePowerCovarianceDirectedEntry n m / (2 * Real.pi)) *
          reciprocalSqrtWeight n := by
      apply Finset.sum_congr rfl
      intro m hm
      exact signedArithmetic_weighted_directed hn (Finset.mem_Icc.mp hm).1
    _ = (∑ m ∈ Finset.Icc 1 X, primePowerCovarianceDirectedEntry n m) /
        (2 * Real.pi) * reciprocalSqrtWeight n := by
      simp only [Finset.sum_mul, Finset.sum_div]
    _ = _ := by rw [hset, sum_primePowerCovarianceDirectedEntry_eq X n hn hnX]

/-- Exact normalized row, retaining the complete multiple/divisor budget. -/
theorem signedArithmetic_normalized_weighted_row_eq (X n : ℕ)
    (hn : 1 ≤ n) (hnX : n ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * reciprocalSqrtWeight m) /
        reciprocalSqrtWeight n = primePowerCovarianceRowBudget X n / (2 * Real.pi) := by
  rw [signedArithmetic_weighted_row_eq X n hn hnX]
  simp [(reciprocalSqrtWeight_pos hn).ne']

def arithmeticRowConstant (X : ℕ) : ℝ :=
  (Real.log (X : ℝ) + Real.log 4 + 4) / (2 * Real.pi)

/-- The unconditional normalized weighted arithmetic row bound. -/
theorem signedArithmetic_weighted_row_le (X n : ℕ) (hn : 1 ≤ n) (hnX : n ≤ X) :
    (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * reciprocalSqrtWeight m) ≤
      arithmeticRowConstant X * reciprocalSqrtWeight n := by
  rw [signedArithmetic_weighted_row_eq X n hn hnX]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (primePowerCovarianceRowBudget_le X n hn hnX)
      (by positivity)) (reciprocalSqrtWeight_nonneg n)

/-- Both weighted row providers, supplied for the actual arithmetic matrix. -/
theorem signedArithmetic_weighted_rows (X : ℕ) :
    (∀ n ∈ Finset.Icc 1 X,
      (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * reciprocalSqrtWeight m) ≤
        arithmeticRowConstant X * reciprocalSqrtWeight n) ∧
    (∀ n ∈ Finset.Icc 1 X,
      (∑ m ∈ Finset.Icc 1 X,
        (‖signedArithmetic n m‖ * logSquareEnvelope n m) * reciprocalSqrtWeight m) ≤
          (Real.log (X : ℝ) ^ 2 * arithmeticRowConstant X) *
            reciprocalSqrtWeight n) := by
  have hrow0 : ∀ n ∈ (Finset.Icc 1 X : Finset ℕ),
      (∑ m ∈ Finset.Icc 1 X, ‖signedArithmetic n m‖ * reciprocalSqrtWeight m) ≤
        arithmeticRowConstant X * reciprocalSqrtWeight n := by
    intro n hn
    exact signedArithmetic_weighted_row_le X n
      (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  refine ⟨hrow0, ?_⟩
  exact weighted_logSquare_row_bound X signedArithmetic reciprocalSqrtWeight
    (arithmeticRowConstant X)
    (fun n hn => reciprocalSqrtWeight_pos (Finset.mem_Icc.mp hn).1) hrow0

end RiemannResearch.Analysis.ActualPrimePowerWeightedRows
