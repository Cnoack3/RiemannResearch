import RiemannResearch.RH.DyadicRegularizedSummability
import RiemannResearch.RH.DyadicStepMeanIdentity
import RiemannResearch.RH.ParetoResidueMean
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Exact mean of the actual convergent arithmetic family

Source: user-provided DyadicAllScaleConvergenceVerification20260910(2).md,
September 10, 2026, actual arithmetic-head and normalization frontier.
The scalar inversion provider is Mathlib's
`LSeries_one_mul_Lseries_moebius` from `NumberTheory/LSeries/Dirichlet`;
the physical logarithmic residue means are the existing complete Pareto sums.

The complete signed Möbius series and the genuine projected Hilbert series
have mean exactly one for every positive damping. This computes the scalar
normalization; it does not identify the full normalization remainder or bound
its mean-zero energy as damping vanishes.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The scalar Möbius Dirichlet series with positive integer indices. -/
def regularizationMobiusSeries (ε : ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.moebius (n+1) : ℝ) /
    (n+1 : ℝ) ^ (1+ε)

private theorem lSeries_real_eq_succ (a : ℕ → ℝ) (s : ℝ)
    (hs : LSeriesSummable (fun n => (a n : ℂ)) (s : ℂ)) :
    LSeries (fun n => (a n : ℂ)) (s : ℂ) =
      ((∑' n : ℕ, a (n+1) / (n+1 : ℝ)^s : ℝ) : ℂ) := by
  unfold LSeries
  rw [hs.tsum_eq_zero_add, LSeries.term_zero, zero_add, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [LSeries.term_of_ne_zero (by omega), Complex.ofReal_div,
    Complex.ofReal_cpow (by positivity)]
  norm_cast

/-- Scalar inversion is supplied by Mathlib's unconditional Möbius Dirichlet
identity in its actual half-plane of absolute convergence. -/
theorem regularizationZetaSeries_mul_mobius (ε : ℝ) (hε : 0 < ε) :
    regularizationZetaSeries ε * regularizationMobiusSeries ε = 1 := by
  have hs : 1 < (((1+ε : ℝ) : ℂ)).re := by simpa using (show 1 < 1+ε by linarith)
  have hz : LSeries (1 : ℕ → ℂ) ((1+ε : ℝ) : ℂ) =
      (regularizationZetaSeries ε : ℂ) := by
    have hz' := lSeries_real_eq_succ (fun _ => 1) (1+ε)
      (by simpa only [Pi.one_def, Complex.ofReal_one] using
        (LSeriesSummable_one_iff.mpr hs))
    have he : (∑' n : ℕ, (1 : ℝ) / (n+1 : ℝ)^(1+ε)) =
        regularizationZetaSeries ε := by
      unfold regularizationZetaSeries
      apply tsum_congr
      intro n
      rw [Real.rpow_neg (by positivity), one_div]
    simpa only [Pi.one_def, Complex.ofReal_one, he] using hz'
  have hm : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ))
      ((1+ε : ℝ) : ℂ) = (regularizationMobiusSeries ε : ℂ) := by
    simpa only [Complex.ofReal_intCast, regularizationMobiusSeries] using
      lSeries_real_eq_succ (fun n => (ArithmeticFunction.moebius n : ℝ)) (1+ε)
        (by simpa only [Complex.ofReal_intCast] using
          (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs))
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [hz, hm] at h
  exact_mod_cast h

/-- The original physical residue has the exact complete logarithmic mean. -/
theorem hilbertResidue_inner_one (a : ℕ) (ha : 0 < a) :
    inner ℝ (hilbertResidue a ha) hilbertOne = Real.log a := by
  rw [hilbert_inner_one, hilbertResidue_sequence, paretoMean_residue a ha]

theorem dyadicRegularizedTerm_inner_one (ε : ℝ) (m j : ℕ) :
    inner ℝ (dyadicRegularizedTerm ε (m,j)) hilbertOne =
      dyadicRegularizationCoefficient ε m j * Real.log 3 := by
  rw [dyadicRegularizedTerm, real_inner_smul_left]
  have hd := dyadicQuotientDilation_inner_one ((m+1)*3^j) (by positivity)
    (hilbertResidue 3 (by norm_num))
  rw [dyadicQuotientDilation_apply] at hd
  rw [hd, hilbertResidue_inner_one]
  norm_num

/-- Scalar mean of the actual head column; every Möbius sign remains. -/
theorem dyadicRegularizedColumn_zero_inner_one (ε : ℝ) (hε : 0 < ε) :
    inner ℝ (dyadicRegularizedColumn ε 0) hilbertOne =
      regularizationMobiusSeries ε * Real.log 3 := by
  have hs := dyadicRegularizedTerm_column_summable ε
    (dyadicRegularizedTerm_summable hε) 0
  have hmap := (innerSL ℝ hilbertOne).map_tsum hs
  change inner ℝ hilbertOne (∑' n : ℕ, dyadicRegularizedTerm ε (n,0)) =
    ∑' n : ℕ, inner ℝ hilbertOne (dyadicRegularizedTerm ε (n,0)) at hmap
  rw [dyadicRegularizedColumn, real_inner_comm]
  rw [hmap]
  calc
    _ = ∑' n : ℕ, ((ArithmeticFunction.moebius (n+1) : ℝ) /
        (n+1 : ℝ)^(1+ε)) * Real.log 3 := by
      apply tsum_congr
      intro n
      rw [real_inner_comm, dyadicRegularizedTerm_inner_one]
      simp only [dyadicRegularizationCoefficient, pow_zero, mul_one]
    _ = _ := tsum_mul_right

/-- Exact scalar normalization, derived from the actual Hilbert resolvent.
No uniform family bound or arithmetic remainder is assumed. -/
theorem dyadicRegularizedFamily_inner_one (ε : ℝ) (hε : 0 < ε) :
    inner ℝ (dyadicRegularizedFamily ε) hilbertOne = 1 := by
  have h := congrArg (fun f : ThresholdHilbert => inner ℝ f hilbertOne)
    (dyadicRegularizedFamily_resolvent_of_pos hε)
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    dyadicQuotientDilation_inner_one, dyadicRegularizedColumn_zero_inner_one ε hε] at h
  have hlog : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hright : dyadicRegularizationNormalization ε *
      (regularizationMobiusSeries ε * Real.log 3) = 1 - triadicDampingRatio ε := by
    unfold dyadicRegularizationNormalization
    calc
      _ = (regularizationZetaSeries ε * regularizationMobiusSeries ε) *
          (1-triadicDampingRatio ε) := by field_simp [hlog]
      _ = _ := by rw [regularizationZetaSeries_mul_mobius ε hε, one_mul]
  rw [hright] at h
  have hr : 0 < 1 - triadicDampingRatio ε :=
    sub_pos.mpr (triadicDampingRatio_lt_one hε)
  apply (mul_left_cancel₀ (ne_of_gt hr))
  nlinarith [h]

/-- All energy above one is precisely the actual mean-zero error. -/
theorem dyadicRegularizedFamily_norm_sq_eq_one_add_error (ε : ℝ) (hε : 0 < ε) :
    ‖dyadicRegularizedFamily ε‖^2 =
      1 + ‖dyadicRegularizedFamily ε - hilbertOne‖^2 := by
  simpa only [one_pow, one_smul] using
    hilbert_norm_sq_eq_mean_sq_add_centered (dyadicRegularizedFamily ε) 1
      (dyadicRegularizedFamily_inner_one ε hε)

theorem one_le_dyadicRegularizedFamily_norm_sq (ε : ℝ) (hε : 0 < ε) :
    1 ≤ ‖dyadicRegularizedFamily ε‖^2 := by
  rw [dyadicRegularizedFamily_norm_sq_eq_one_add_error ε hε]
  exact le_add_of_nonneg_right (sq_nonneg _)

end
end RiemannResearch.RH.Pareto
