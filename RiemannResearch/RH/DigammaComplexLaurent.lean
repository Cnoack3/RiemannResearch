import RiemannResearch.RH.DigammaLaurentSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The complex digamma Laurent series on the punctured unit disk

The coefficients are the actual Riemann zeta values.  Every finite
truncation has an exact convergent rational-series remainder, bounded by
`‖z‖^(N+1) * ζ(2) / (1 - ‖z‖)`.  In particular this is an identity for the
actual Gamma logarithmic derivative, with no asymptotic or series provider
assumption.

Source for the classical series statement: NIST DLMF 5.7.4
(https://dlmf.nist.gov/5.7.E4). The proof uses the proved actual Gamma
logarithmic-derivative series and an exact finite geometric identity.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.DigammaComplexLaurent

noncomputable section

def remainderTerm (z : ℂ) (N n : ℕ) : ℂ :=
  1 / (((n : ℂ) + 1) ^ (N + 1) * ((n : ℂ) + 1 + z))

def remainder (z : ℂ) (N : ℕ) : ℂ := ∑' n : ℕ, remainderTerm z N n

def laurentTerm (z : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * z ^ (k + 1) * riemannZeta ((k + 2 : ℕ) : ℂ)

private theorem norm_nat_add_one (n : ℕ) :
    ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  have he : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_of_nonneg (by positivity)]

private theorem nat_add_one_ne_zero (n : ℕ) : (n : ℂ) + 1 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_nat_add_one]
  positivity

/-- The disk avoids every digamma pole except its explicitly removed center. -/
theorem mem_integerComplement {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    z ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have hnabs : |(n : ℝ)| < 1 := by
    have h := (Complex.abs_re_le_norm z).trans_lt hz1
    simpa only [← hn, Complex.intCast_re] using h
  have hnlow : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hnabs).1
  have hnhigh : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hnabs).2
  have hn0 : n = 0 := by omega
  subst n
  exact hz0 (by simpa using hn.symm)

theorem denominator_norm_lower {z : ℂ} (hz1 : ‖z‖ < 1) (n : ℕ) :
    ((n : ℝ) + 1) * (1 - ‖z‖) ≤ ‖(n : ℂ) + 1 + z‖ := by
  have hzre : -‖z‖ ≤ z.re := (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hnorm := Complex.re_le_norm ((n : ℂ) + 1 + z)
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hnorm
  have hmul : 0 ≤ (n : ℝ) * ‖z‖ := mul_nonneg (Nat.cast_nonneg n) (norm_nonneg z)
  nlinarith

theorem denominator_ne_zero {z : ℂ} (hz1 : ‖z‖ < 1) (n : ℕ) :
    (n : ℂ) + 1 + z ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (mul_pos (by positivity) (sub_pos.mpr hz1))
    (denominator_norm_lower hz1 n)

/-- Absolute comparison with the ordinary positive p-series. -/
theorem norm_remainderTerm_le {z : ℂ} (hz1 : ‖z‖ < 1) (N n : ℕ) :
    ‖remainderTerm z N n‖ ≤
      (1 / (1 - ‖z‖)) * (1 / (((n : ℝ) + 1) ^ (N + 2))) := by
  have hA : 0 < (n : ℝ) + 1 := by positivity
  have hA0 : (n : ℝ) + 1 ≠ 0 := ne_of_gt hA
  have hδ : 0 < 1 - ‖z‖ := sub_pos.mpr hz1
  have hδ0 : 1 - ‖z‖ ≠ 0 := ne_of_gt hδ
  unfold remainderTerm
  rw [norm_div, norm_one, norm_mul, norm_pow, norm_nat_add_one]
  calc
    _ ≤ 1 / (((n : ℝ) + 1) ^ (N + 1) *
        (((n : ℝ) + 1) * (1 - ‖z‖))) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left (denominator_norm_lower hz1 n) (by positivity)
    _ = _ := by
      rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
      field_simp [hA0, hδ0] <;> simp only [pow_succ] <;> ring

theorem summable_norm_remainderTerm {z : ℂ} (hz1 : ‖z‖ < 1) (N : ℕ) :
    Summable (fun n : ℕ => ‖remainderTerm z N n‖) := by
  exact ((positivePSeries_summable (N + 2) (by omega)).mul_left
    (1 / (1 - ‖z‖))).of_nonneg_of_le (fun n => norm_nonneg _)
      (norm_remainderTerm_le hz1 N)

theorem summable_remainderTerm {z : ℂ} (hz1 : ‖z‖ < 1) (N : ℕ) :
    Summable (remainderTerm z N) := (summable_norm_remainderTerm hz1 N).of_norm

theorem norm_remainder_le_coefficient {z : ℂ} (hz1 : ‖z‖ < 1) (N : ℕ) :
    ‖remainder z N‖ ≤ positivePSeries (N + 2) / (1 - ‖z‖) := by
  have hs := (positivePSeries_summable (N + 2) (by omega)).hasSum.mul_left
    (1 / (1 - ‖z‖))
  have h := tsum_of_norm_bounded hs (norm_remainderTerm_le hz1 N)
  simpa only [remainder, positivePSeries, div_eq_mul_inv, one_mul, mul_comm] using h

theorem norm_remainder_le_two {z : ℂ} (hz1 : ‖z‖ < 1) (N : ℕ) :
    ‖remainder z N‖ ≤ positivePSeries 2 / (1 - ‖z‖) := by
  exact (norm_remainder_le_coefficient hz1 N).trans
    (div_le_div_of_nonneg_right (DigammaSmallArgument.positivePSeries_le_two N)
      (sub_pos.mpr hz1).le)

theorem remainderTerm_recurrence {z : ℂ} (hz1 : ‖z‖ < 1) (N n : ℕ) :
    remainderTerm z N n = 1 / (((n : ℂ) + 1) ^ (N + 2)) -
      z * remainderTerm z (N + 1) n := by
  have h1 := nat_add_one_ne_zero n
  have h2 := denominator_ne_zero hz1 n
  unfold remainderTerm
  rw [show N + 1 + 1 = N + 2 by omega,
    show N + 2 = (N + 1) + 1 by omega, pow_succ]
  field_simp
  ring

private theorem hasSum_zeta_coefficient (N : ℕ) :
    HasSum (fun n : ℕ => 1 / (((n : ℂ) + 1) ^ (N + 2)))
      (riemannZeta ((N + 2 : ℕ) : ℂ)) := by
  have hs := Complex.hasSum_ofReal.mpr
    (positivePSeries_summable (N + 2) (by omega)).hasSum
  change HasSum (fun n : ℕ => ((1 / (((n : ℝ) + 1) ^ (N + 2)) : ℝ) : ℂ))
    (positivePSeries (N + 2) : ℂ) at hs
  rw [positivePSeries_coe_eq_zeta (N + 2) (by omega)] at hs
  convert hs using 1
  ext n
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_natCast]

theorem remainder_recurrence {z : ℂ} (hz1 : ‖z‖ < 1) (N : ℕ) :
    remainder z N = riemannZeta ((N + 2 : ℕ) : ℂ) - z * remainder z (N + 1) := by
  have hs := (hasSum_zeta_coefficient N).sub
    ((summable_remainderTerm hz1 (N + 1)).hasSum.mul_left z)
  have he : (fun n : ℕ => 1 / (((n : ℂ) + 1) ^ (N + 2)) -
      z * remainderTerm z (N + 1) n) = remainderTerm z N := by
    funext n
    exact (remainderTerm_recurrence hz1 N n).symm
  rw [he] at hs
  exact (summable_remainderTerm hz1 N).hasSum.unique hs

theorem digamma_regular_part_eq_remainder_zero {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z =
      z * remainder z 0 := by
  have hs := Zeta23.DigammaSeries.hasSum_digamma_series (mem_integerComplement hz0 hz1)
  have ht := (summable_remainderTerm hz1 0).hasSum.mul_left z
  have he : (fun n : ℕ => z * remainderTerm z 0 n) =
      (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + (n : ℂ) + 1)) := by
    funext n
    have h1 := nat_add_one_ne_zero n
    have h2 := denominator_ne_zero hz1 n
    have h3 : z + (n : ℂ) + 1 ≠ 0 := by
      convert h2 using 1 <;> ring
    unfold remainderTerm
    simp only [zero_add, pow_one]
    field_simp
    ring
  rw [he] at ht
  exact hs.unique ht

/-- The exact all-order complex finite Laurent formula. -/
theorem digamma_laurent_truncation {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : ‖z‖ < 1) (N : ℕ) :
    Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z =
      (∑ k ∈ Finset.range N, laurentTerm z k) +
      (-1 : ℂ) ^ N * z ^ (N + 1) * remainder z N := by
  induction N with
  | zero => simpa using digamma_regular_part_eq_remainder_zero hz0 hz1
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rw [ih, remainder_recurrence hz1 N]
    unfold laurentTerm
    simp only [pow_succ]
    ring

/-- Every complex truncation error has a quantitative geometric bound. -/
theorem digamma_laurent_error_bound {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : ‖z‖ < 1) (N : ℕ) :
    ‖(Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) -
      (∑ k ∈ Finset.range N, laurentTerm z k)‖ ≤
        ‖z‖ ^ (N + 1) * (positivePSeries 2 / (1 - ‖z‖)) := by
  rw [digamma_laurent_truncation hz0 hz1 N, add_sub_cancel_left]
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact mul_le_mul_of_nonneg_left (norm_remainder_le_two hz1 N) (by positivity)

theorem norm_zeta_coefficient (k : ℕ) :
    ‖riemannZeta ((k + 2 : ℕ) : ℂ)‖ = positivePSeries (k + 2) := by
  rw [← positivePSeries_coe_eq_zeta (k + 2) (by omega)]
  exact Complex.norm_of_nonneg
    (positivePSeries_pos (k + 2) (by omega)).le

theorem summable_norm_laurentTerm {z : ℂ} (hz1 : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖laurentTerm z k‖) := by
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hs := (summable_geometric_of_norm_lt_one hr).mul_left
    (‖z‖ * positivePSeries 2)
  apply hs.of_nonneg_of_le (fun k => norm_nonneg _) ?_
  intro k
  unfold laurentTerm
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, norm_zeta_coefficient]
  calc
    _ ≤ ‖z‖ ^ (k + 1) * positivePSeries 2 :=
      mul_le_mul_of_nonneg_left (DigammaSmallArgument.positivePSeries_le_two k)
        (by positivity)
    _ = (‖z‖ * positivePSeries 2) * ‖z‖ ^ k := by rw [pow_succ]; ring

/-- Absolute convergence to the actual digamma regular part throughout the
punctured complex unit disk. -/
theorem hasSum_digamma_laurent {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    HasSum (laurentTerm z)
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (show |‖z‖| < 1 by rwa [abs_of_nonneg (norm_nonneg z)])
  have hg : Tendsto (fun N : ℕ =>
      ‖z‖ ^ (N + 1) * (positivePSeries 2 / (1 - ‖z‖))) atTop (𝓝 0) := by
    convert hp.mul_const (‖z‖ * (positivePSeries 2 / (1 - ‖z‖))) using 1
    · funext N
      rw [pow_succ]
      ring
    · simp
  have he : Tendsto (fun N : ℕ =>
      ‖(Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) -
        (∑ k ∈ Finset.range N, laurentTerm z k)‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
      (fun N => norm_nonneg _) (digamma_laurent_error_bound hz0 hz1)
  apply (summable_norm_laurentTerm hz1).of_norm.hasSum_iff_tendsto_nat.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using he

/-- The full complex Laurent identity, with the pole and all zeta coefficients. -/
theorem digamma_eq_zeta_laurent_tsum {z : ℂ} (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z +
      ∑' k : ℕ, (-1 : ℂ) ^ k * z ^ (k + 1) * riemannZeta ((k + 2 : ℕ) : ℂ) := by
  have h := (hasSum_digamma_laurent hz0 hz1).tsum_eq
  change (∑' k : ℕ, (-1 : ℂ) ^ k * z ^ (k + 1) * riemannZeta ((k + 2 : ℕ) : ℂ)) =
    Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z at h
  rw [h]
  ring

end

end RiemannResearch.RH.Pareto.DigammaComplexLaurent
