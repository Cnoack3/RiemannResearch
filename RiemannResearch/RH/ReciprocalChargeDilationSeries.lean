import RiemannResearch.RH.ReciprocalChargeDilationArithmetic
import RiemannResearch.Analysis.BoundedSquareEnergy

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.BoundedSquareEnergy RiemannResearch.NumberTheory

def mobiusDilationCorrelation (h d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius (h * d) : ℝ) /
    (d : ℝ) ^ 2

theorem mobiusDilationCorrelation_summable (h : ℕ) :
    Summable (mobiusDilationCorrelation h) := by
  apply hasSum_zeta_two.summable.of_norm_bounded
  intro d
  have hmu (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  simp only [mobiusDilationCorrelation, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg (d : ℝ))]
  have hprod : |(ArithmeticFunction.moebius d : ℝ)| *
      |(ArithmeticFunction.moebius (h * d) : ℝ)| ≤ 1 := by
    simpa using (mul_le_mul (hmu d) (hmu (h * d))
      (abs_nonneg (ArithmeticFunction.moebius (h * d) : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1))
  exact div_le_div_of_nonneg_right hprod (sq_nonneg (d : ℝ))

theorem dilationMobiusCoefficient_square_summable (h : ℕ) (hh : 0 < h) :
    Summable (fun n => (dilationMobiusCoefficient h n) ^ 2) :=
  summable_square_of_reciprocal_bound (dilationMobiusCoefficient h)
    (dilationMobiusCoefficient_zero h) ((h : ℝ) + 1) (by positivity)
    (fun n hn => dilationMobiusCoefficient_abs_le h n hh hn)

theorem dilationMobiusCoefficient_square_sum_correlation (h M : ℕ) (hh : 0 < h) :
    (∑ n ∈ Finset.Icc 1 M, (dilationMobiusCoefficient h n) ^ 2) =
      (∑ n ∈ Finset.Icc 1 M, (mobiusReciprocalCoefficient n) ^ 2) +
      (∑ d ∈ Finset.Icc 1 (M / h), (mobiusReciprocalCoefficient d) ^ 2) +
      (2 / (h : ℝ)) * ∑ d ∈ Finset.Icc 1 (M / h), mobiusDilationCorrelation h d := by
  have hc : (∑ d ∈ Finset.Icc 1 (M / h),
      mobiusReciprocalCoefficient (h * d) * mobiusReciprocalCoefficient d) =
      (1 / (h : ℝ)) * ∑ d ∈ Finset.Icc 1 (M / h), mobiusDilationCorrelation h d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact dilationMobiusCoefficient_mixed h d
  rw [dilationMobiusCoefficient_square_sum h M hh, hc]
  ring

/-- The squared kernel-coefficient energy keeps the full dilation correlation. -/
theorem dilationMobiusCoefficient_square_tsum (h : ℕ) (hh : 0 < h) :
    (∑' n : ℕ, (dilationMobiusCoefficient h n) ^ 2) =
      30 / Real.pi ^ 2 + (2 / (h : ℝ)) * ∑' d : ℕ, mobiusDilationCorrelation h d := by
  have htdiv : Tendsto (fun M : ℕ => M / h) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b * h)] with M hM
    exact (Nat.le_div_iff_mul_le hh).mpr hM
  have hbaseSummable : Summable (fun n => (mobiusReciprocalCoefficient n) ^ 2) :=
    summable_square_of_reciprocal_bound mobiusReciprocalCoefficient
      mobiusReciprocalCoefficient_zero 1 (by norm_num)
      (fun n _ => mobiusReciprocalCoefficient_abs_le n)
  have hbase := summable_tendsto_sum_Icc _ hbaseSummable (by simp)
  have hcross := summable_tendsto_sum_Icc _ (mobiusDilationCorrelation_summable h)
    (by simp [mobiusDilationCorrelation])
  have hleft := summable_tendsto_sum_Icc _ (dilationMobiusCoefficient_square_summable h hh)
    (by simp)
  have hright : Tendsto
      (fun M => ∑ n ∈ Finset.Icc 1 M, (dilationMobiusCoefficient h n) ^ 2)
      atTop (𝓝 ((∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) +
        (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) +
        (2 / (h : ℝ)) * ∑' d : ℕ, mobiusDilationCorrelation h d)) := by
    convert (hbase.add (hbase.comp htdiv)).add
      ((hcross.comp htdiv).const_mul (2 / (h : ℝ))) using 1
    funext M
    exact dilationMobiusCoefficient_square_sum_correlation h M hh
  have hS : (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) = 15 / Real.pi ^ 2 := by
    simpa only [mobiusReciprocalCoefficient, div_pow] using
      RiemannResearch.NumberTheory.squarefree_reciprocal_square_sum
  calc
    _ = (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) +
        (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) +
        (2 / (h : ℝ)) * ∑' d : ℕ, mobiusDilationCorrelation h d :=
      tendsto_nhds_unique hleft hright
    _ = _ := by rw [hS]; ring

/-- Equivalent coefficient-product form of the correlation series. -/
theorem dilationMobiusCoefficient_mixed_tsum (h : ℕ) :
    (∑' d : ℕ, mobiusReciprocalCoefficient (h * d) * mobiusReciprocalCoefficient d) =
      (1 / (h : ℝ)) * ∑' d : ℕ, mobiusDilationCorrelation h d := by
  simp_rw [dilationMobiusCoefficient_mixed]
  exact tsum_mul_left

theorem dilationMobiusCoefficient_square_tsum_mixed (h : ℕ) (hh : 0 < h) :
    (∑' n : ℕ, (dilationMobiusCoefficient h n) ^ 2) =
      30 / Real.pi ^ 2 + 2 *
        ∑' d : ℕ, mobiusReciprocalCoefficient (h * d) * mobiusReciprocalCoefficient d := by
  rw [dilationMobiusCoefficient_square_tsum h hh, dilationMobiusCoefficient_mixed_tsum]
  ring

theorem dilationMobiusCoefficient_square_tsum_exact (h : ℕ) (hh : 0 < h) :
    (∑' n : ℕ, (dilationMobiusCoefficient h n) ^ 2) =
      2 * (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) + 2 *
        ∑' d : ℕ, mobiusReciprocalCoefficient (h * d) * mobiusReciprocalCoefficient d := by
  have hS : (∑' n : ℕ, (mobiusReciprocalCoefficient n) ^ 2) = 15 / Real.pi ^ 2 := by
    simpa only [mobiusReciprocalCoefficient, div_pow] using
      RiemannResearch.NumberTheory.squarefree_reciprocal_square_sum
  rw [dilationMobiusCoefficient_square_tsum_mixed h hh, hS]
  ring

end RiemannResearch.RH.Pareto
