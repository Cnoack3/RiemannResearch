import RiemannResearch.RH.ConditionalUniformMixture
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Uniform-interval mixture for the inverse-square law

Source: user's P/Q change-of-measure question (1 November 2026).
The formula is obtained by discrete differentiation of the inverse-square
marginal. All finite identities retain their endpoint remainder.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QUniformMixture
open ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative

/-- Positive physical endpoints are used; the zero value is not an atom. -/
def qMixtureWeight (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) / (zetaTwo * (n : ℝ) * ((n : ℝ) + 1) ^ 2)

theorem qMixtureWeight_nonneg (n : ℕ) : 0 ≤ qMixtureWeight n := by
  have hz := zetaTwo_pos
  unfold qMixtureWeight
  positivity

theorem qMixtureWeight_pos (n : ℕ) (hn : 0 < n) : 0 < qMixtureWeight n := by
  have hz := zetaTwo_pos
  unfold qMixtureWeight
  positivity

theorem qMixtureWeight_step (n : ℕ) (hn : 0 < n) :
    qMixtureWeight n = (n : ℝ) * (positiveQWeight n - positiveQWeight (n + 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold qMixtureWeight positiveQWeight
  push_cast
  field_simp [ne_of_gt zetaTwo_pos]
  ring

theorem qMixture_density_step (n : ℕ) (hn : 0 < n) :
    qMixtureWeight n / (n : ℝ) = positiveQWeight n - positiveQWeight (n + 1) := by
  rw [qMixtureWeight_step n hn]
  exact mul_div_cancel_left₀ _ (by positivity : (n : ℝ) ≠ 0)

theorem qMixture_partial_sum (N : ℕ) :
    (∑ k ∈ Finset.range N, qMixtureWeight (k + 1)) =
      (∑ k ∈ Finset.range N, positiveQWeight (k + 1)) -
        (N : ℝ) * positiveQWeight (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      qMixtureWeight_step (N + 1) (by omega)]
    push_cast
    ring

private theorem qBoundary_tendsto_zero :
    Tendsto (fun N : ℕ => (N : ℝ) * positiveQWeight (N + 1)) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
  have he (N : ℕ) : (N : ℝ) * positiveQWeight (N + 1) =
      (1 / ((N : ℝ) + 1) - (1 / ((N : ℝ) + 1)) ^ 2) / zetaTwo := by
    unfold positiveQWeight
    push_cast
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [he]
  convert (hi.sub (hi.pow 2)).div_const zetaTwo using 1
  norm_num

theorem hasSum_qMixtureWeight :
    HasSum (fun k : ℕ => qMixtureWeight (k + 1)) 1 := by
  have hs : HasSum (fun k : ℕ => positiveQWeight (k + 1)) 1 := by
    have hsum := positiveQWeight_summable.tsum_eq_zero_add
    have hzero : positiveQWeight 0 = 0 := by simp [positiveQWeight]
    rw [positiveQWeight_tsum, hzero, zero_add] at hsum
    exact hsum ▸ ((summable_nat_add_iff 1).mpr positiveQWeight_summable).hasSum
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => qMixtureWeight_nonneg (k + 1)) _).2
  simp_rw [qMixture_partial_sum]
  simpa using hs.tendsto_sum_nat.sub qBoundary_tendsto_zero

theorem qMixture_density_partial_sum (n R : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range R, qMixtureWeight (n + k) / ((n + k : ℕ) : ℝ)) =
      positiveQWeight n - positiveQWeight (n + R) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, qMixture_density_step (n + R) (by omega)]
    simp only [Nat.add_assoc]
    ring

theorem hasSum_uniform_mixture_marginal (n : ℕ) (hn : 0 < n) :
    HasSum (fun k : ℕ => qMixtureWeight (n + k) / ((n + k : ℕ) : ℝ))
      (positiveQWeight n) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => div_nonneg (qMixtureWeight_nonneg _) (Nat.cast_nonneg _)) _).2
  simp_rw [qMixture_density_partial_sum n _ hn]
  have hw : Tendsto (fun k => positiveQWeight (n + k)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.add_comm] using
      positiveQWeight_summable.tendsto_atTop_zero.comp (Filter.tendsto_add_atTop_nat n)
  simpa only [sub_zero] using tendsto_const_nhds.sub hw

/-- Exact positive difference between the two latent laws. -/
theorem latent_density_difference (n : ℕ) (hn : 0 < n) :
    zetaTwo * qMixtureWeight n - mixtureWeight n =
      (3 * (n : ℝ) + 2) /
        ((n : ℝ) * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  unfold qMixtureWeight mixtureWeight
  field_simp [ne_of_gt zetaTwo_pos]
  ring

/-- Exact remainder in the reverse sharp uniform bound. -/
theorem latent_density_upper_difference (n : ℕ) (hn : 0 < n) :
    (9 / 4 : ℝ) * mixtureWeight n - zetaTwo * qMixtureWeight n =
      (((n : ℝ) - 1) * (5 * (n : ℝ) + 4)) /
        (2 * (n : ℝ) * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  unfold qMixtureWeight mixtureWeight
  field_simp [ne_of_gt zetaTwo_pos]
  ring

theorem latent_weight_comparison (n : ℕ) (hn : 0 < n) :
    (4 / 9 : ℝ) * zetaTwo * qMixtureWeight n ≤ mixtureWeight n ∧
      mixtureWeight n ≤ zetaTwo * qMixtureWeight n := by
  have h1 := latent_density_difference n hn
  have h2 := latent_density_upper_difference n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ (3 * (n : ℝ) + 2) /
      ((n : ℝ) * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by positivity
  have hb : 0 ≤ (((n : ℝ) - 1) * (5 * (n : ℝ) + 4)) /
      (2 * (n : ℝ) * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by positivity
  constructor <;> nlinarith

/-- Exact positive remainder behind the improved comparison after a moving head. -/
theorem latent_density_head_remainder (n : ℕ) (hn : 0 < n) :
    mixtureWeight n =
      ((n : ℝ) / ((n : ℝ) + 2)) * zetaTwo * qMixtureWeight n +
        1 / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  unfold mixtureWeight qMixtureWeight
  field_simp [hn0, hn1, hn2, ne_of_gt zetaTwo_pos]
  ring

theorem latent_weight_lower_of_gt_head (H n : ℕ) (hn : H < n) :
    zetaTwo * (((H : ℝ) + 1) / ((H : ℝ) + 3)) * qMixtureWeight n ≤
      mixtureWeight n := by
  have hHn : H + 1 ≤ n := by omega
  have hHnR : (H : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hHn
  have hratio : ((H : ℝ) + 1) / ((H : ℝ) + 3) ≤
      (n : ℝ) / ((n : ℝ) + 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hratio
    (mul_nonneg zetaTwo_pos.le (qMixtureWeight_nonneg n))
  have he := latent_density_head_remainder n (by omega)
  have hrem : 0 ≤ 1 / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by positivity
  nlinarith


end RiemannResearch.RH.QUniformMixture
