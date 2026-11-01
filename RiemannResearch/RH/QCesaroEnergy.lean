import RiemannResearch.RH.QUniformMixture
import RiemannResearch.RH.ConditionalMeanEnergy
import RiemannResearch.Analysis.CesaroWeightedContraction
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Complete Cesàro energies under the two latent laws

Source: user's 1 November 2026 P/Q question. The exact finite Abel identity
and the complete change-of-measure defect precede their positive estimates.
The averaging operator is unchanged, while its output measure is the latent
endpoint law, not the input marginal.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCesaroEnergy
open QUniformMixture ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative
open Pareto Analysis.Cesaro Probability.ConditionalIID

def qConditionalMeanSquare (F : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2

theorem qConditionalMeanSquare_nonneg (F : ℕ → ℝ) : 0 ≤ qConditionalMeanSquare F :=
  tsum_nonneg (fun _ => mul_nonneg (qMixtureWeight_nonneg _) (sq_nonneg _))

/-- Abel summation keeps the entire nonnegative endpoint contribution. -/
theorem q_cesaro_square_majorant_abel (F : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, qMixtureWeight (k + 1) / ((k + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (k + 1), F (j + 1) ^ 2) =
      (∑ k ∈ Finset.range N, positiveQWeight (k + 1) * F (k + 1) ^ 2) -
        positiveQWeight (N + 1) * ∑ j ∈ Finset.range N, F (j + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      qMixture_density_step (N + 1) (by omega), Finset.sum_range_succ]
    ring

/-- Exact input energy = mean energy + Jensen deficits + endpoint remainder. -/
theorem q_cesaro_energy_prefix_exact (F : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, positiveQWeight (k + 1) * F (k + 1) ^ 2) =
      (∑ k ∈ Finset.range N, qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) +
      (∑ k ∈ Finset.range N, qMixtureWeight (k + 1) *
        ((∑ j ∈ Finset.range (k + 1), F (j + 1) ^ 2) / ((k + 1 : ℕ) : ℝ) -
          cesaro F (k + 1) ^ 2)) +
      positiveQWeight (N + 1) * ∑ j ∈ Finset.range N, F (j + 1) ^ 2 := by
  have h := q_cesaro_square_majorant_abel F N
  have he :
      (∑ k ∈ Finset.range N, qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) +
      (∑ k ∈ Finset.range N, qMixtureWeight (k + 1) *
        ((∑ j ∈ Finset.range (k + 1), F (j + 1) ^ 2) / ((k + 1 : ℕ) : ℝ) -
          cesaro F (k + 1) ^ 2)) =
      ∑ k ∈ Finset.range N, qMixtureWeight (k + 1) / ((k + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (k + 1), F (j + 1) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, h]
  ring

theorem q_cesaro_energy_prefix_le (F : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) ≤
      ∑ k ∈ Finset.range N, positiveQWeight (k + 1) * F (k + 1) ^ 2 := by
  rw [q_cesaro_energy_prefix_exact F N]
  have hd : 0 ≤ ∑ k ∈ Finset.range N, qMixtureWeight (k + 1) *
      ((∑ j ∈ Finset.range (k + 1), F (j + 1) ^ 2) / ((k + 1 : ℕ) : ℝ) -
        cesaro F (k + 1) ^ 2) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (qMixtureWeight_nonneg _)
      (sub_nonneg.mpr (cesaro_square_le_average_square F (k + 1) (by omega)))
  have hb : 0 ≤ positiveQWeight (N + 1) *
      ∑ j ∈ Finset.range N, F (j + 1) ^ 2 :=
    mul_nonneg (positiveQWeight_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  linarith

theorem q_cesaro_weighted_square_summable (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => positiveQWeight (k + 1) * F (k + 1) ^ 2)) :
    Summable (fun k : ℕ => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) := by
  apply summable_of_sum_range_le
    (fun k => mul_nonneg (qMixtureWeight_nonneg _) (sq_nonneg _))
    (c := ∑' k : ℕ, positiveQWeight (k + 1) * F (k + 1) ^ 2)
  intro N
  exact (q_cesaro_energy_prefix_le F N).trans
    (hF.sum_le_tsum (Finset.range N)
      (fun k hk => mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _)))

theorem q_cesaro_weighted_energy_le (F : ℕ → ℝ)
    (hF : Summable (fun k : ℕ => positiveQWeight (k + 1) * F (k + 1) ^ 2)) :
    qConditionalMeanSquare F ≤
      ∑' k : ℕ, positiveQWeight (k + 1) * F (k + 1) ^ 2 := by
  apply le_of_tendsto (q_cesaro_weighted_square_summable F hF).hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall (fun N => (q_cesaro_energy_prefix_le F N).trans
    (hF.sum_le_tsum (Finset.range N)
      (fun k hk => mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))))

theorem qMixtureWeight_le_mul_mixtureWeight (n : ℕ) (hn : 0 < n) :
    qMixtureWeight n ≤ (9 / (4 * zetaTwo)) * mixtureWeight n := by
  by_contra hlt
  have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hlt) zetaTwo_pos
  have he : zetaTwo * ((9 / (4 * zetaTwo)) * mixtureWeight n) =
      (9 / 4 : ℝ) * mixtureWeight n := by
    field_simp [ne_of_gt zetaTwo_pos]
  rw [he] at hmul
  have h := (latent_weight_comparison n hn).1
  nlinarith

/-- Both complete smoothed energies have precisely the same summability domain. -/
theorem conditionalMean_summable_iff (F : ℕ → ℝ) :
    Summable (fun k : ℕ => conditionalWeight k * cesaro F (k + 1) ^ 2) ↔
      Summable (fun k : ℕ => qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) := by
  constructor
  · intro hp
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (qMixtureWeight_nonneg _) (sq_nonneg _)) _
      (hp.mul_left (9 / (4 * zetaTwo)))
    intro k
    simpa only [conditionalWeight, mul_assoc] using
      mul_le_mul_of_nonneg_right (qMixtureWeight_le_mul_mixtureWeight (k + 1) (by omega))
        (sq_nonneg (cesaro F (k + 1)))
  · intro hq
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _)) _
      (hq.mul_left zetaTwo)
    intro k
    simpa only [conditionalWeight, mul_assoc] using
      mul_le_mul_of_nonneg_right (latent_weight_comparison (k + 1) (by omega)).2
        (sq_nonneg (cesaro F (k + 1)))

/-- Exact full-energy change of measure, retaining the positive rational defect. -/
theorem conditionalMean_change_measure_exact (F : ℕ → ℝ)
    (hp : Summable (fun k : ℕ => conditionalWeight k * cesaro F (k + 1) ^ 2)) :
    zetaTwo * qConditionalMeanSquare F = conditionalMeanSquare F +
      ∑' k : ℕ, ((3 * ((k + 1 : ℕ) : ℝ) + 2) /
        (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 *
          (((k + 1 : ℕ) : ℝ) + 2))) * cesaro F (k + 1) ^ 2 := by
  have hq := (conditionalMean_summable_iff F).mp hp
  have he : (fun k : ℕ => ((3 * ((k + 1 : ℕ) : ℝ) + 2) /
        (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) ^ 2 *
          (((k + 1 : ℕ) : ℝ) + 2))) * cesaro F (k + 1) ^ 2) =
      (fun k => zetaTwo * (qMixtureWeight (k + 1) * cesaro F (k + 1) ^ 2) -
        conditionalWeight k * cesaro F (k + 1) ^ 2) := by
    funext k
    rw [← latent_density_difference (k + 1) (by omega)]
    unfold conditionalWeight
    ring
  rw [he, (hq.mul_left zetaTwo).tsum_sub hp, tsum_mul_left]
  unfold qConditionalMeanSquare conditionalMeanSquare
  ring

theorem conditionalMean_measure_comparison (F : ℕ → ℝ)
    (hp : Summable (fun k : ℕ => conditionalWeight k * cesaro F (k + 1) ^ 2)) :
    (4 / 9 : ℝ) * zetaTwo * qConditionalMeanSquare F ≤ conditionalMeanSquare F ∧
      conditionalMeanSquare F ≤ zetaTwo * qConditionalMeanSquare F := by
  have hq := (conditionalMean_summable_iff F).mp hp
  constructor
  · have h := (hq.mul_left ((4 / 9 : ℝ) * zetaTwo)).tsum_le_tsum
      (fun k => by
        simpa only [conditionalWeight, mul_assoc] using
          mul_le_mul_of_nonneg_right (latent_weight_comparison (k + 1) (by omega)).1
            (sq_nonneg (cesaro F (k + 1)))) hp
    simpa only [tsum_mul_left, qConditionalMeanSquare, conditionalMeanSquare] using h
  · have h := hp.tsum_le_tsum
      (fun k => by
        simpa only [conditionalWeight, mul_assoc] using
          mul_le_mul_of_nonneg_right (latent_weight_comparison (k + 1) (by omega)).2
            (sq_nonneg (cesaro F (k + 1)))) (hq.mul_left zetaTwo)
    simpa only [tsum_mul_left, qConditionalMeanSquare, conditionalMeanSquare] using h

/-- On a zero Cesàro head, the complete latent metric ratio tends uniformly to
the common limiting factor ζ(2). All tail coordinates remain in the sums. -/
theorem conditionalMean_measure_comparison_of_head_zero (F : ℕ → ℝ) (H : ℕ)
    (hp : Summable (fun k : ℕ => conditionalWeight k * cesaro F (k + 1) ^ 2))
    (hhead : ∀ n, 0 < n → n ≤ H → cesaro F n = 0) :
    zetaTwo * (((H : ℝ) + 1) / ((H : ℝ) + 3)) * qConditionalMeanSquare F ≤
      conditionalMeanSquare F ∧
      conditionalMeanSquare F ≤ zetaTwo * qConditionalMeanSquare F := by
  have hq := (conditionalMean_summable_iff F).mp hp
  constructor
  · have h := (hq.mul_left (zetaTwo * (((H : ℝ) + 1) / ((H : ℝ) + 3)))).tsum_le_tsum
      (fun k => by
        by_cases hk : k + 1 ≤ H
        · simp [hhead (k + 1) (Nat.succ_pos k) hk]
        · simpa only [conditionalWeight, mul_assoc] using
            mul_le_mul_of_nonneg_right
              (latent_weight_lower_of_gt_head H (k + 1) (by omega))
              (sq_nonneg (cesaro F (k + 1)))) hp
    simpa only [tsum_mul_left, qConditionalMeanSquare, conditionalMeanSquare] using h
  · exact (conditionalMean_measure_comparison F hp).2


end RiemannResearch.RH.QCesaroEnergy
