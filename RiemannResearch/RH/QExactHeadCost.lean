import RiemannResearch.RH.QReciprocalCostEquivalence

/-!
# Complete reciprocal cost of an exact physical head

Source: the complete-cost continuation of the November 11 density manuscript.
Physical errors vanish through H, so the reciprocal multiplier costs at most
1/(H+1) on the entire remaining tail. The signed inner product is retained.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QExactHeadCost
open ZetaTwoHilbert QReciprocalMetric QReciprocalCostEquivalence

theorem D_norm_sq_le_of_head_zero (H : ℕ) (f : QHilbert)
    (hz : ∀ n ≤ H, qSequence f n = 0) :
    ‖D f‖ ^ 2 ≤ ‖f‖ ^ 2 / ((H : ℝ) + 1) ^ 2 := by
  rw [qNorm_sq, qNorm_sq, ← tsum_div_const]
  apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
    ((qCoordinate_square_summable f).div_const _)
  intro n
  rw [D_apply, div_pow]
  by_cases hn : n < H
  · have he := hz (n+1) (by omega)
    rw [qSequence_succ, div_eq_zero_iff] at he
    have hfn : f n = 0 := he.resolve_right (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))
    simp [hfn]
  · have hdn : (H : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast (show H+1 ≤ n+1 by omega)
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ (by positivity) hdn 2)

theorem cost_le_of_exact_head (H : ℕ) (v : QHilbert)
    (hh : ∀ n ≤ H, qSequence v n = qSequence qOne n) (α : ℝ) :
    cost α qOne v ≤ ‖v - qOne‖ ^ 2 / ((H : ℝ)+1)^2 + α*‖v‖ ^ 2 := by
  apply add_le_add _ le_rfl
  apply D_norm_sq_le_of_head_zero
  intro n hn
  change qSequenceLinear (v-qOne) n = 0
  simp only [map_sub, Pi.sub_apply]
  exact sub_eq_zero.mpr (hh n hn)

theorem cost_le_signed_of_exact_head (H : ℕ) (v : QHilbert)
    (hh : ∀ n ≤ H, qSequence v n = qSequence qOne n) (α : ℝ) :
    cost α qOne v ≤
      (‖v‖ ^ 2 + 1 - 2*inner ℝ v qOne) / ((H : ℝ)+1)^2 + α*‖v‖ ^ 2 := by
  have he : ‖v-qOne‖ ^ 2 = ‖v‖ ^ 2 + 1 - 2*inner ℝ v qOne := by
    have he := norm_sub_sq_real v qOne
    rw [qOne_norm_sq] at he
    linarith
  simpa only [he] using cost_le_of_exact_head H v hh α

end RiemannResearch.RH.QExactHeadCost
