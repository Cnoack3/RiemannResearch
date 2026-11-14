import RiemannResearch.Analysis.SignalNormalizationStability
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Exact residual-normalized correction cost

Source: user-provided Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md,
formula (F). Orthogonal projection and SignalNormalizationStability give
an attained minimum and the complete norm-square remainder. A zero
projection is handled as infeasibility, never as a real-valued empty infimum.

The consumer RH/QFullResidualCorrectionCost applies these identities to
actual full-conductor Q projections. Its uniform budget is a conditional
research reduction; no arithmetic correlation estimate is asserted.
-/

open Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ResidualCorrectionCost
open SignalNormalizationStability
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (W : Submodule ℝ H) [W.HasOrthogonalProjection]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem pairing_projection (r w : H) (hw : w ∈ W) :
    ⟪r, w⟫ = ⟪W.starProjection r, w⟫ := by
  have h := Submodule.starProjection_inner_eq_zero r w hw
  rw [inner_sub_left] at h
  exact sub_eq_zero.mp h

/-- The normalized projection of the actual residual is the canonical correction. -/
def optimal (r : H) : H :=
  normalized (W.starProjection r) (W.starProjection r)

theorem optimal_mem (r : H) : optimal W r ∈ W :=
  W.smul_mem _ (W.starProjection_apply_mem r)

theorem optimal_signal (r : H) (hp : W.starProjection r ≠ 0) :
    ⟪r, optimal W r⟫ = 1 := by
  rw [pairing_projection W r _ (optimal_mem W r)]
  exact normalized_signal _ _ (by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hp))

theorem optimal_energy (r : H) (hp : W.starProjection r ≠ 0) :
    ‖optimal W r‖ ^ 2 = 1 / ‖W.starProjection r‖ ^ 2 := by
  have hn := norm_ne_zero_iff.mpr hp
  rw [optimal, normalized_energy, real_inner_self_eq_norm_sq]
  field_simp

/-- Exact cost, including the full nonnegative remainder away from the optimum. -/
theorem cost_completion (r w : H) (hw : w ∈ W) (hs : ⟪r, w⟫ ≠ 0) :
    ‖w‖ ^ 2 / ⟪r, w⟫ ^ 2 =
      1 / ‖W.starProjection r‖ ^ 2 +
        ‖normalized r w - optimal W r‖ ^ 2 := by
  have hp : W.starProjection r ≠ 0 := by
    intro hp
    apply hs
    rw [pairing_projection W r w hw, hp, inner_zero_left]
  have hn : 0 < ‖W.starProjection r‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hp) _
  have hpair := pairing_projection W r w hw
  have he := normalized_pythagoras (W.starProjection r) w hn (hpair ▸ hs)
  rw [normalized_energy] at he
  simpa only [optimal, normalized, ← hpair] using he

/-- The infimum is an attained minimum whenever the residual has a nonzero projection. -/
theorem cost_isLeast (r : H) (hp : W.starProjection r ≠ 0) :
    IsLeast {E : ℝ | ∃ w ∈ W, ⟪r, w⟫ ≠ 0 ∧
      ‖w‖ ^ 2 / ⟪r, w⟫ ^ 2 = E} (1 / ‖W.starProjection r‖ ^ 2) := by
  constructor
  · refine ⟨optimal W r, optimal_mem W r, ?_, ?_⟩
    · rw [optimal_signal W r hp]; norm_num
    · rw [optimal_signal W r hp, one_pow, div_one, optimal_energy W r hp]
  · rintro E ⟨w, hw, hs, rfl⟩
    rw [cost_completion W r w hw hs]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- Zero projection means the set of nonzero-correlation corrections is empty. -/
theorem no_correction_iff (r : H) :
    (¬ ∃ w ∈ W, ⟪r, w⟫ ≠ 0) ↔ W.starProjection r = 0 := by
  constructor
  · intro h
    by_contra hp
    exact h ⟨optimal W r, optimal_mem W r, by
      rw [optimal_signal W r hp]; norm_num⟩
  · rintro hp ⟨w, hw, hs⟩
    apply hs
    rw [pairing_projection W r w hw, hp, inner_zero_left]

/-- A cost budget is exactly a lower bound on the actual projected residual energy. -/
theorem normalized_budget_iff (r : H) (hr : r ≠ 0) (K : ℝ) (hK : 0 < K) :
    (∃ w ∈ W, ⟪r, w⟫ ≠ 0 ∧
      ‖r‖ ^ 2 * (‖w‖ ^ 2 / ⟪r, w⟫ ^ 2) ≤ K) ↔
    ‖r‖ ^ 2 / K ≤ ‖W.starProjection r‖ ^ 2 := by
  have hr2 : 0 < ‖r‖ ^ 2 := pow_pos (norm_pos_iff.mpr hr) _
  constructor
  · rintro ⟨w, hw, hs, hcost⟩
    have hp : W.starProjection r ≠ 0 := by
      intro hp
      exact (no_correction_iff W r).mpr hp ⟨w, hw, hs⟩
    have hp2 : 0 < ‖W.starProjection r‖ ^ 2 := pow_pos (norm_pos_iff.mpr hp) _
    have hl := (cost_isLeast W r hp).2 ⟨w, hw, hs, rfl⟩
    have hb : ‖r‖ ^ 2 / ‖W.starProjection r‖ ^ 2 ≤ K := by
      simpa only [mul_one_div] using (mul_le_mul_of_nonneg_left hl hr2.le).trans hcost
    exact (div_le_iff₀ hK).mpr (by
      simpa only [mul_comm] using (div_le_iff₀ hp2).mp hb)
  · intro hb
    have hp2 : 0 < ‖W.starProjection r‖ ^ 2 :=
      (div_pos hr2 hK).trans_le hb
    have hp : W.starProjection r ≠ 0 := by
      intro h
      simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hp2
      exact lt_irrefl 0 hp2
    refine ⟨optimal W r, optimal_mem W r, ?_, ?_⟩
    · rw [optimal_signal W r hp]; norm_num
    · rw [optimal_signal W r hp, one_pow, div_one, optimal_energy W r hp, mul_one_div]
      apply (div_le_iff₀ hp2).mpr
      simpa only [mul_comm] using (div_le_iff₀ hK).mp hb

theorem logarithmic_budget_iff (r : H) (hr : r ≠ 0)
    (C L : ℝ) (hC : 0 < C) (hL : 1 < L) :
    (∃ w ∈ W, ⟪r, w⟫ ≠ 0 ∧
      ‖r‖ ^ 2 * (‖w‖ ^ 2 / ⟪r, w⟫ ^ 2) ≤ C * Real.log L) ↔
    ‖r‖ ^ 2 / (C * Real.log L) ≤ ‖W.starProjection r‖ ^ 2 :=
  normalized_budget_iff W r hr _ (mul_pos hC (Real.log_pos hL))


/-- A uniform correction budget along any convergent projection approximation
forces the target into the admissible space. This is an abstract implication;
the budget itself must be supplied in each arithmetic application. -/
theorem mem_of_eventual_uniform_budget {α : Type*} (l : Filter α) [l.NeBot]
    (x : H) (v : α → H)
    (hv : ∀ᶠ i in l, v i ∈ W)
    (ht : Filter.Tendsto v l (nhds (W.starProjection x)))
    (K : ℝ) (hK : 0 < K)
    (hbudget : ∀ᶠ i in l, x - v i ≠ 0 →
      ∃ w ∈ W, ⟪x - v i, w⟫ ≠ 0 ∧
        ‖x - v i‖ ^ 2 * (‖w‖ ^ 2 / ⟪x - v i, w⟫ ^ 2) ≤ K) :
    x ∈ W := by
  have hineq : ∀ᶠ i in l,
      ‖x - v i‖ ^ 2 ≤ K * ‖W.starProjection x - v i‖ ^ 2 := by
    refine (hv.and hbudget).mono ?_
    rintro i ⟨hvi, hi⟩
    by_cases hr : x - v i = 0
    · rw [hr, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg hK.le (sq_nonneg _)
    · have h := (normalized_budget_iff W (x - v i) hr K hK).mp (hi hr)
      have hpv : W.starProjection (v i) = v i :=
        Submodule.starProjection_eq_self_iff.mpr hvi
      rw [map_sub, hpv] at h
      simpa only [mul_comm] using (div_le_iff₀ hK).mp h
  have hleft : Filter.Tendsto (fun i => ‖x - v i‖ ^ 2) l
      (nhds (‖x - W.starProjection x‖ ^ 2)) :=
    (tendsto_const_nhds.sub ht).norm.pow 2
  have hright : Filter.Tendsto (fun i => K * ‖W.starProjection x - v i‖ ^ 2)
      l (nhds 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (tendsto_const_nhds.mul ((tendsto_const_nhds.sub ht).norm.pow 2) :
        Filter.Tendsto (fun i => K * ‖W.starProjection x - v i‖ ^ 2) l
          (nhds (K * ‖W.starProjection x - W.starProjection x‖ ^ 2)))
  have hz : ‖x - W.starProjection x‖ ^ 2 = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto hleft hright hineq) (sq_nonneg _)
  have he : W.starProjection x = x :=
    (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm
  exact Submodule.starProjection_eq_self_iff.mp he

end RiemannResearch.Analysis.ResidualCorrectionCost
