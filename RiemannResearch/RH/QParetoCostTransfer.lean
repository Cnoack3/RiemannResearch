import Mathlib.Tactic.LinearCombination
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QReciprocalCostEquivalence

/-!
# Physical P/Q transfer of complete regularized costs

The same physical sequences are compared in the two equivalent Hilbert norms. The positive metric correction is retained; this does not identify P and Q orthogonal projections.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
namespace RiemannResearch.RH.QParetoCostTransfer
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoMetric QReciprocalMetric QReciprocalCostEquivalence

theorem toPareto_D (f : QHilbert) :
    toPareto (D f) = reciprocalD (toPareto f) := by
  apply Subtype.ext
  funext n
  change Real.sqrt (paretoWeight n) * qSequence (D f) (n+1) =
    (Real.sqrt (paretoWeight n) * qSequence f (n+1)) / ((n : ℝ)+1)
  rw [qSequence_D]
  push_cast
  ring

def paretoCost (α : ℝ) (x v : QHilbert) : ℝ :=
  ‖toPareto (D (v-x))‖ ^ 2 + α*‖toPareto v‖ ^ 2

theorem paretoCost_physical (α : ℝ) (x v : QHilbert) :
    paretoCost α x v =
      ‖reciprocalD (toPareto v-toPareto x)‖ ^ 2 + α*‖toPareto v‖ ^ 2 := by
  rw [paretoCost, toPareto_D]
  change ‖reciprocalD (toParetoLinear (v-x))‖ ^ 2 + _ = _
  rw [map_sub]
  rfl

theorem cost_identity (α : ℝ) (x v : QHilbert) :
    zetaTwo*cost α x v = paretoCost α x v +
      metricCorrection (D (v-x)) + α*metricCorrection v := by
  have he := norm_identity (D (v-x))
  have hv := norm_identity v
  unfold cost paretoCost
  linear_combination he + α*hv

theorem paretoCost_le_scaled_cost (α : ℝ) (hα : 0 ≤ α) (x v : QHilbert) :
    paretoCost α x v ≤ zetaTwo*cost α x v := by
  rw [cost_identity]
  have h1 := metricCorrection_nonneg (D (v-x))
  have h2 := mul_nonneg hα (metricCorrection_nonneg v)
  linarith

theorem scaled_cost_le_twice_paretoCost (α : ℝ) (hα : 0 ≤ α) (x v : QHilbert) :
    zetaTwo*cost α x v ≤ 2*paretoCost α x v := by
  have he := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (D (v-x))
  have hv := mul_le_mul_of_nonneg_left
    (zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq v) hα
  unfold cost paretoCost
  nlinarith only [he,hv]

theorem cofinal_cost_bound_iff (α : ℕ → ℝ) (hα : ∀ j, 0 ≤ α j)
    (x : QHilbert) (F : ℕ → QHilbert) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N, ∃ j, N ≤ j ∧ cost (α j) x (F j) ≤ C*α j) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N, ∃ j, N ≤ j ∧ paretoCost (α j) x (F j) ≤ C*α j) := by
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨zetaTwo*C,mul_nonneg zetaTwo_pos.le hC,fun N => ?_⟩
    obtain ⟨j,hj,hb⟩ := h N
    refine ⟨j,hj,?_⟩
    have hu := mul_le_mul_of_nonneg_left hb zetaTwo_pos.le
    have hl := paretoCost_le_scaled_cost (α j) (hα j) x (F j)
    nlinarith only [hu,hl]
  · rintro ⟨C,hC,h⟩
    refine ⟨2*C/zetaTwo,by positivity [zetaTwo_pos],fun N => ?_⟩
    obtain ⟨j,hj,hb⟩ := h N
    refine ⟨j,hj,?_⟩
    have hu := scaled_cost_le_twice_paretoCost (α j) (hα j) x (F j)
    have hcost : cost (α j) x (F j) ≤ (2*C*α j)/zetaTwo :=
      (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith only [hu,hb])
    convert hcost using 1; ring

end RiemannResearch.RH.QParetoCostTransfer
