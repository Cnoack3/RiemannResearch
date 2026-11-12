import RiemannResearch.RH.QCanonicalMobiusCost

/-!
# Exact arithmetic obligation for the explicit legal family

Source: the complete-cost continuation of the November 11 density manuscript.
For this one fixed family, near-linear complete cost is equivalent to subpower
complete source energy and implies Mathlib's RiemannHypothesis. Neither side
of this equivalence is asserted unconditionally. No converse from RH to this
particular family's energy estimate is claimed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QCanonicalMobiusCost
open Pareto ZetaTwoHilbert ZetaTwoProbability QParetoEquivalence
open QReciprocalMetric QReciprocalCostEquivalence QExactHeadCost QMobiusExactHead

open QReciprocalRegularizedCriterion

theorem near_linear_cost_iff_subpower_energy :
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      cost (regularizationScale j) qOne (legalFamily j) ≤
        C * (regularizationScale j)^(1-η)) ↔
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      ‖canonicalMobiusHilbert (stage j)‖ ^ 2 ≤
        C * (regularizationScale j)^(-η)) := by
  have hp (j : ℕ) (η : ℝ) :
      (regularizationScale j)^(1-η) =
        regularizationScale j * (regularizationScale j)^(-η) := by
    rw [sub_eq_add_neg, Real.rpow_add (regularizationScale_pos j), Real.rpow_one]
  constructor
  · intro hc η hη
    obtain ⟨C,hC,hCj⟩ := hc η hη
    refine ⟨zetaTwo*C, mul_nonneg zetaTwo_pos.le hC, ?_⟩
    intro j
    have hlo := balanced_cost_source_lower (stage j)
    rw [← regularizationScale_eq j] at hlo
    change regularizationScale j * ‖canonicalMobiusHilbert (stage j)‖ ^ 2 / zetaTwo ≤
      cost (regularizationScale j) qOne (legalFamily j) at hlo
    have h := hlo.trans (hCj j)
    have h' := (div_le_iff₀ zetaTwo_pos).mp h
    rw [hp] at h'
    apply (mul_le_mul_iff_left₀ (regularizationScale_pos j)).mp
    nlinarith only [h']
  · intro he η hη
    obtain ⟨C,hC,hCj⟩ := he η hη
    refine ⟨(4/zetaTwo)*C, by positivity [zetaTwo_pos], ?_⟩
    intro j
    have hu := balanced_cost_source_upper (stage j) (stage_pos j)
    rw [← regularizationScale_eq j] at hu
    change cost (regularizationScale j) qOne (legalFamily j) ≤
      (4/zetaTwo)*regularizationScale j * ‖canonicalMobiusHilbert (stage j)‖ ^ 2 at hu
    calc
      _ ≤ (4/zetaTwo)*regularizationScale j *
          ‖canonicalMobiusHilbert (stage j)‖ ^ 2 := hu
      _ ≤ (4/zetaTwo)*regularizationScale j *
          (C*(regularizationScale j)^(-η)) :=
        mul_le_mul_of_nonneg_left (hCj j) (by positivity [zetaTwo_pos, regularizationScale_pos j])
      _ = _ := by rw [hp]; ring

/-- The source-energy condition is open; legality and all analytic steps are proved. -/
theorem riemannHypothesis_of_subpower_energy
    (he : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      ‖canonicalMobiusHilbert (stage j)‖ ^ 2 ≤
        C * (regularizationScale j)^(-η)) : RiemannHypothesis := by
  have hc := near_linear_cost_iff_subpower_energy.mpr he
  apply riemannHypothesis_of_near_linear_D_cost legalFamily legalFamily_legal
  intro η hη
  obtain ⟨C,hC,hj⟩ := hc η hη
  refine ⟨C,hC,?_⟩
  intro j
  simpa only [cost, map_sub, norm_sub_rev] using hj j

end RiemannResearch.RH.QCanonicalMobiusCost
