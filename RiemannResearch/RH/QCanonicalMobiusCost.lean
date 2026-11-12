import RiemannResearch.RH.ParetoExactHeadEnergy
import RiemannResearch.RH.QExactHeadCost
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.CanonicalMobiusQuantitativeEnergy

/-!
# Explicit Mobius legal-family complete cost

Source: the complete-cost continuation of the November 11 density manuscript.
Reuses QMobiusExactHead.exactHead, including its boundary conductor H+1.
The cost is bounded above and below by fixed multiples of H^-2 times the
complete Pareto source energy. PNT gives o(H^-1), not a near-linear cost.
The fixed stage H=(j+1)^2 matches regularizationScale j exactly.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QCanonicalMobiusCost
open Pareto ZetaTwoHilbert ZetaTwoProbability QParetoEquivalence
open QReciprocalMetric QReciprocalCostEquivalence QExactHeadCost

open QMobiusExactHead

theorem exactHead_eq_toQ (H : ℕ) :
    exactHead H = toQ (canonicalMobiusHilbert H) := by
  apply qSequence_injective
  rw [exactHead_sequence, toQ_sequence, canonicalMobiusHilbert_sequence]

theorem exactHead_matches_one (H n : ℕ) (hn : n ≤ H) :
    qSequence (exactHead H) n = qSequence qOne n := by
  by_cases hn0 : n = 0
  · simp [hn0]
  rw [exactHead_exact H n (by omega) hn, qSequence_qOne,
    qOneSequence, if_neg hn0]

theorem exactHead_norm_sq_le (H : ℕ) :
    ‖exactHead H‖ ^ 2 ≤ (2 / zetaTwo) * ‖canonicalMobiusHilbert H‖ ^ 2 :=
  by rw [exactHead_eq_toQ]; exact toQ_norm_sq_le _

theorem exactHead_error_norm_sq_le (H : ℕ) :
    ‖exactHead H-qOne‖ ^ 2 ≤ (2 / zetaTwo) * ‖canonicalMobiusHilbert H-hilbertOne‖ ^ 2 := by
  have he : exactHead H-qOne = toQ (canonicalMobiusHilbert H-hilbertOne) := by
    change exactHead H-qOne = toQLinear (_-_)
    rw [map_sub]
    change exactHead H-qOne = toQ (canonicalMobiusHilbert H)-toQ hilbertOne
    rw [exactHead_eq_toQ, toQ_hilbertOne]
  rw [he]
  exact toQ_norm_sq_le _

theorem complete_cost_bound (H : ℕ) (α : ℝ) (hα : 0 ≤ α) :
    cost α qOne (exactHead H) ≤ (2 / zetaTwo) *
      (‖canonicalMobiusHilbert H-hilbertOne‖ ^ 2 / ((H : ℝ)+1)^2 +
        α*‖canonicalMobiusHilbert H‖ ^ 2) := by
  calc
    _ ≤ ‖exactHead H-qOne‖ ^ 2 / ((H : ℝ)+1)^2 + α*‖exactHead H‖ ^ 2 :=
      cost_le_of_exact_head H _ (fun n hn => exactHead_matches_one H n hn) α
    _ ≤ ((2 / zetaTwo) * ‖canonicalMobiusHilbert H-hilbertOne‖ ^ 2) /
        ((H : ℝ)+1)^2 + α*((2 / zetaTwo)*‖canonicalMobiusHilbert H‖ ^ 2) :=
      add_le_add (div_le_div_of_nonneg_right (exactHead_error_norm_sq_le H) (by positivity))
        (mul_le_mul_of_nonneg_left (exactHead_norm_sq_le H) hα)
    _ = _ := by ring

theorem exactHead_pareto_error_sharp (H : ℕ) (hH : 0 < H) :
    ‖canonicalMobiusHilbert H-hilbertOne‖ ^ 2 ≤
      (((H : ℝ)+1)/(H : ℝ))*‖canonicalMobiusHilbert H‖ ^ 2 := by
  apply ParetoExactHeadEnergy.error_norm_sq_le H hH
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · rw [canonicalMobiusHilbert_exact H n (by omega) hn, hilbertOne_sequence]
    simp [zeroAnchor, hn0]

theorem complete_cost_source_bound (H : ℕ) (hH : 0 < H)
    (α : ℝ) (hα : 0 ≤ α) :
    cost α qOne (exactHead H) ≤
      (2 / zetaTwo) * (α + 1 / ((H : ℝ)*((H : ℝ)+1))) *
        ‖canonicalMobiusHilbert H‖ ^ 2 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ (2 / zetaTwo) *
        (‖canonicalMobiusHilbert H-hilbertOne‖ ^ 2 / ((H : ℝ)+1)^2 +
          α*‖canonicalMobiusHilbert H‖ ^ 2) := complete_cost_bound H α hα
    _ ≤ (2 / zetaTwo) *
        (((((H : ℝ)+1)/(H : ℝ))*‖canonicalMobiusHilbert H‖ ^ 2) /
          ((H : ℝ)+1)^2 + α*‖canonicalMobiusHilbert H‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_right (exactHead_pareto_error_sharp H hH) (by positivity))
        le_rfl) (by positivity [zetaTwo_pos])
    _ = _ := by field_simp; ring

theorem balanced_cost_source_upper (H : ℕ) (hH : 0 < H) :
    cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) ≤
      (4 / zetaTwo) * ((H : ℝ)^2)⁻¹ * ‖canonicalMobiusHilbert H‖ ^ 2 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hi : 1/((H : ℝ)*((H : ℝ)+1)) ≤ ((H : ℝ)^2)⁻¹ := by
    rw [← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  calc
    _ ≤ (2 / zetaTwo) * (((H : ℝ)^2)⁻¹+1/((H : ℝ)*((H : ℝ)+1))) *
        ‖canonicalMobiusHilbert H‖ ^ 2 := complete_cost_source_bound H hH _ (by positivity)
    _ ≤ (2 / zetaTwo) * (((H : ℝ)^2)⁻¹+((H : ℝ)^2)⁻¹) *
        ‖canonicalMobiusHilbert H‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl hi)
        (by positivity [zetaTwo_pos])) (sq_nonneg _)
    _ = _ := by ring

theorem balanced_cost_source_lower (H : ℕ) :
    ((H : ℝ)^2)⁻¹ * ‖canonicalMobiusHilbert H‖ ^ 2 / zetaTwo ≤
      cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) := by
  have hp := ZetaTwoParetoTransfer.toPareto_norm_sq_le (exactHead H)
  rw [exactHead_eq_toQ, toPareto_toQ] at hp
  rw [← exactHead_eq_toQ] at hp
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ ((H : ℝ)^2)⁻¹ by positivity)
  apply (div_le_iff₀ zetaTwo_pos).mpr
  unfold cost
  nlinarith [mul_nonneg zetaTwo_pos.le (sq_nonneg ‖D (exactHead H-qOne)‖)]

theorem balanced_cost_explicit (H : ℕ) (hH : 0 < H) :
    cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) ≤ 16/(zetaTwo*(H : ℝ)) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ (4 / zetaTwo) * ((H : ℝ)^2)⁻¹ * ‖canonicalMobiusHilbert H‖ ^ 2 :=
      balanced_cost_source_upper H hH
    _ ≤ (4 / zetaTwo) * ((H : ℝ)^2)⁻¹ * (4*(H : ℝ)) :=
      mul_le_mul_of_nonneg_left (canonicalMobiusHilbert_norm_sq_lt_four_mul H hH).le
        (by positivity [zetaTwo_pos])
    _ = _ := by field_simp; ring

theorem balanced_cost_eventual_log_ceiling :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop,
      (H : ℝ) * cost ((H : ℝ)^2)⁻¹ qOne (exactHead H) ≤
        (4 / zetaTwo) * canonicalMobiusEnergyCeiling C H := by
  obtain ⟨C,hC,hE⟩ := canonicalMobiusHilbert_eventual_optimized_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hE, eventually_ge_atTop (1 : ℕ)] with H he hH
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ (H : ℝ) * ((4 / zetaTwo) * ((H : ℝ)^2)⁻¹ * ‖canonicalMobiusHilbert H‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (balanced_cost_source_upper H hH) hHR.le
    _ = (4 / zetaTwo)*(‖canonicalMobiusHilbert H‖ ^ 2/(H : ℝ)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity [zetaTwo_pos])

theorem balanced_cost_little_o :
    Tendsto (fun H : ℕ => (H : ℝ) * cost ((H : ℝ)^2)⁻¹ qOne (exactHead H))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun H : ℕ => (4 / zetaTwo) *
      (‖canonicalMobiusHilbert H‖ ^ 2 / (H : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using canonicalMobiusHilbert_sublinear.const_mul (4 / zetaTwo)
  apply squeeze_zero' _ _ hu
  · exact Eventually.of_forall (fun H => by unfold cost; positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
    have hHR : (0 : ℝ) < H := by exact_mod_cast hH
    calc
      _ ≤ (H : ℝ) * ((4 / zetaTwo) * ((H : ℝ)^2)⁻¹ * ‖canonicalMobiusHilbert H‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (balanced_cost_source_upper H hH) hHR.le
      _ = _ := by field_simp

def stage (j : ℕ) : ℕ := (j+1)^2
def legalFamily (j : ℕ) : QHilbert := exactHead (stage j)

theorem stage_pos (j : ℕ) : 0 < stage j := by unfold stage; positivity

theorem stage_tendsto : Tendsto stage atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  change j ≤ (j+1)^2
  nlinarith

theorem regularizationScale_eq (j : ℕ) :
    QReciprocalRegularizedCriterion.regularizationScale j =
      ((stage j : ℝ)^2)⁻¹ := by
  unfold QReciprocalRegularizedCriterion.regularizationScale stage
  rw [Real.rpow_neg (by positivity)]
  norm_num only [Real.rpow_ofNat]
  push_cast
  congr 1
  ring

theorem legalFamily_legal (j : ℕ) :
    legalFamily j ∈ QFullResidueProjection.legalSpan := exactHead_mem_legalSpan _

theorem legalFamily_complete_cost (j : ℕ) :
    cost (QReciprocalRegularizedCriterion.regularizationScale j) qOne (legalFamily j) ≤
      16 / (zetaTwo * ((j : ℝ)+1)^2) := by
  rw [regularizationScale_eq]
  simpa only [legalFamily, stage, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    balanced_cost_explicit (stage j) (stage_pos j)

theorem legalFamily_complete_cost_little_o :
    Tendsto (fun j : ℕ => ((j : ℝ)+1)^2 *
      cost (QReciprocalRegularizedCriterion.regularizationScale j) qOne (legalFamily j))
      atTop (𝓝 0) := by
  simpa only [Function.comp_def, legalFamily, regularizationScale_eq,
    stage, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    balanced_cost_little_o.comp stage_tendsto

theorem legalFamily_half_loss_bound (η : ℝ) (hη : (1 / 2 : ℝ) ≤ η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      cost (QReciprocalRegularizedCriterion.regularizationScale j) qOne (legalFamily j) ≤
        C * (QReciprocalRegularizedCriterion.regularizationScale j)^(1-η) := by
  refine ⟨16/zetaTwo, by positivity [zetaTwo_pos], ?_⟩
  intro j
  have hx : 0 < (j : ℝ)+1 := by positivity
  have hx1 : 1 ≤ (j : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hp : ((j : ℝ)+1)^(-2 : ℝ) ≤
      (QReciprocalRegularizedCriterion.regularizationScale j)^(1-η) := by
    unfold QReciprocalRegularizedCriterion.regularizationScale
    rw [← Real.rpow_mul hx.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    nlinarith
  calc
    _ ≤ 16/(zetaTwo*((j : ℝ)+1)^2) := legalFamily_complete_cost j
    _ = (16/zetaTwo)*((j : ℝ)+1)^(-2 : ℝ) := by
      rw [Real.rpow_neg hx.le, Real.rpow_two]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity [zetaTwo_pos])

end RiemannResearch.RH.QCanonicalMobiusCost
