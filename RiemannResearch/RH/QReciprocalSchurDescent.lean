import RiemannResearch.RH.QReciprocalFullMinimizer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import RiemannResearch.RH.QReciprocalFiniteCost
import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QResidueTriangular
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Signed direction descent and conductor enlargement

Source: user-requested investigation of inverse-Gram minimizers, 12 November 2026.
The exact Hilbert-space identities retain every signed inner product and every
nonnegative remainder. They quantify finite improvement; they do not assert a
uniform arithmetic lower bound for a Schur gain or a new asymptotic RH provider.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QReciprocalSchurDescent
open ZetaTwoHilbert QReciprocalMetric QReciprocalCostEquivalence
open QReciprocalFiniteCost QReciprocalFullMinimizer
open RiemannResearch.Analysis.FiniteHilbertGram

def directionEnergy (α : ℝ) (w : QHilbert) : ℝ :=
  ‖D w‖^2 + α * ‖w‖^2

def residualPairing (α : ℝ) (x v w : QHilbert) : ℝ :=
  inner ℝ (D (x-v)) (D w) - α * inner ℝ v w

theorem cost_change_regularization (α β : ℝ) (x v : QHilbert) :
    cost α x v = cost β x v + (α-β)*‖v‖^2 := by
  unfold cost
  ring

theorem cost_add_smul (α t : ℝ) (x v w : QHilbert) :
    cost α x (v+t • w) = cost α x v -
      2*t*residualPairing α x v w + t^2*directionEnergy α w := by
  have he : v+t • w-x = (v-x)+t • w := by abel
  have hn : D (x-v) = -D (v-x) := by
    rw [← map_neg]
    congr 1
    abel
  simp only [cost, he, map_add, map_smul, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right,
    residualPairing, directionEnergy, hn, inner_neg_left]
  ring

theorem directionEnergy_pos (α : ℝ) (hα : 0 < α) (w : QHilbert) (hw : w ≠ 0) :
    0 < directionEnergy α w := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold directionEnergy
  positivity

theorem optimized_direction_identity (α : ℝ) (x v w : QHilbert)
    (hs : directionEnergy α w ≠ 0) :
    cost α x (v+(residualPairing α x v w/directionEnergy α w) • w) =
      cost α x v - (residualPairing α x v w)^2/directionEnergy α w := by
  rw [cost_add_smul]
  field_simp
  ring

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem minimizer_direction_bound (a : ι → QHilbert) (ha : LinearIndependent ℝ a)
    (α : ℝ) (hα : 0 < α) (x v w : QHilbert)
    (hv : v ∈ synthesisSpan a) (hw : w ∈ synthesisSpan a)
    (hs : directionEnergy α w ≠ 0) :
    cost α x (minimizer a x α) ≤
      cost α x v - (residualPairing α x v w)^2/directionEnergy α w := by
  rw [← optimized_direction_identity α x v w hs]
  exact minimizer_le a ha x _ ((synthesisSpan a).add_mem hv
    ((synthesisSpan a).smul_mem _ hw)) α hα

theorem nested_parameters_identity (a : ι → QHilbert) (b : κ → QHilbert)
    (hb : LinearIndependent ℝ b) (hab : synthesisSpan a ≤ synthesisSpan b)
    (α β : ℝ) (hβ : 0 < β) (x : QHilbert) :
    cost α x (minimizer a x α) =
      cost β x (minimizer b x β) +
      ‖D (minimizer a x α-minimizer b x β)‖^2 +
      β*‖minimizer a x α-minimizer b x β‖^2 +
      (α-β)*‖minimizer a x α‖^2 := by
  rw [cost_change_regularization α β x]
  rw [cost_completion b hb x (minimizer a x α) (hab (minimizer_mem a x α)) β hβ]

theorem fullSpan_mono (H K : ℕ) (hHK : H ≤ K) :
    synthesisSpan (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) ≤
      synthesisSpan (fun i : Fin K => qResidue (QFullResidueProjection.conductor K i)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨i.val,lt_of_lt_of_le i.isLt hHK⟩,rfl⟩

theorem fullValue_parameters_identity (H K : ℕ) (hHK : H ≤ K)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    fullValue H α = fullValue K β +
      ‖D (fullMinimizer H α-fullMinimizer K β)‖^2 +
      β*‖fullMinimizer H α-fullMinimizer K β‖^2 +
      (α-β)*‖fullMinimizer H α‖^2 := by
  rw [← full_minimum_value H α hα, ← full_minimum_value K β hβ]
  exact nested_parameters_identity _ _
    (QResidueTriangular.qResidue_linearIndependent_injective _
      (QFullResidueProjection.conductor_gt_one K)
      (QFullResidueProjection.conductor_injective K))
    (fullSpan_mono H K hHK) α β hβ qOne

theorem fullValue_nested_gain (H K : ℕ) (hHK : H ≤ K)
    (α : ℝ) (hα : 0 < α) :
    fullValue H α-fullValue K α =
      ‖D (fullMinimizer H α-fullMinimizer K α)‖^2 +
      α*‖fullMinimizer H α-fullMinimizer K α‖^2 := by
  have h := fullValue_parameters_identity H K hHK α α hα hα
  simp only [sub_self, zero_mul, add_zero] at h
  linarith only [h]

theorem fullValue_mono_conductors (H K : ℕ) (hHK : H ≤ K)
    (α : ℝ) (hα : 0 < α) : fullValue K α ≤ fullValue H α := by
  have h := fullValue_nested_gain H K hHK α hα
  nlinarith [sq_nonneg ‖D (fullMinimizer H α-fullMinimizer K α)‖,
    mul_nonneg hα.le (sq_nonneg ‖fullMinimizer H α-fullMinimizer K α‖)]

theorem fullValue_mono_parameters (H K : ℕ) (hHK : H ≤ K)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    fullValue K β ≤ fullValue H α -
      (α-β)*‖fullMinimizer H α‖^2 := by
  have h := fullValue_parameters_identity H K hHK α β hα hβ
  nlinarith [sq_nonneg ‖D (fullMinimizer H α-fullMinimizer K β)‖,
    mul_nonneg hβ.le (sq_nonneg ‖fullMinimizer H α-fullMinimizer K β‖)]


theorem fullValue_regularization_slope (H : ℕ)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (α-β)*‖fullMinimizer H α‖^2 ≤ fullValue H α-fullValue H β ∧
    fullValue H α-fullValue H β ≤ (α-β)*‖fullMinimizer H β‖^2 := by
  have h1 := fullValue_mono_parameters H H le_rfl α β hα hβ
  have h2 := fullValue_mono_parameters H H le_rfl β α hβ hα
  constructor <;> nlinarith only [h1,h2]

theorem fullValue_normalized_mono (H : ℕ)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α) :
    β*fullValue H α ≤ α*fullValue H β := by
  have hu := (fullValue_regularization_slope H α β hα hβ).2
  have hn : β*‖fullMinimizer H β‖^2 ≤ fullValue H β := by
    rw [← full_minimum_value H β hβ]
    unfold cost
    linarith [sq_nonneg ‖D (fullMinimizer H β-qOne)‖]
  have h1 := mul_le_mul_of_nonneg_left hu hβ.le
  have h2 := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hβα)
  nlinarith only [h1,h2]

theorem fullValue_direction_bound (H K : ℕ) (hHK : H ≤ K)
    (α : ℝ) (hα : 0 < α) (w : QHilbert)
    (hw : w ∈ synthesisSpan
      (fun i : Fin K => qResidue (QFullResidueProjection.conductor K i)))
    (hs : directionEnergy α w ≠ 0) :
    fullValue K α ≤ fullValue H α -
      (residualPairing α qOne (fullMinimizer H α) w)^2/directionEnergy α w := by
  rw [← full_minimum_value H α hα, ← full_minimum_value K α hα]
  exact minimizer_direction_bound _
    (QResidueTriangular.qResidue_linearIndependent_injective _
      (QFullResidueProjection.conductor_gt_one K)
      (QFullResidueProjection.conductor_injective K))
    α hα qOne (fullMinimizer H α) w
    (fullSpan_mono H K hHK (minimizer_mem _ qOne α)) hw hs

end RiemannResearch.RH.QReciprocalSchurDescent
