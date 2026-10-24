import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact normal-equation defect certificates for arbitrary legal trials

Source: user-requested third Ramanujan transfer program, 23 October 2026.
The defect is measured in the actual inverse Gram form. Every finite trial
vector and every target are allowed; no conditioning estimate is presumed.
Both the Pareto and Q applications retain their own Gram and source moments.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
open FiniteGramCapacity FiniteHilbertConstraints

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The complete normal-equation defect, with sign fixed as Gram times trial minus source. -/
def normalDefect (v : ι → H) (x : H) (a : ι → ℝ) : ι → ℝ :=
  gram v a - cross v x

/-- The exact error excess, in the inverse of the actual complete Gram form. -/
def defectEnergy {v : ι → H} (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) : ℝ :=
  capacity hv (normalDefect v x a)

theorem normalDefect_apply (v : ι → H) (x : H) (a : ι → ℝ) (i : ι) :
    normalDefect v x a i =
      (∑ j, inner ℝ (v i) (v j) * a j) - inner ℝ (v i) x := by
  simp only [normalDefect, Pi.sub_apply, gram_apply, cross]

theorem normalDefect_eq_gram_displacement {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    normalDefect v x a = gram v (a - inverseCoeff hv x) := by
  have hn : gram v (inverseCoeff hv x) = cross v x :=
    funext (inverseCoeff_normal hv x)
  rw [map_sub, hn]
  rfl

theorem inverseSource_normalDefect {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    inverseSource hv (normalDefect v x a) = a - inverseCoeff hv x := by
  rw [normalDefect_eq_gram_displacement hv]
  exact (gramEquiv hv).symm_apply_apply (a - inverseCoeff hv x)

theorem defectEnergy_eq_norm_sq {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    defectEnergy hv x a =
      ‖Fintype.linearCombination ℝ v (a - inverseCoeff hv x)‖ ^ 2 := by
  rw [defectEnergy, capacity_eq_norm_sq]
  change ‖Fintype.linearCombination ℝ v
    (inverseSource hv (normalDefect v x a))‖ ^ 2 = _
  rw [inverseSource_normalDefect]

theorem defectEnergy_nonneg {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    0 ≤ defectEnergy hv x a := capacity_nonneg hv _

/-- No approximate or diagonal Gram replacement is involved in this certificate. -/
theorem residual_error_defect_identity {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    ‖x - Fintype.linearCombination ℝ v a‖ ^ 2 =
      ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x)‖ ^ 2 +
      defectEnergy hv x a := by
  rw [defectEnergy_eq_norm_sq]
  exact residual_completion hv x a

/-- The entire target error is an inverse-Gram source value plus a defect value. -/
theorem residual_error_source_defect {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    ‖x - Fintype.linearCombination ℝ v a‖ ^ 2 =
      ‖x‖ ^ 2 - capacity hv (cross v x) + defectEnergy hv x a := by
  rw [residual_error_defect_identity, residual_schur_value]
  rfl

theorem defectEnergy_zero_iff {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    defectEnergy hv x a = 0 ↔ a = inverseCoeff hv x := by
  rw [defectEnergy_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using h
  · intro h
    simp only [h, sub_self, map_zero]

theorem normalDefect_zero_iff {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    normalDefect v x a = 0 ↔ a = inverseCoeff hv x := by
  rw [normalDefect_eq_gram_displacement hv]
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply gram_injective hv
    simpa only [map_zero] using h
  · intro h
    simp only [h, sub_self, map_zero]

/-- Every simultaneous test direction gives a rigorous lower certificate for the defect. -/
theorem defectEnergy_test_bound {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a b : ι → ℝ) :
    (∑ i, b i * normalDefect v x a i) ^ 2 ≤
      defectEnergy hv x a * ‖Fintype.linearCombination ℝ v b‖ ^ 2 :=
  source_sq_le_capacity_mul_energy hv (normalDefect v x a) b

/-- The dual quadratic certificate retains its complete signed remainder. -/
theorem defectEnergy_dual_completion {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a b : ι → ℝ) :
    2 * (∑ i, b i * normalDefect v x a i) -
        ‖Fintype.linearCombination ℝ v b‖ ^ 2 =
      defectEnergy hv x a -
        ‖Fintype.linearCombination ℝ v (a - inverseCoeff hv x - b)‖ ^ 2 := by
  have h := capacity_completion hv (normalDefect v x a) b
  change _ = defectEnergy hv x a -
    ‖Fintype.linearCombination ℝ v (inverseSource hv (normalDefect v x a)) -
      Fintype.linearCombination ℝ v b‖ ^ 2 at h
  rw [inverseSource_normalDefect, ← map_sub] at h
  exact h

theorem defectEnergy_inverseGram [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (a : ι → ℝ) :
    defectEnergy hv x a = dotProduct (normalDefect v x a)
      ((gramMatrix v)⁻¹.mulVec (normalDefect v x a)) := by
  rw [gramMatrix_inverseSource hv]
  unfold defectEnergy capacity dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

end RiemannResearch.Analysis.FiniteHilbertGram
