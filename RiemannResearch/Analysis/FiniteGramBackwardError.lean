import RiemannResearch.Analysis.FiniteGramNormalDefect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact backward-error budgets for inexact finite Gram solves

Source: user-requested fourth Ramanujan transfer program, 23 October 2026.
The computed matrix and source are arbitrary. The true defect splits into
solver residual, source error, and Gram action error. The actual inverse-Gram
budget retains all three diagonal terms and all three signed cross terms.
No invertibility, positivity, or symmetry of the computed matrix is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.FiniteGramBackwardError
open FiniteHilbertGram FiniteGramCapacity FiniteHilbertConstraints

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def inverseGramPairing {v : ι → H} (hv : LinearIndependent ℝ v) (b c : ι → ℝ) : ℝ :=
  inner ℝ (minimumVector hv b) (minimumVector hv c)

theorem minimumVector_add_source {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    minimumVector hv (b + c) = minimumVector hv b + minimumVector hv c := by
  simp only [minimumVector, map_add]

theorem inverseGramPairing_symmetric {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) : inverseGramPairing hv b c = inverseGramPairing hv c b :=
  real_inner_comm _ _

theorem inverseGramPairing_add_left {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c d : ι → ℝ) :
    inverseGramPairing hv (b + c) d =
      inverseGramPairing hv b d + inverseGramPairing hv c d := by
  simp only [inverseGramPairing, minimumVector_add_source, inner_add_left]

theorem inverseGramPairing_matrix [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (b c : ι → ℝ) :
    inverseGramPairing hv b c = dotProduct b ((gramMatrix v)⁻¹.mulVec c) := by
  rw [gramMatrix_inverseSource hv]
  unfold inverseGramPairing
  rw [real_inner_comm]
  change inner ℝ (Fintype.linearCombination ℝ v (inverseSource hv c))
    (minimumVector hv b) = _
  rw [inner_synthesis_minimumVector]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem capacity_add_signed {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    capacity hv (b + c) = capacity hv b + capacity hv c + 2 * inverseGramPairing hv b c := by
  simp only [capacity_eq_norm_sq, minimumVector_add_source, norm_add_sq_real,
    inverseGramPairing] <;> ring

theorem capacity_three_signed {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c d : ι → ℝ) :
    capacity hv (b + c + d) =
      capacity hv b + capacity hv c + capacity hv d +
      2 * inverseGramPairing hv b c + 2 * inverseGramPairing hv b d +
      2 * inverseGramPairing hv c d := by
  rw [capacity_add_signed, capacity_add_signed, inverseGramPairing_add_left]
  ring

theorem twice_inverseGramPairing_le {v : ι → H} (hv : LinearIndependent ℝ v)
    (b c : ι → ℝ) :
    2 * inverseGramPairing hv b c ≤ capacity hv b + capacity hv c := by
  have h := sq_nonneg ‖minimumVector hv b - minimumVector hv c‖
  rw [norm_sub_sq_real, ← capacity_eq_norm_sq hv b, ← capacity_eq_norm_sq hv c] at h
  exact (by unfold inverseGramPairing; linarith)

def solverResidual (A : Matrix ι ι ℝ) (b a : ι → ℝ) : ι → ℝ := A.mulVec a - b

def sourceError (v : ι → H) (x : H) (b : ι → ℝ) : ι → ℝ := b - cross v x

def gramActionError (v : ι → H) (A : Matrix ι ι ℝ) (a : ι → ℝ) : ι → ℝ :=
  gram v a - A.mulVec a

/-- Exact backward error, allowing arbitrary computed matrices and inexact solves. -/
theorem normalDefect_decomposition (v : ι → H) (x : H)
    (A : Matrix ι ι ℝ) (b a : ι → ℝ) :
    normalDefect v x a = solverResidual A b a + sourceError v x b + gramActionError v A a := by
  funext i
  simp only [normalDefect, solverResidual, sourceError, gramActionError, Pi.add_apply, Pi.sub_apply]
  ring

def backwardBudget {v : ι → H} (hv : LinearIndependent ℝ v) (x : H)
    (A : Matrix ι ι ℝ) (b a : ι → ℝ) : ℝ :=
  capacity hv (solverResidual A b a) + capacity hv (sourceError v x b) +
    capacity hv (gramActionError v A a) +
    2 * inverseGramPairing hv (solverResidual A b a) (sourceError v x b) +
    2 * inverseGramPairing hv (solverResidual A b a) (gramActionError v A a) +
    2 * inverseGramPairing hv (sourceError v x b) (gramActionError v A a)

def componentBudget {v : ι → H} (hv : LinearIndependent ℝ v) (x : H)
    (A : Matrix ι ι ℝ) (b a : ι → ℝ) : ℝ :=
  capacity hv (solverResidual A b a) + capacity hv (sourceError v x b) +
    capacity hv (gramActionError v A a)

theorem backwardBudget_eq_defectEnergy {v : ι → H} (hv : LinearIndependent ℝ v)
    (x : H) (A : Matrix ι ι ℝ) (b a : ι → ℝ) :
    backwardBudget hv x A b a = defectEnergy hv x a := by
  simpa only [backwardBudget, defectEnergy, normalDefect_decomposition v x A b a] using
    (capacity_three_signed hv (solverResidual A b a) (sourceError v x b)
      (gramActionError v A a)).symm

/-- All six signed terms sum to the exact true excess energy. -/
theorem residual_error_backward_budget {v : ι → H} (hv : LinearIndependent ℝ v)
    (x : H) (A : Matrix ι ι ℝ) (b a : ι → ℝ) :
    ‖x - Fintype.linearCombination ℝ v a‖ ^ 2 =
      ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x)‖ ^ 2 +
        backwardBudget hv x A b a := by
  rw [backwardBudget_eq_defectEnergy]
  exact residual_error_defect_identity hv x a

theorem backwardBudget_nonneg {v : ι → H} (hv : LinearIndependent ℝ v)
    (x : H) (A : Matrix ι ι ℝ) (b a : ι → ℝ) : 0 ≤ backwardBudget hv x A b a := by
  rw [backwardBudget_eq_defectEnergy]
  exact defectEnergy_nonneg hv x a

/-- Individual errors may cancel; only their complete signed sum must vanish. -/
theorem backward_cancellation_optimal_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (x : H) (A : Matrix ι ι ℝ) (b a : ι → ℝ) :
    solverResidual A b a + sourceError v x b + gramActionError v A a = 0 ↔
      a = inverseCoeff hv x := by
  rw [← normalDefect_decomposition]
  exact normalDefect_zero_iff hv x a

/-- A safe separate-error estimate follows only after the exact signed budget. -/
theorem backwardBudget_le_three_components {v : ι → H} (hv : LinearIndependent ℝ v)
    (x : H) (A : Matrix ι ι ℝ) (b a : ι → ℝ) :
    backwardBudget hv x A b a ≤ 3 * componentBudget hv x A b a := by
  have h₁ := twice_inverseGramPairing_le hv (solverResidual A b a) (sourceError v x b)
  have h₂ := twice_inverseGramPairing_le hv (solverResidual A b a) (gramActionError v A a)
  have h₃ := twice_inverseGramPairing_le hv (sourceError v x b) (gramActionError v A a)
  unfold backwardBudget componentBudget
  linarith

/-- Component-error control is valid for moving finite dimensions and arbitrary filters. -/
theorem backwardBudget_tendsto_zero_of_components
    {α : Type*} {l : Filter α} {κ : α → Type*} [∀ i, Fintype (κ i)]
    (v : ∀ i, κ i → H) (hv : ∀ i, LinearIndependent ℝ (v i))
    (x : α → H) (A : ∀ i, Matrix (κ i) (κ i) ℝ)
    (b a : ∀ i, κ i → ℝ)
    (h : Tendsto (fun i => componentBudget (hv i) (x i) (A i) (b i) (a i)) l (𝓝 0)) :
    Tendsto (fun i => backwardBudget (hv i) (x i) (A i) (b i) (a i)) l (𝓝 0) := by
  apply squeeze_zero (fun i => backwardBudget_nonneg (hv i) (x i) (A i) (b i) (a i))
    (fun i => backwardBudget_le_three_components (hv i) (x i) (A i) (b i) (a i))
  simpa only [mul_zero] using h.const_mul 3

end RiemannResearch.Analysis.FiniteGramBackwardError
