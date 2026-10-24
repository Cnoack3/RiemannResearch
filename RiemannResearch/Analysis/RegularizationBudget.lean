import RiemannResearch.Analysis.FiniteRegularizedConstraints
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Exact canonical budgets for soft regularization

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The complete canonical observation defect splits into the soft cost and
two further nonnegative energies. A centered square improves the physical
bias estimate to one quarter of the canonical weighted defect budget.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.RegularizationBudget
open FiniteHilbertGram FiniteRegularizedConstraints
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def biasEnergy {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) : ℝ :=
  ‖Fintype.linearCombination ℝ v (coefficients hv B f t ρ - inverseCoeff hv f)‖ ^ 2

def softCost {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) : ℝ :=
  biasEnergy hv B f t ρ + ρ ^ 2 * mismatchEnergy B t (coefficients hv B f t ρ)

def canonicalBudget {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) : ℝ :=
  ρ ^ 2 * mismatchEnergy B t (inverseCoeff hv f)

theorem softCost_nonneg {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    0 ≤ softCost hv B f t ρ :=
  add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (mismatchEnergy_nonneg _ _ _))

theorem minimum_decomposition {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    objective v B f t ρ (coefficients hv B f t ρ) =
      ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 + softCost hv B f t ρ := by
  rw [objective, residual_completion hv f (coefficients hv B f t ρ)]
  unfold softCost biasEnergy
  ring

/-- Exact allocation of the whole canonical observation budget. -/
theorem budget_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    canonicalBudget hv B f t ρ = softCost hv B f t ρ + biasEnergy hv B f t ρ +
      ρ ^ 2 * observationEnergy B (coefficients hv B f t ρ - inverseCoeff hv f) := by
  have h := coefficients_completion hv B f t ρ (inverseCoeff hv f)
  rw [minimum_decomposition hv B f t ρ] at h
  have hn : ‖Fintype.linearCombination ℝ v (inverseCoeff hv f - coefficients hv B f t ρ)‖ ^ 2 =
      biasEnergy hv B f t ρ := by
    rw [biasEnergy, map_sub, map_sub, norm_sub_rev]
  rw [hn, observationEnergy_sub_rev B (inverseCoeff hv f) (coefficients hv B f t ρ)] at h
  change _ + canonicalBudget hv B f t ρ = _ at h
  linarith only [h]

/-- Centered square retaining all mixed observation terms; no division or rank assumption. -/
theorem bias_centered_square {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    4 * biasEnergy hv B f t ρ + ρ ^ 2 *
      (∑ j, (2 * observe B (coefficients hv B f t ρ - inverseCoeff hv f) j +
        observe B (inverseCoeff hv f) j - t j) ^ 2) = canonicalBudget hv B f t ρ := by
  have h := budget_completion hv B f t ρ
  have hs : (∑ j, (2 * observe B (coefficients hv B f t ρ - inverseCoeff hv f) j +
        observe B (inverseCoeff hv f) j - t j) ^ 2) =
      2 * mismatchEnergy B t (coefficients hv B f t ρ) +
        2 * observationEnergy B (coefficients hv B f t ρ - inverseCoeff hv f) -
        mismatchEnergy B t (inverseCoeff hv f) := by
    unfold mismatchEnergy observationEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [observe_sub]
    ring
  rw [hs]
  dsimp only [softCost, canonicalBudget] at h ⊢
  nlinarith only [h]

theorem bias_le_quarter_budget {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    biasEnergy hv B f t ρ ≤ canonicalBudget hv B f t ρ / 4 := by
  have h := bias_centered_square hv B f t ρ
  have hs := mul_nonneg (sq_nonneg ρ) (Finset.sum_nonneg (s := Finset.univ)
    (fun j _ => sq_nonneg (2 * observe B (coefficients hv B f t ρ - inverseCoeff hv f) j +
      observe B (inverseCoeff hv f) j - t j)))
  linarith only [h, hs]

theorem softCost_le_budget {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    softCost hv B f t ρ ≤ canonicalBudget hv B f t ρ := by
  have h := budget_completion hv B f t ρ
  have hb : 0 ≤ biasEnergy hv B f t ρ := sq_nonneg _
  have ho := mul_nonneg (sq_nonneg ρ)
    (observationEnergy_nonneg B (coefficients hv B f t ρ - inverseCoeff hv f))
  linarith only [h, hb, ho]

/-- Exact nonnegative slack in the quarter-budget bias estimate for one scalar observation. -/
theorem scalar_budget_bias_slack (f t ρ : ℝ) :
    ρ ^ 2 * (f - t) ^ 2 / 4 -
      ((f + ρ ^ 2 * t) / (1 + ρ ^ 2) - f) ^ 2 =
      ρ ^ 2 * (f - t) ^ 2 * (ρ ^ 2 - 1) ^ 2 / (4 * (1 + ρ ^ 2) ^ 2) := by
  have hd : 1 + ρ ^ 2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- A single scalar observation forces every uniform canonical-budget constant
to be at least one quarter, attained at penalty one. -/
theorem scalar_budget_bias_constant_ge_quarter (C : ℝ)
    (h : ∀ f t ρ : ℝ,
      ((f + ρ ^ 2 * t) / (1 + ρ ^ 2) - f) ^ 2 ≤ C * (ρ ^ 2 * (f - t) ^ 2)) :
    (1 / 4 : ℝ) ≤ C := by
  have h1 := h 1 0 1
  norm_num at h1
  exact h1

end RiemannResearch.Analysis.RegularizationBudget
