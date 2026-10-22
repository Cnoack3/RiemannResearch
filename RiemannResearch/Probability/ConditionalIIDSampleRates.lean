import RiemannResearch.Probability.ConditionalIIDSampleMean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Deterministic sample sizes for conditional iid approximation

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 6. The sample size depends on the unconditional variance budget, never
on the realized latent endpoint. The residual conditional-mean error is retained.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

def fiberVarianceBudget (F : ℕ → ℝ) : ℝ :=
  ∫ ω, variance F (uniformLaw (latentIndex ω)) ∂probability

theorem fiberVarianceBudget_nonneg (F : ℕ → ℝ) : 0 ≤ fiberVarianceBudget F :=
  integral_nonneg (fun ω => variance_nonneg F (uniformLaw (latentIndex ω)))

def diagonalSampleSize (F : ℕ → ℝ) (j : ℕ) : ℕ :=
  max (j + 1) ⌈(j + 1 : ℝ) * fiberVarianceBudget F⌉₊

theorem diagonalSampleSize_ge (F : ℕ → ℝ) (j : ℕ) :
    j + 1 ≤ diagonalSampleSize F j := le_max_left _ _

theorem diagonalSampleSize_pos (F : ℕ → ℝ) (j : ℕ) :
    0 < diagonalSampleSize F j := lt_of_lt_of_le (Nat.succ_pos j) (diagonalSampleSize_ge F j)

theorem diagonalSampleSize_budget (F : ℕ → ℝ) (j : ℕ) :
    (j + 1 : ℝ) * fiberVarianceBudget F ≤ (diagonalSampleSize F j : ℝ) := by
  unfold diagonalSampleSize
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (j + 1)
    ⌈(j + 1 : ℝ) * fiberVarianceBudget F⌉₊))

theorem diagonalSampleSize_variance_le (F : ℕ → ℝ) (j : ℕ) :
    fiberVarianceBudget F / (diagonalSampleSize F j : ℝ) ≤ 1 / (j + 1 : ℝ) := by
  have hr : (0 : ℝ) < diagonalSampleSize F j := by exact_mod_cast diagonalSampleSize_pos F j
  have hj : (0 : ℝ) < j + 1 := by positivity
  apply (div_le_div_iff₀ hr hj).2
  simpa only [one_mul, mul_comm] using diagonalSampleSize_budget F j

/-- The actual mean-square sample error is at most its persistent bias plus 1/(j+1). -/
theorem diagonal_average_error_le (F : ℕ → ℝ) (j : ℕ) (c : ℝ)
    (hF : ∀ i, MemLp (fun ω => F (coordinate i ω)) 2 probability) :
    (∫ ω : Omega, (c - pathAverage F (diagonalSampleSize F j) ω.2) ^ 2 ∂probability) ≤
      (∫ ω, (c - cesaro F (endpoint ω)) ^ 2 ∂probability) + 1 / (j + 1 : ℝ) := by
  rw [average_error F _ (diagonalSampleSize_pos F j) c hF]
  exact add_le_add le_rfl (diagonalSampleSize_variance_le F j)

/-- Sample sizes diverge even when the arithmetic observable changes with j. -/
theorem diagonalSampleSize_tendsto (F : ℕ → ℕ → ℝ) :
    Tendsto (fun j => diagonalSampleSize (F j) j) atTop atTop := by
  apply tendsto_atTop_mono (fun j => le_trans (Nat.le_succ j) (diagonalSampleSize_ge (F j) j))
  exact tendsto_id

/-- Conditional-mean approximation yields sample-mean approximation with explicit sample sizes. -/
theorem diagonal_average_error_tendsto (F : ℕ → ℕ → ℝ) (c : ℝ)
    (hF : ∀ j i, MemLp (fun ω => F j (coordinate i ω)) 2 probability)
    (hmean : Tendsto (fun j => ∫ ω, (c - cesaro (F j) (endpoint ω)) ^ 2 ∂probability)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ ω : Omega,
      (c - pathAverage (F j) (diagonalSampleSize (F j) j) ω.2) ^ 2 ∂probability)
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun j => integral_nonneg (fun ω => sq_nonneg _))
    (fun j => diagonal_average_error_le (F j) j c (hF j))
  simpa only [add_zero] using hmean.add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Sample-mean approximation forces conditional-mean approximation for every deterministic schedule. -/
theorem conditionalMean_error_tendsto_of_average_error (F : ℕ → ℕ → ℝ)
    (r : ℕ → ℕ) (hr : ∀ j, 0 < r j) (c : ℝ)
    (hF : ∀ j i, MemLp (fun ω => F j (coordinate i ω)) 2 probability)
    (hmean : Tendsto (fun j => ∫ ω : Omega,
      (c - pathAverage (F j) (r j) ω.2) ^ 2 ∂probability) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ ω, (c - cesaro (F j) (endpoint ω)) ^ 2 ∂probability)
      atTop (𝓝 0) := by
  exact squeeze_zero (fun j => integral_nonneg (fun ω => sq_nonneg _))
    (fun j => conditionalMean_error_le_average_error (F j) (r j) (hr j) c (hF j)) hmean

end RiemannResearch.Probability.ConditionalIID
