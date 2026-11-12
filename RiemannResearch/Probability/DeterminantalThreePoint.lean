import RiemannResearch.Probability.DeterminantalEntry
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Three-point inclusion and the connected cycle

Source: Lyons, https://arxiv.org/abs/math/0204325, for determinantal
correlations. This expands the defining determinant with every signed term.
Consumer: the actual-zero Fourier projection DPP.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace RiemannResearch.Probability.DPP
variable {α Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Set α} {K : α → α → ℝ}

/-- The complete signed three-point inclusion determinant. -/
theorem IsDPP.three_point (h : IsDPP μ X K) (e : Fin 3 ↪ α) :
    μ.real {ω | ∀ i : Fin 3, e i ∈ X ω} =
      K (e 0) (e 0) * K (e 1) (e 1) * K (e 2) (e 2) -
      K (e 0) (e 0) * K (e 1) (e 2) * K (e 2) (e 1) -
      K (e 1) (e 1) * K (e 0) (e 2) * K (e 2) (e 0) -
      K (e 2) (e 2) * K (e 0) (e 1) * K (e 1) (e 0) +
      K (e 0) (e 1) * K (e 1) (e 2) * K (e 2) (e 0) +
      K (e 0) (e 2) * K (e 2) (e 1) * K (e 1) (e 0) := by
  rw [h.correlation, Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  ring

/-- The connected third correlation is the sum of both directed cycles.
Unlike two-point covariance, its sign is not fixed by positive contraction. -/
theorem IsDPP.connected_three (h : IsDPP μ X K) (e : Fin 3 ↪ α) :
    μ.real {ω | ∀ i : Fin 3, e i ∈ X ω} -
      K (e 0) (e 0) * μ.real {ω | e 1 ∈ X ω ∧ e 2 ∈ X ω} -
      K (e 1) (e 1) * μ.real {ω | e 0 ∈ X ω ∧ e 2 ∈ X ω} -
      K (e 2) (e 2) * μ.real {ω | e 0 ∈ X ω ∧ e 1 ∈ X ω} +
      2 * K (e 0) (e 0) * K (e 1) (e 1) * K (e 2) (e 2) =
      K (e 0) (e 1) * K (e 1) (e 2) * K (e 2) (e 0) +
      K (e 0) (e 2) * K (e 2) (e 1) * K (e 1) (e 0) := by
  rw [h.three_point e, h.two_point (e.injective.ne (by decide : (1 : Fin 3) ≠ 2)),
    h.two_point (e.injective.ne (by decide : (0 : Fin 3) ≠ 2)),
    h.two_point (e.injective.ne (by decide : (0 : Fin 3) ≠ 1))]
  ring
end RiemannResearch.Probability.DPP
