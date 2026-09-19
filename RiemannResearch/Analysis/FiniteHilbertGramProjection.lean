import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Finite inverse-Gram regression as orthogonal projection

Source: independently assembled for the user's CRT/regression convergence
request, 19 September 2026, using the existing exact Gram normal equations
and Mathlib's orthogonal projection uniqueness theorem. No novelty is claimed.
The target's membership in the limiting span is not inferred from uniqueness.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
noncomputable section
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def synthesisSpan (v : ι → H) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range v)

instance synthesisSpan_finiteDimensional (v : ι → H) :
    FiniteDimensional ℝ (synthesisSpan v) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem synthesis_mem (v : ι → H) (c : ι → ℝ) :
    Fintype.linearCombination ℝ v c ∈ synthesisSpan v := by
  rw [synthesisSpan, ← Fintype.range_linearCombination]
  exact ⟨c, rfl⟩

/-- Uniqueness identifies the exact inverse-Gram fit with the actual projection. -/
theorem synthesis_inverseCoeff_eq_projection {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) :
    Fintype.linearCombination ℝ v (inverseCoeff hv x) =
      (synthesisSpan v).starProjection x := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (synthesis_mem v _)
  intro w hw
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hw
  obtain ⟨c, rfl⟩ := hw
  exact residual_orthogonal hv x c

end
end RiemannResearch.Analysis.FiniteHilbertGram
