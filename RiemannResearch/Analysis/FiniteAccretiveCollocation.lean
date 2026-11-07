import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite collocation for an injective difference of a contraction

Source: user-provided CRT collocation handoff, 6 November 2026, Section 3.
This abstracts its finite solvability argument. The concrete RH consumer is
the anchored physical Q shift and divisor-cutoff residue spaces.
No uniform inverse bound is asserted.
-/

noncomputable section
namespace RiemannResearch.Analysis.FiniteAccretiveCollocation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem difference_energy (S : H →L[ℝ] H) (f : H) :
    2 * inner ℝ f (f - S f) =
      ‖f - S f‖ ^ 2 + ‖f‖ ^ 2 - ‖S f‖ ^ 2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real]
  ring

omit [CompleteSpace H] in
theorem eq_zero_of_difference_inner (S : H →L[ℝ] H)
    (hS : ∀ f, ‖S f‖ ≤ ‖f‖)
    (hinj : Function.Injective (ContinuousLinearMap.id ℝ H - S))
    (f : H) (hf : inner ℝ f (f - S f) = 0) : f = 0 := by
  have he := difference_energy S f
  have hn := hS f
  have hz : ‖f - S f‖ = 0 := by
    nlinarith [sq_nonneg ‖f - S f‖, norm_nonneg f, norm_nonneg (S f)]
  apply hinj
  change f - S f = 0 - S 0
  simpa using norm_eq_zero.mp hz

/-- A finite test system with strictly accretive diagonal is uniquely solvable. -/
theorem existsUnique_test_match (D : H →L[ℝ] H)
    (hD : ∀ f, inner ℝ f (D f) = 0 → f = 0)
    (V : Submodule ℝ H) [FiniteDimensional ℝ V] (h : H) :
    ∃! f : V, ∀ v : V, inner ℝ (f : H) (D v) = inner ℝ h (D v) := by
  let A : V →ₗ[ℝ] V :=
    ((V.orthogonalProjectionOnto.comp D.adjoint).toLinearMap).comp V.subtype
  have hpair (f v : V) : inner ℝ (A f : H) (v : H) =
      inner ℝ (f : H) (D v) := by
    change inner ℝ (V.starProjection (D.adjoint f)) (v : H) = _
    rw [V.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr v.property, D.adjoint_inner_left]
  have hinj : Function.Injective A := by
    intro f g he
    have hz : A (f - g) = 0 := by rw [map_sub, he, sub_self]
    have hfg : ((f - g : V) : H) = 0 := by
      apply hD
      rw [← hpair, hz]
      simp
    apply Subtype.ext
    exact sub_eq_zero.mp hfg
  obtain ⟨f, hf⟩ := LinearMap.surjective_of_injective hinj
    (V.orthogonalProjectionOnto (D.adjoint h))
  have hmatch : ∀ v : V, inner ℝ (f : H) (D v) = inner ℝ h (D v) := by
    intro v
    rw [← hpair, hf]
    change inner ℝ (V.starProjection (D.adjoint h)) (v : H) = _
    rw [V.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr v.property, D.adjoint_inner_left]
  refine ⟨f, hmatch, ?_⟩
  intro g hg
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hD
  change inner ℝ ((g : H) - (f : H)) (D ((g - f : V) : H)) = 0
  rw [inner_sub_left, hg (g-f), hmatch (g-f), sub_self]

omit [CompleteSpace H] in
/-- The complete contraction defect is kept in this exact energy identity. -/
theorem matched_energy (S : H →L[ℝ] H) (f h : H)
    (hm : inner ℝ f (f - S f) = inner ℝ h (f - S f)) :
    ‖f - S f - h‖ ^ 2 + (‖f‖ ^ 2 - ‖S f‖ ^ 2) = ‖h‖ ^ 2 := by
  have he := difference_energy S f
  rw [norm_sub_sq_real, real_inner_comm h (f - S f)]
  linarith

omit [CompleteSpace H] in
theorem matched_defect_le (S : H →L[ℝ] H) (f h : H)
    (hm : inner ℝ f (f - S f) = inner ℝ h (f - S f)) :
    ‖f‖ ^ 2 - ‖S f‖ ^ 2 ≤ ‖h‖ ^ 2 := by
  have he := matched_energy S f h hm
  linarith [sq_nonneg ‖f - S f - h‖]

end RiemannResearch.Analysis.FiniteAccretiveCollocation
