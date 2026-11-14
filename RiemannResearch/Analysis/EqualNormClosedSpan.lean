import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions
/-!
# Equal norm presentations identify closed ranges
Source: the Hilbert-space argument in V_vector_space_RH.pdf, Section 5.
This uses Mathlib's dense isometric extension theorem. No independence of the
presenting family is required; equal norms preserve all linear relations.
-/
noncomputable section
namespace RiemannResearch.Analysis.EqualNormClosedSpan
variable {M E F : Type*} [AddCommGroup M] [Module ℂ M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def closureRestrict (A : M →ₗ[ℂ] E) : M →ₗ[ℂ] A.range.topologicalClosure :=
  A.codRestrict A.range.topologicalClosure (fun m =>
    A.range.le_topologicalClosure (LinearMap.mem_range_self A m))

theorem dense_closureRestrict (A : M →ₗ[ℂ] E) : DenseRange (closureRestrict A) := by
  have hi : DenseRange (Set.inclusion A.range.le_topologicalClosure) := by
    apply (denseRange_inclusion_iff _).mpr
    exact Set.Subset.rfl
  have he : Set.range (closureRestrict A) = Set.range (Set.inclusion A.range.le_topologicalClosure) := by
    ext x
    constructor
    · rintro ⟨m,rfl⟩
      exact ⟨⟨A m, LinearMap.mem_range_self A m⟩,rfl⟩
    · rintro ⟨⟨y,⟨m,hm⟩⟩,rfl⟩
      refine ⟨m, ?_⟩
      exact Subtype.ext hm
  simpa only [DenseRange, he] using hi

def equivalence (A : M →ₗ[ℂ] E) (B : M →ₗ[ℂ] F)
    (h : ∀ m, ‖B m‖ = ‖A m‖) :
    A.range.topologicalClosure ≃ₗᵢ[ℂ] B.range.topologicalClosure :=
  (LinearEquiv.refl ℂ M).extendOfIsometry (closureRestrict A) (closureRestrict B)
    (dense_closureRestrict A) (dense_closureRestrict B) h

theorem equivalence_apply (A : M →ₗ[ℂ] E) (B : M →ₗ[ℂ] F)
    (h : ∀ m, ‖B m‖ = ‖A m‖) (m : M) :
    equivalence A B h (closureRestrict A m) = closureRestrict B m := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

end RiemannResearch.Analysis.EqualNormClosedSpan
