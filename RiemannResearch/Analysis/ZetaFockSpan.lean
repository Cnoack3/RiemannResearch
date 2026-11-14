import RiemannResearch.Analysis.EqualNormClosedSpan
import RiemannResearch.Analysis.ZetaFockKernel
import RiemannResearch.Analysis.ZetaDirichletTotality
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
/-!
# Isometry of the zeta-generated Fock and Dirichlet spans
Source: V_vector_space_RH.pdf, Section 5.
The map is constructed on the actual closed Hilbert subspaces, with an exact
formula on the generating vectors.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ZetaFockKernel
abbrev Parameter := {s : ℂ // 1 / 2 < s.re}
def coherentCombination :=
  Finsupp.linearCombination ℂ (fun s : Parameter => coherent s.1 s.2)
def integerCombination :=
  Finsupp.linearCombination ℂ (fun s : Parameter => ZetaDirichletKernel.vector s.1 s.2)

theorem combination_norm_eq (c : Parameter →₀ ℂ) :
    ‖integerCombination c‖ = ‖coherentCombination c‖ := by
  classical
  have h := finite_combination_norm_eq
    (fun i : c.support => i.val.val) (fun i : c.support => c i.val)
    (fun i : c.support => i.val.property)
  change ‖∑ i ∈ c.support, c i • ZetaDirichletKernel.vector i.val i.property‖ =
    ‖∑ i ∈ c.support, c i • coherent i.val i.property‖
  rw [← Finset.sum_coe_sort c.support
    (fun i : Parameter => c i • ZetaDirichletKernel.vector i.val i.property),
    ← Finset.sum_coe_sort c.support (fun i : Parameter => c i • coherent i.val i.property)]
  exact h.symm

def closedSpanIsometry :
    coherentCombination.range.topologicalClosure ≃ₗᵢ[ℂ]
      integerCombination.range.topologicalClosure :=
  EqualNormClosedSpan.equivalence coherentCombination integerCombination combination_norm_eq

theorem closedSpanIsometry_apply (s : Parameter) :
    closedSpanIsometry
      (EqualNormClosedSpan.closureRestrict coherentCombination (Finsupp.single s 1)) =
      EqualNormClosedSpan.closureRestrict integerCombination (Finsupp.single s 1) :=
  EqualNormClosedSpan.equivalence_apply _ _ _ _

theorem integer_closedSpan_eq_top : integerCombination.range.topologicalClosure = ⊤ := by
  rw [integerCombination, Finsupp.range_linearCombination]
  exact ZetaDirichletKernel.span_features_dense

def integerSpaceEquiv :
    integerCombination.range.topologicalClosure ≃ₗᵢ[ℂ] SampledGauge.Space ℕ where
  toFun := Subtype.val
  invFun x := ⟨x, by rw [integer_closedSpan_eq_top]; trivial⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

def fullIsometry :
    coherentCombination.range.topologicalClosure ≃ₗᵢ[ℂ] SampledGauge.Space ℕ :=
  closedSpanIsometry.trans integerSpaceEquiv

def coherentInSpace (s : Parameter) : coherentCombination.range.topologicalClosure :=
  EqualNormClosedSpan.closureRestrict coherentCombination (Finsupp.single s 1)

theorem fullIsometry_coherent (s : Parameter) :
    fullIsometry (coherentInSpace s) = ZetaDirichletKernel.vector s.val s.property := by
  have h := congrArg Subtype.val (closedSpanIsometry_apply s)
  change (closedSpanIsometry (coherentInSpace s)).val =
    integerCombination (Finsupp.single s 1) at h
  change (closedSpanIsometry (coherentInSpace s)).val =
    ZetaDirichletKernel.vector s.val s.property
  exact h.trans (by simp [integerCombination])

def integerBasis : HilbertBasis ℕ ℂ coherentCombination.range.topologicalClosure :=
  HilbertBasis.ofRepr fullIsometry

theorem integerBasis_orthonormal : Orthonormal ℂ integerBasis :=
  integerBasis.orthonormal

theorem integerBasis_dense :
    (Submodule.span ℂ (Set.range integerBasis)).topologicalClosure = ⊤ :=
  integerBasis.dense_span

theorem coherent_basis_hasSum (s : Parameter) :
    HasSum (fun n => ZetaDirichletKernel.feature s.val n • integerBasis n)
      (coherentInSpace s) := by
  have h := integerBasis.hasSum_repr (coherentInSpace s)
  change HasSum (fun n => fullIsometry (coherentInSpace s) n • integerBasis n) _ at h
  rw [fullIsometry_coherent] at h
  exact h

end RiemannResearch.Analysis.ZetaFockKernel
