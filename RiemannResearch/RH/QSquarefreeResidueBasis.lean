/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An orthonormal basis of the literal squarefree residue closure

Source: the user's basis request, 4 November 2026. The construction specializes
Mathlib Gram-Schmidt and HilbertBasis to the residue-only dictionary.
The proof follows the project's QSquarefreeCompleteBasis construction, whose
space instead adjoins constants. No constant-membership hypothesis is used.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open InnerProductSpace
namespace RiemannResearch.RH.QSquarefreeResidueBasis
open ZetaTwoHilbert
/-- The exhaustive squarefree residue dictionary; no constant is adjoined. -/
def residueSeed : ℕ → QHilbert := ZetaTwoOptimizerStage.squarefreeAtom

/-- The dictionary generates the literal squarefree closure. -/
theorem residueSeed_closed_span :
    (Submodule.span ℝ (Set.range residueSeed)).topologicalClosure =
      ZetaTwoOptimizerStage.closure := by
  rfl

/-- Retain exactly the nonzero Gram–Schmidt innovations; independence is not assumed. -/
def ResidueIndex := {n : ℕ // gramSchmidtNormed ℝ residueSeed n ≠ 0}
/-- Normalized residue innovation, in the ambient actual Q Hilbert space. -/
def residueVector (i : ResidueIndex) : QHilbert := gramSchmidtNormed ℝ residueSeed i.val

/-- The retained innovations are orthonormal in the actual Q inner product. -/
theorem residueVector_orthonormal : Orthonormal ℝ residueVector :=
  gramSchmidtNormed_orthonormal' residueSeed

/-- Removing zero innovations preserves the full algebraic span. -/
theorem residueVector_span :
    Submodule.span ℝ (Set.range residueVector) = Submodule.span ℝ (Set.range residueSeed) := by
  rw [← span_gramSchmidt ℝ residueSeed, ← span_gramSchmidtNormed_range residueSeed]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.val, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    by_cases h : gramSchmidtNormed ℝ residueSeed n = 0
    · rw [h]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨n, h⟩, rfl⟩

/-- Completeness in the residue closure, not in the ambient Hilbert space. -/
theorem residueVector_closed_span :
    (Submodule.span ℝ (Set.range residueVector)).topologicalClosure =
      ZetaTwoOptimizerStage.closure := by
  rw [residueVector_span, residueSeed_closed_span]

/-- Every basis direction belongs to the literal squarefree closure. -/
theorem residueVector_mem (i : ResidueIndex) : residueVector i ∈ ZetaTwoOptimizerStage.closure := by
  rw [← residueVector_closed_span]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The same direction regarded as a vector of the residue closed subspace. -/
def residueVectorIn (i : ResidueIndex) : ZetaTwoOptimizerStage.closure :=
  ⟨residueVector i, residueVector_mem i⟩

/-- Orthonormality in the residue subspace with its inherited Q norm. -/
theorem residueVectorIn_orthonormal : Orthonormal ℝ residueVectorIn := by
  constructor
  · intro i
    exact residueVector_orthonormal.1 i
  · intro i j hij
    exact residueVector_orthonormal.2 hij

/-- No nonzero residue vector is orthogonal to every retained innovation. -/
theorem residueVectorIn_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range residueVectorIn))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hb (i : ResidueIndex) : inner ℝ (x : QHilbert) (residueVector i) = 0 :=
    (Submodule.mem_orthogonal' _ x).mp hx _ (Submodule.subset_span ⟨i, rfl⟩)
  let L := innerSL ℝ (x : QHilbert)
  have hc : ZetaTwoOptimizerStage.closure ≤ L.ker := by
    rw [← residueVector_closed_span]
    apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact hb i
  have hz : inner ℝ (x : QHilbert) (x : QHilbert) = 0 := hc x.property
  have he : (x : QHilbert) = 0 := inner_self_eq_zero.mp hz
  exact Subtype.ext he

/-- The residue subspace is complete because it is a closed subspace of QHilbert. -/
instance residueCompleteSpace : CompleteSpace ZetaTwoOptimizerStage.closure :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- A complete countable Hilbert basis of ZetaTwoOptimizerStage.closure. -/
def residueHilbertBasis : HilbertBasis ResidueIndex ℝ ZetaTwoOptimizerStage.closure :=
  HilbertBasis.mkOfOrthogonalEqBot residueVectorIn_orthonormal residueVectorIn_orthogonal_eq_bot

/-- The Hilbert basis uses exactly the explicit Gram–Schmidt innovations. -/
@[simp] theorem residueHilbertBasis_apply (i : ResidueIndex) :
    residueHilbertBasis i = residueVectorIn i := by
  simp only [residueHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]


/-- Orthogonal projection onto the literal squarefree residue closure. -/
def residueProjection (f : QHilbert) : QHilbert := ZetaTwoOptimizerStage.closure.starProjection f

/-- The projected vector belongs to the residue closure. -/
theorem residueProjection_mem (f : QHilbert) :
    residueProjection f ∈ ZetaTwoOptimizerStage.closure :=
  (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f).property

/-- Legal vectors are fixed by the residue projection. -/
theorem residueProjection_eq_self {f : QHilbert} (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    residueProjection f = f :=
  ZetaTwoOptimizerStage.closure.starProjection_mem_subspace_eq_self ⟨f, hf⟩

/-- Legal projection preserves every residue basis coefficient. -/
theorem residueProjection_inner (f : QHilbert) (i : ResidueIndex) :
    inner ℝ (residueProjection f) (residueVector i) = inner ℝ f (residueVector i) := by
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (residueVectorIn i) f

/-- The full coefficient series converges unconditionally to the residue projection. -/
theorem residueProjection_hasSum (f : QHilbert) :
    HasSum (fun i : ResidueIndex => inner ℝ f (residueVector i) • residueVector i)
      (residueProjection f) := by
  have h := ZetaTwoOptimizerStage.closure.subtypeL.hasSum
    (residueHilbertBasis.hasSum_repr (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f))
  have hc (i : ResidueIndex) :
      inner ℝ (residueHilbertBasis i) (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f) =
      inner ℝ f (residueVector i) := by
    rw [residueHilbertBasis_apply, real_inner_comm]
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (residueVectorIn i) f
  simp only [HilbertBasis.repr_apply_apply] at h
  simp_rw [hc] at h
  simp only [map_smul, residueHilbertBasis_apply] at h
  change HasSum (fun i : ResidueIndex => inner ℝ f (residueVector i) • residueVector i)
    (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f : QHilbert) at h
  rw [Submodule.coe_orthogonalProjectionOnto_apply] at h
  exact h

/-- All projected energy is retained in the infinite coefficient sum. -/
theorem residueProjection_parseval (f : QHilbert) :
    (∑' i : ResidueIndex, (inner ℝ f (residueVector i)) ^ 2) = ‖residueProjection f‖ ^ 2 := by
  have h := residueHilbertBasis.tsum_inner_mul_inner
    (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f)
    (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f)
  have he (i : ResidueIndex) :
      inner ℝ (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f) (residueHilbertBasis i) *
      inner ℝ (residueHilbertBasis i) (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f) =
      (inner ℝ f (residueVector i)) ^ 2 := by
    have hc :
        inner ℝ (residueHilbertBasis i)
          (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f) =
        inner ℝ (ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f)
          (residueHilbertBasis i) :=
      real_inner_comm _ _
    rw [hc, residueHilbertBasis_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    change (inner ℝ f (residueVector i)) * (inner ℝ f (residueVector i)) =
      (inner ℝ f (residueVector i)) ^ 2
    ring
  simp only [he, real_inner_self_eq_norm_sq] at h
  change (∑' i : ResidueIndex, (inner ℝ f (residueVector i)) ^ 2) =
    ‖(ZetaTwoOptimizerStage.closure.orthogonalProjectionOnto f : QHilbert)‖ ^ 2 at h
  rw [Submodule.coe_orthogonalProjectionOnto_apply] at h
  exact h

/-- Full Parseval decomposition with the entire orthogonal residue residual. -/
theorem residueBasis_energy_exact (f : QHilbert) :
    ‖f‖ ^ 2 = (∑' i : ResidueIndex, (inner ℝ f (residueVector i)) ^ 2) +
      ‖f - residueProjection f‖ ^ 2 := by
  rw [residueProjection_parseval]
  exact (Submodule.norm_sq_eq_add_norm_sq_starProjection f ZetaTwoOptimizerStage.closure).trans
    (by rw [Submodule.starProjection_orthogonal_val]; rfl)

/-- Every signed coefficient discrepancy and the full residue residual are retained. -/
theorem residueBasis_error_exact (x f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    ‖x - f‖ ^ 2 =
      (∑' i : ResidueIndex, (inner ℝ x (residueVector i) - inner ℝ f (residueVector i)) ^ 2) +
      ‖x - residueProjection x‖ ^ 2 := by
  have he : x - f - residueProjection (x - f) = x - residueProjection x := by
    have hf' := residueProjection_eq_self hf
    unfold residueProjection at *
    rw [map_sub, hf']
    abel
  simpa only [inner_sub_left, he] using residueBasis_energy_exact (x - f)

/-- Exact Parseval criterion for membership in the literal squarefree closure. -/
theorem mem_closure_iff_parseval (f : QHilbert) :
    f ∈ ZetaTwoOptimizerStage.closure ↔
      (∑' i : ResidueIndex, (inner ℝ f (residueVector i)) ^ 2) = ‖f‖ ^ 2 := by
  constructor
  · intro hf
    rw [residueProjection_parseval, residueProjection_eq_self hf]
  · intro he
    have h := residueBasis_energy_exact f
    rw [he] at h
    have hz : ‖f - residueProjection f‖ ^ 2 = 0 := by linarith
    have hf : f = residueProjection f := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    rw [hf]
    exact residueProjection_mem f


/-- Exact constant-energy criterion for the literal squarefree closure. -/
theorem qOne_mem_closure_iff_parseval :
    qOne ∈ ZetaTwoOptimizerStage.closure ↔
      (∑' i : ResidueIndex, (inner ℝ qOne (residueVector i)) ^ 2) = 1 := by
  simpa only [qOne_norm_sq] using mem_closure_iff_parseval qOne

end RiemannResearch.RH.QSquarefreeResidueBasis
