/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityBasis
import RiemannResearch.RH.QPrimePowerParityBasis
import RiemannResearch.RH.QSquarefreeDilationObstruction
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete legal squarefree Gram–Schmidt basis

Source: user-provided legal-basis direction, 20 October 2026, and
FpOrthonormalBasisResearch20261020.md. The construction uses Mathlib's
InnerProductSpace.gramSchmidtNormed and span preservation from
Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho, then its HilbertBasis API.

The dictionary is the physical constant, the positively oriented parity unit,
and every squarefreeAtom in conductor order. Zero innovations are omitted.
Thus no unproved independence or finite-rank hypothesis is needed.
The actual closed span is exactly closureWithConstants. The full series
reconstructs the legal projection; every error identity retains the entire
orthogonal residual and all signed coefficient discrepancies.

This establishes basis completeness and the saturation equivalence, not
saturation for F_2 or F_3. Those targets remain Nat.log p n, not valuations;
their legal-closure membership and higher Meixner completeness remain open.
-/

noncomputable section
open scoped RealInnerProductSpace BigOperators
open InnerProductSpace
namespace RiemannResearch.RH.QSquarefreeCompleteBasis
open ZetaTwoHilbert PrimePowerTarget ZetaTwoParitySignal
/-- Exhaustive legal dictionary, beginning with the constant and positive parity unit. -/
def legalSeed : ℕ → QHilbert
  | 0 => qOne
  | 1 => parityUnit
  | n + 2 => ZetaTwoOptimizerStage.squarefreeAtom n

/-- The exhaustive dictionary generates precisely the enlarged squarefree legal closure. -/
theorem legalSeed_closed_span :
    (Submodule.span ℝ (Set.range legalSeed)).topologicalClosure = closureWithConstants := by
  let S := Submodule.span ℝ (Set.range legalSeed)
  have hmem (n : ℕ) : legalSeed n ∈ closureWithConstants := by
    cases n with
    | zero => exact qOne_mem_closureWithConstants
    | succ n =>
      cases n with
      | zero => exact parityUnit_mem_closureWithConstants
      | succ n =>
        apply closure_le_closureWithConstants
        exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  apply le_antisymm
  · exact S.topologicalClosure_minimal (Submodule.span_le.mpr (by rintro x ⟨n, rfl⟩; exact hmem n))
      (Submodule.isClosed_topologicalClosure _)
  · apply Submodule.topologicalClosure_minimal
    · apply sup_le
      · apply Submodule.topologicalClosure_minimal
        · apply Submodule.span_le.mpr
          rintro x ⟨n, rfl⟩
          exact S.le_topologicalClosure (Submodule.subset_span ⟨n + 2, rfl⟩)
        · exact Submodule.isClosed_topologicalClosure S
      · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
        exact S.le_topologicalClosure (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.isClosed_topologicalClosure S

/-- Retain exactly the nonzero Gram–Schmidt innovations; independence is not assumed. -/
def LegalIndex := {n : ℕ // gramSchmidtNormed ℝ legalSeed n ≠ 0}
/-- Normalized legal innovation, in the ambient actual Q Hilbert space. -/
def legalVector (i : LegalIndex) : QHilbert := gramSchmidtNormed ℝ legalSeed i.val

/-- The retained innovations are orthonormal in the actual Q inner product. -/
theorem legalVector_orthonormal : Orthonormal ℝ legalVector :=
  gramSchmidtNormed_orthonormal' legalSeed

/-- Removing zero innovations preserves the full algebraic span. -/
theorem legalVector_span :
    Submodule.span ℝ (Set.range legalVector) = Submodule.span ℝ (Set.range legalSeed) := by
  rw [← span_gramSchmidt ℝ legalSeed, ← span_gramSchmidtNormed_range legalSeed]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.val, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    by_cases h : gramSchmidtNormed ℝ legalSeed n = 0
    · rw [h]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨n, h⟩, rfl⟩

/-- Completeness in the legal closure, not in the ambient Hilbert space. -/
theorem legalVector_closed_span :
    (Submodule.span ℝ (Set.range legalVector)).topologicalClosure = closureWithConstants := by
  rw [legalVector_span, legalSeed_closed_span]

/-- Every basis direction is legal. -/
theorem legalVector_mem (i : LegalIndex) : legalVector i ∈ closureWithConstants := by
  rw [← legalVector_closed_span]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The same direction regarded as a vector of the legal closed subspace. -/
def legalVectorIn (i : LegalIndex) : closureWithConstants := ⟨legalVector i, legalVector_mem i⟩

/-- Orthonormality in the legal subspace with its inherited Q norm. -/
theorem legalVectorIn_orthonormal : Orthonormal ℝ legalVectorIn := by
  constructor
  · intro i
    exact legalVector_orthonormal.1 i
  · intro i j hij
    exact legalVector_orthonormal.2 hij

/-- No nonzero legal vector is orthogonal to every retained innovation. -/
theorem legalVectorIn_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range legalVectorIn))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hb (i : LegalIndex) : inner ℝ (x : QHilbert) (legalVector i) = 0 :=
    (Submodule.mem_orthogonal' _ x).mp hx _ (Submodule.subset_span ⟨i, rfl⟩)
  let L := innerSL ℝ (x : QHilbert)
  have hc : closureWithConstants ≤ L.ker := by
    rw [← legalVector_closed_span]
    apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact hb i
  have hz : inner ℝ (x : QHilbert) (x : QHilbert) = 0 := hc x.property
  have he : (x : QHilbert) = 0 := inner_self_eq_zero.mp hz
  exact Subtype.ext he

/-- The legal subspace is complete because it is a closed subspace of QHilbert. -/
instance legalCompleteSpace : CompleteSpace closureWithConstants :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- A complete countable Hilbert basis of closureWithConstants. -/
def legalHilbertBasis : HilbertBasis LegalIndex ℝ closureWithConstants :=
  HilbertBasis.mkOfOrthogonalEqBot legalVectorIn_orthonormal legalVectorIn_orthogonal_eq_bot

/-- The Hilbert basis uses exactly the explicit Gram–Schmidt innovations. -/
@[simp] theorem legalHilbertBasis_apply (i : LegalIndex) :
    legalHilbertBasis i = legalVectorIn i := by
  simp only [legalHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]


/-- Orthogonal projection onto the actual enlarged squarefree legal closure. -/
def legalProjection (f : QHilbert) : QHilbert := closureWithConstants.starProjection f

/-- The projected vector belongs to the legal closure. -/
theorem legalProjection_mem (f : QHilbert) : legalProjection f ∈ closureWithConstants :=
  (closureWithConstants.orthogonalProjectionOnto f).property

/-- Legal vectors are fixed by the legal projection. -/
theorem legalProjection_eq_self {f : QHilbert} (hf : f ∈ closureWithConstants) :
    legalProjection f = f :=
  closureWithConstants.starProjection_mem_subspace_eq_self ⟨f, hf⟩

/-- Legal projection preserves every legal basis coefficient. -/
theorem legalProjection_inner (f : QHilbert) (i : LegalIndex) :
    inner ℝ (legalProjection f) (legalVector i) = inner ℝ f (legalVector i) := by
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (legalVectorIn i) f

/-- The full coefficient series converges unconditionally to the legal projection. -/
theorem legalProjection_hasSum (f : QHilbert) :
    HasSum (fun i : LegalIndex => inner ℝ f (legalVector i) • legalVector i)
      (legalProjection f) := by
  have h := closureWithConstants.subtypeL.hasSum
    (legalHilbertBasis.hasSum_repr (closureWithConstants.orthogonalProjectionOnto f))
  have hc (i : LegalIndex) :
      inner ℝ (legalHilbertBasis i) (closureWithConstants.orthogonalProjectionOnto f) =
      inner ℝ f (legalVector i) := by
    rw [legalHilbertBasis_apply, real_inner_comm]
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (legalVectorIn i) f
  simp only [HilbertBasis.repr_apply_apply] at h
  simp_rw [hc] at h
  simp only [map_smul, legalHilbertBasis_apply] at h
  change HasSum (fun i : LegalIndex => inner ℝ f (legalVector i) • legalVector i)
    (closureWithConstants.orthogonalProjectionOnto f : QHilbert) at h
  rw [Submodule.coe_orthogonalProjectionOnto_apply] at h
  exact h

/-- All projected energy is retained in the infinite coefficient sum. -/
theorem legalProjection_parseval (f : QHilbert) :
    (∑' i : LegalIndex, (inner ℝ f (legalVector i)) ^ 2) = ‖legalProjection f‖ ^ 2 := by
  have h := legalHilbertBasis.tsum_inner_mul_inner
    (closureWithConstants.orthogonalProjectionOnto f)
    (closureWithConstants.orthogonalProjectionOnto f)
  have he (i : LegalIndex) :
      inner ℝ (closureWithConstants.orthogonalProjectionOnto f) (legalHilbertBasis i) *
      inner ℝ (legalHilbertBasis i) (closureWithConstants.orthogonalProjectionOnto f) =
      (inner ℝ f (legalVector i)) ^ 2 := by
    have hc : inner ℝ (legalHilbertBasis i) (closureWithConstants.orthogonalProjectionOnto f) =
        inner ℝ (closureWithConstants.orthogonalProjectionOnto f) (legalHilbertBasis i) :=
      real_inner_comm _ _
    rw [hc, legalHilbertBasis_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    change (inner ℝ f (legalVector i)) * (inner ℝ f (legalVector i)) =
      (inner ℝ f (legalVector i)) ^ 2
    ring
  simp only [he, real_inner_self_eq_norm_sq] at h
  change (∑' i : LegalIndex, (inner ℝ f (legalVector i)) ^ 2) =
    ‖(closureWithConstants.orthogonalProjectionOnto f : QHilbert)‖ ^ 2 at h
  rw [Submodule.coe_orthogonalProjectionOnto_apply] at h
  exact h

/-- Full Parseval decomposition with the entire orthogonal legal residual. -/
theorem legalBasis_energy_exact (f : QHilbert) :
    ‖f‖ ^ 2 = (∑' i : LegalIndex, (inner ℝ f (legalVector i)) ^ 2) +
      ‖f - legalProjection f‖ ^ 2 := by
  rw [legalProjection_parseval]
  exact (Submodule.norm_sq_eq_add_norm_sq_starProjection f closureWithConstants).trans
    (by rw [Submodule.starProjection_orthogonal_val]; rfl)

/-- Every signed coefficient discrepancy and the full legal residual are retained. -/
theorem legalBasis_error_exact (x f : QHilbert) (hf : f ∈ closureWithConstants) :
    ‖x - f‖ ^ 2 =
      (∑' i : LegalIndex, (inner ℝ x (legalVector i) - inner ℝ f (legalVector i)) ^ 2) +
      ‖x - legalProjection x‖ ^ 2 := by
  have he : x - f - legalProjection (x - f) = x - legalProjection x := by
    have hf' := legalProjection_eq_self hf
    unfold legalProjection at *
    rw [map_sub, hf']
    abel
  simpa only [inner_sub_left, he] using legalBasis_energy_exact (x - f)

/-- Exact saturation criterion; it does not discharge saturation for either target. -/
theorem mem_closureWithConstants_iff_parseval (f : QHilbert) :
    f ∈ closureWithConstants ↔
      (∑' i : LegalIndex, (inner ℝ f (legalVector i)) ^ 2) = ‖f‖ ^ 2 := by
  constructor
  · intro hf
    rw [legalProjection_parseval, legalProjection_eq_self hf]
  · intro he
    have h := legalBasis_energy_exact f
    rw [he] at h
    have hz : ‖f - legalProjection f‖ ^ 2 = 0 := by linarith
    have hf : f = legalProjection f := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    rw [hf]
    exact legalProjection_mem f

/-- The first raw innovation is the physical constant. -/
theorem legalGram_zero : gramSchmidt ℝ legalSeed 0 = qOne :=
  gramSchmidt_bot ℝ legalSeed

/-- The second raw innovation is the positively oriented parity unit. -/
theorem legalGram_one : gramSchmidt ℝ legalSeed 1 = parityUnit := by
  have h := gramSchmidt_def'' ℝ legalSeed 1
  have ho : inner ℝ qOne parityUnit = 0 := by rw [real_inner_comm, parityUnit_inner_one]
  have hI : Finset.Iio (1 : ℕ) = {0} := by
    ext n
    simp only [Finset.mem_Iio, Finset.mem_singleton]
    omega
  norm_num [hI, legalGram_zero, legalSeed, ho] at h
  exact h.symm

/-- Normalization preserves the physical constant. -/
theorem legalNormed_zero : gramSchmidtNormed ℝ legalSeed 0 = qOne := by
  simp [gramSchmidtNormed, legalGram_zero, qOne_norm]

/-- Normalization preserves the positive parity orientation. -/
theorem legalNormed_one : gramSchmidtNormed ℝ legalSeed 1 = parityUnit := by
  have hn : ‖parityUnit‖ = 1 := by
    nlinarith [parityUnit_norm_sq, norm_nonneg parityUnit]
  simp [gramSchmidtNormed, legalGram_one, hn]

/-- The constant innovation survives removal of zero innovations. -/
def constantIndex : LegalIndex := ⟨0, by
  rw [legalNormed_zero]
  intro h
  have hn := qOne_norm
  rw [h, norm_zero] at hn
  norm_num at hn⟩

/-- The parity innovation survives removal of zero innovations. -/
def parityIndex : LegalIndex := ⟨1, by
  rw [legalNormed_one]
  intro h
  have hn := parityUnit_norm_sq
  rw [h, norm_zero] at hn
  norm_num at hn⟩

/-- The constant basis vector is exactly qOne. -/
@[simp] theorem legalVector_constantIndex : legalVector constantIndex = qOne :=
  legalNormed_zero

/-- The parity basis vector agrees with the previously established legal unit. -/
@[simp] theorem legalVector_parityIndex : legalVector parityIndex = parityUnit :=
  legalNormed_one

/-- The complete legal basis retains coefficient 1/sqrt(3), hence energy 1/3. -/
theorem qTarget_two_legal_parity_coefficient :
    inner ℝ (qTarget 2 (by norm_num)) (legalVector parityIndex) = 1 / Real.sqrt 3 := by
  rw [legalVector_parityIndex]
  exact qTarget_two_inner_parityUnit
end RiemannResearch.RH.QSquarefreeCompleteBasis
