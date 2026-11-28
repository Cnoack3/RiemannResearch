/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailReciprocalCell
import RiemannResearch.RH.LegalTailTriangularMesh
import RiemannResearch.RH.ParetoFiniteHeadRepair

/-!
# The completed legal stage equals its real reciprocal mesh

Source: Christian Noack, November 2026. Finite approximants preserve the
entire prescribed head. The constant generator at parameter one vanishes.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open FiniteHeadRepair RiemannResearch.RH.Burnol.ContinuousNyman
open RiemannResearch.RH.ArithmeticCumulative

private theorem real_gen_memLp (α : ℝ) : MemLp (realGenerator α) 2 intervalMeasure :=
  MemLp.of_bound (realGenerator_measurable α).aestronglyMeasurable (1+|α|)
    (Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using realGenerator_abs_le α t))

def realMeshGenerator (α : ℝ) : RealMeshHilbert := (real_gen_memLp α).toLp _
theorem realMeshGenerator_ae (α : ℝ) :
    (realMeshGenerator α : ℝ → ℝ) =ᵐ[intervalMeasure] realGenerator α :=
  (real_gen_memLp α).coeFn_toLp

def realStageMesh (K : ℕ) : Submodule ℝ RealMeshHilbert :=
  (Submodule.span ℝ (realMeshGenerator '' scaleMeshParameters (K+1))).topologicalClosure

instance (K : ℕ) : CompleteSpace (realStageMesh K) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

private theorem real_gen_one : realMeshGenerator 1 = 0 := by
  apply Lp.ext
  filter_upwards [realMeshGenerator_ae 1, (Lp.coeFn_zero ℝ 2 intervalMeasure)] with t ht h0
  calc
    _ = realGenerator 1 t := ht
    _ = (0 : ℝ) := by simp [realGenerator]
    _ = _ := h0.symm

private theorem real_gen_sum_ae (s : Finset ℕ) (a α : ℕ → ℝ) :
    ((∑ d ∈ s, a d • realMeshGenerator (α d) : RealMeshHilbert) : ℝ → ℝ) =ᵐ[intervalMeasure]
      fun t => ∑ d ∈ s, a d * realGenerator (α d) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 intervalMeasure
  | @insert d s hd ih =>
    simp only [Finset.sum_insert hd]
    filter_upwards [Lp.coeFn_add (a d • realMeshGenerator (α d))
      (∑ j ∈ s, a j • realMeshGenerator (α j)),
      Lp.coeFn_smul (a d) (realMeshGenerator (α d)), realMeshGenerator_ae (α d), ih] with t h₁ h₂ h₃ h₄
    simp only [h₁,Pi.add_apply,h₂,Pi.smul_apply,h₃,h₄,smul_eq_mul]

private theorem finite_cell_expansion (K : ℕ) {F : ℕ → ℝ}
    (hF : F ∈ legalSeedSpan (Ici 1)) (h0 : ∀ n, 0 < n → n ≤ K → F n = 0) :
    ∃ (s : Finset ℕ) (a : ℕ → ℝ), (∀ d ∈ s, K < d) ∧
      ∀ t : ℝ, 0 < t → F ⌊((K+1 : ℕ) : ℝ)/t⌋₊ =
        ∑ d ∈ s, a d * realGenerator (((K+1 : ℕ) : ℝ)/d) t := by
  cases K with
  | succ K => exact legal_zero_head_exists_nyman_mesh _ (Nat.succ_pos _) hF h0
  | zero =>
    obtain ⟨s,c,hs,hc⟩ := legal_exists_normalized_synthesis hF
    refine ⟨s,c,fun d hd => by have := hs d hd; omega, ?_⟩
    intro t ht
    rw [← hc]
    apply Finset.sum_congr rfl
    intro d hd
    rw [realGenerator_eq_neg_divisorAnchor _ _ (by decide) (by have := hs d hd; omega) t ht]
    simp [divisorAnchorDirection, residueFraction, Nat.mod_one]

private theorem finite_cell_mem (K : ℕ) (v : TailHeadSpace K)
    (hv : v.val ∈ hilbertLegalSubspace (Ici 1)) : reciprocalCellMap K v ∈ realStageMesh K := by
  obtain ⟨s,a,hs,hf⟩ := finite_cell_expansion K (F := hilbertSequence v) hv
    (fun n _ hn => legalHeadKernel_sequence_zero v.property hn)
  let α := fun d : ℕ => ((K+1 : ℕ) : ℝ)/d
  have he : reciprocalCellMap K v = ∑ d ∈ s, a d • realMeshGenerator (α d) := by
    apply Lp.ext
    filter_upwards [reciprocalCellMap_ae K v, real_gen_sum_ae s a α,
      ae_restrict_mem (μ := volume) measurableSet_Ioc] with t h₁ h₂ ht
    exact h₁.trans ((hf t ht.1).trans h₂.symm)
  rw [he]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  by_cases heq : d = K+1
  · subst d
    change realMeshGenerator (((K+1 : ℕ) : ℝ)/((K+1 : ℕ) : ℝ)) ∈ realStageMesh K
    rw [div_self (by positivity), real_gen_one]
    exact Submodule.zero_mem _
  · apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨α d, ⟨d, by have := hs d hd; omega, rfl⟩, rfl⟩

theorem legalCellMap_range_eq_realStageMesh (K : ℕ) : (legalCellMap K).range = realStageMesh K := by
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    obtain ⟨u,hu,ht⟩ := exists_exact_head_approximants K v
      (CoefficientStabilization.closedSpace_le_legalClosure v.property.1)
    have hhead (n : ℕ) : u n ∈ TailHeadSpace K := by
      change headMap K _ = 0
      ext i
      rw [headMap_apply, (hu n).2 _ (Nat.succ_pos _) (by have := i.isLt; omega),
        legalHeadKernel_sequence_zero v.property.2 (by have := i.isLt; omega)]
      rfl
    let a := fun n => (⟨u n, hhead n⟩ : TailHeadSpace K)
    let b : TailHeadSpace K := ⟨v.val,v.property.2⟩
    have hat : Tendsto a atTop (𝓝 b) := tendsto_subtype_rng.mpr ht
    have hc : Continuous (reciprocalCellMap K) :=
      ((reciprocalCellMap K).mkContinuous (Real.sqrt (K+1 : ℕ))
        (fun f => (reciprocalCellMap_norm K f).le)).continuous
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (hc.continuousAt.tendsto.comp hat)
      (Eventually.of_forall (fun n => finite_cell_mem K (a n) (hu n).1))
  · apply Submodule.topologicalClosure_minimal _ _ (legalCellMap_range_closed K)
    apply Submodule.span_le.mpr
    rintro _ ⟨α,⟨d,hd,rfl⟩,rfl⟩
    let m := K+1
    have hm : 0 < m := Nat.succ_pos _
    have hv := rational_residue_pair_mem_legalHeadKernel m d hm hd.le
    let v : legalHeadKernel K := ⟨_,by simpa [m] using hv⟩
    refine ⟨v, ?_⟩
    apply Lp.ext
    filter_upwards [reciprocalCellMap_ae K ⟨v.val,v.property.2⟩, realMeshGenerator_ae ((m : ℝ)/d),
      ae_restrict_mem (μ := volume) measurableSet_Ioc] with t h₁ h₂ ht
    change (reciprocalCellMap K ⟨v.val,v.property.2⟩ : ℝ → ℝ) t = _
    rw [h₁,h₂,realGenerator_eq_neg_divisorAnchor _ _ hm (hm.trans hd) t ht.1]
    simp only [reciprocalCellFunction,v,hilbertSequence_sub,hilbertSequence_smul,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,normalizedResidueHilbert_sequence,divisorAnchorDirection,m]
    push_cast
    ring

theorem legalCellIsometry_range (K : ℕ) :
    (legalCellIsometry K).toLinearMap.range = realStageMesh K :=
  (legalCellMap_range_eq_isometry K).symm.trans (legalCellMap_range_eq_realStageMesh K)

theorem realStageMesh_projection (K : ℕ) :
    (realStageMesh K).starProjection realMeshUnit = commonTailOptimizer K := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← legalCellMap_range_eq_realStageMesh]
    exact ⟨_,rfl⟩
  · intro y hy
    rw [← legalCellMap_range_eq_realStageMesh] at hy
    obtain ⟨v,rfl⟩ := hy
    let t : TailHeadSpace K := ⟨paretoTail K, paretoTail_mem_headKer K⟩
    let p : TailHeadSpace K := ⟨legalTailMeanVector K,(legalTailMeanVector_mem K).2⟩
    let w : TailHeadSpace K := ⟨v.val,v.property.2⟩
    have hr : inner ℝ (t-p) w = 0 := legalTailResidual_orthogonal v.property
    have hi := (reciprocalCellIsometry K).inner_map_map (t-p) w
    change inner ℝ ((Real.sqrt (K+1 : ℕ))⁻¹ • reciprocalCellMap K (t-p))
      ((Real.sqrt (K+1 : ℕ))⁻¹ • reciprocalCellMap K w) = _ at hi
    rw [real_inner_smul_left, real_inner_smul_right, hr] at hi
    rw [← reciprocalCellMap_tail K]
    change inner ℝ (reciprocalCellMap K t - reciprocalCellMap K p) (reciprocalCellMap K w) = 0
    rw [← map_sub]
    have hs : (Real.sqrt (K+1 : ℕ))⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hs)).resolve_left hs

theorem normalizedLegalTailMeanCapacity_eq_realMeshProjection (K : ℕ) :
    normalizedLegalTailMeanCapacity K = ‖(realStageMesh K).starProjection realMeshUnit‖^2 := by
  rw [realStageMesh_projection,commonTailOptimizer_norm_sq]

end RiemannResearch.RH.Pareto.PrimePowerSchur
