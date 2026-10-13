/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteObservationApproximation
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ZetaTwoParetoTransfer

/-!
# The geometric converse for squarefree exact-head tail energies

Source: user-provided CRT formulation, 13 October 2026. The common-period
algebraic space is identified with the literal squarefree residue span.
Closure membership allows exact finite heads and arbitrarily small tails.
This is a geometric equivalence, not an RH-to-density analytic assertion.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative SquarefreeStageExhaustion

theorem divisorResidueSpan_mono {K L : ℕ} (h : K ∣ L) :
    divisorResidueSpan K ≤ divisorResidueSpan L := by
  apply Submodule.span_le.mpr
  rintro F ⟨d, hd, hdK, rfl⟩
  exact Submodule.subset_span ⟨d, hd, dvd_trans hdK h, rfl⟩

/-- All finite squarefree residue combinations, represented by a squarefree
common period. This is an algebraic submodule, before taking closure. -/
def squarefreeCRTSpan : Submodule ℝ ThresholdHilbert where
  carrier := {f | ∃ L : ℕ, Squarefree L ∧ hilbertSequence f ∈ divisorResidueSpan L}
  zero_mem' := by
    refine ⟨1, by simp, ?_⟩
    change hilbertSequenceLinear 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    rintro f g ⟨L, hL, hf⟩ ⟨K, hK, hg⟩
    let J := primorialPeriod (max L K)
    have hLJ : L ∣ J := squarefree_dvd_primorialPeriod L _ hL (le_max_left _ _)
    have hKJ : K ∣ J := squarefree_dvd_primorialPeriod K _ hK (le_max_right _ _)
    refine ⟨J, primorialPeriod_squarefree _, ?_⟩
    change hilbertSequenceLinear (f + g) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ (divisorResidueSpan_mono hLJ hf)
      (divisorResidueSpan_mono hKJ hg)
  smul_mem' := by
    rintro c f ⟨L, hL, hf⟩
    refine ⟨L, hL, ?_⟩
    change hilbertSequenceLinear (c • f) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ c hf

theorem exists_near_with_same_physical_head
    (S : Submodule ℝ ThresholdHilbert) {f : ThresholdHilbert}
    (hf : f ∈ S.topologicalClosure) (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ThresholdHilbert, g ∈ S ∧
      (∀ n, 0 < n → n ≤ M → hilbertSequence g n = hilbertSequence f n) ∧
      ‖f - g‖ < ε := by
  let T : ThresholdHilbert →L[ℝ] (Fin M → ℝ) :=
    ContinuousLinearMap.pi (fun i => innerSL ℝ (paretoPointHilbert i.val))
  obtain ⟨g, hg, he, hnear⟩ :=
    RiemannResearch.Analysis.exists_near_with_same_finite_observations S T hf hε
  refine ⟨g, hg, ?_, hnear⟩
  intro n hn hnM
  let i : Fin M := ⟨n - 1, by omega⟩
  have hh := congrFun he i
  change inner ℝ (paretoPointHilbert (n - 1)) g =
    inner ℝ (paretoPointHilbert (n - 1)) f at hh
  have hpoint (v : ThresholdHilbert) :
      inner ℝ (paretoPointHilbert (n - 1)) v =
        paretoWeight (n - 1) * hilbertSequence v (n - 1 + 1) := by
    rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq]
  rw [hpoint g, hpoint f] at hh
  have heq : n - 1 + 1 = n := by omega
  rw [heq] at hh
  exact (mul_left_cancel₀ (ne_of_gt (paretoWeight_pos (n - 1)))) hh

theorem crtReciprocalEnergy_le_two_norm_sq (L : ℕ) (f : ThresholdHilbert) :
    crtReciprocalEnergy L (hilbertSequence f) ≤ 2 * ‖f‖ ^ 2 := by
  classical
  rw [crtReciprocalEnergy_eq_Icc]
  have hw (n : ℕ) : 1 / (n : ℝ) ^ 2 ≤ 2 * positiveWeight n := by
    have h := ZetaTwoParetoTransfer.zetaTwo_mul_QWeight_le_two_mul_paretoWeight n
    have he : ZetaTwoProbability.zetaTwo * ZetaTwoHilbert.positiveQWeight n =
        1 / (n : ℝ) ^ 2 := by
      unfold ZetaTwoHilbert.positiveQWeight
      field_simp [ne_of_gt ZetaTwoProbability.zetaTwo_pos]
    rwa [he] at h
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 L, 2 * (positiveWeight n * hilbertSequence f n ^ 2) := by
      apply Finset.sum_le_sum
      intro n _
      have h := mul_le_mul_of_nonneg_right (hw n) (sq_nonneg (hilbertSequence f n))
      convert h using 1 <;> ring
    _ ≤ ∑' n, 2 * (positiveWeight n * hilbertSequence f n ^ 2) :=
      ((hilbertSequence_square_summable f).mul_left 2).sum_le_tsum _
        (fun n _ => by positivity [positiveWeight_nonneg n])
    _ = 2 * ‖f‖ ^ 2 := by rw [tsum_mul_left, ← hilbert_norm_weighted_sq]

/-- Geometric converse: squarefree closure membership permits any fixed
exact head with arbitrarily small finite reciprocal tail energy. -/
theorem squarefree_exact_head_small_tail_of_closure
    (h1 : hilbertOne ∈ squarefreeCRTSpan.topologicalClosure)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (L : ℕ) (F : ℕ → ℝ), Squarefree L ∧ F ∈ divisorResidueSpan L ∧
      (∀ n, 0 < n → n ≤ M → F n = 1) ∧
      (∑ a ∈ Finset.Icc (M + 1) L, |1 - F a| ^ 2 / (a : ℝ) ^ 2) < ε := by
  obtain ⟨g, hg, hhead, hnear⟩ := exists_near_with_same_physical_head
    squarefreeCRTSpan h1 M (Real.sqrt_pos.mpr (half_pos hε))
  obtain ⟨L, hL, hgL⟩ := hg
  have hhead' (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) : hilbertSequence g n = 1 := by
    rw [hhead n hn hnM, hilbertOne_sequence]
    simp [zeroAnchor, Nat.ne_of_gt hn]
  refine ⟨L, hilbertSequence g, hL, hgL, hhead', ?_⟩
  rw [← crtReciprocalEnergy_eq_Icc_tail M L _
    (by intro n hn hnM; rw [hhead' n hn hnM]; ring)]
  have he : crtReciprocalEnergy L (fun n => 1 - hilbertSequence g n) =
      crtReciprocalEnergy L (hilbertSequence (hilbertOne - g)) := by
    unfold crtReciprocalEnergy
    apply Finset.sum_congr rfl
    intro a _
    have hseq := congrFun (hilbertSequenceLinear.map_sub hilbertOne g) (a.val + 1)
    change hilbertSequence (hilbertOne - g) (a.val + 1) =
      hilbertSequence hilbertOne (a.val + 1) - hilbertSequence g (a.val + 1) at hseq
    rw [hseq, hilbertOne_sequence]
    simp [zeroAnchor]
  rw [he]
  apply (crtReciprocalEnergy_le_two_norm_sq L (hilbertOne - g)).trans_lt
  have hs := Real.sq_sqrt (half_pos hε).le
  nlinarith [norm_nonneg (hilbertOne - g), Real.sqrt_nonneg (ε / 2)]

/-- The common-period definition is exactly the algebraic squarefree residue span. -/
theorem squarefreeCRTSpan_eq_span :
    squarefreeCRTSpan = Submodule.span ℝ
      (Set.range (fun d : {d : ℕ // 2 ≤ d ∧ Squarefree d} =>
        normalizedResidueHilbert d.val (by have := d.property.1; omega))) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨L, hL, hfL⟩ := hf
    let S := Submodule.span ℝ
      (Set.range (fun d : {d : ℕ // 2 ≤ d ∧ Squarefree d} =>
        normalizedResidueHilbert d.val (by have := d.property.1; omega)))
    have hmap : divisorResidueSpan L ≤ S.map hilbertSequenceLinear := by
      apply Submodule.span_le.mpr
      rintro F ⟨d, hd, hdL, rfl⟩
      refine ⟨normalizedResidueHilbert d (by omega), ?_,
        normalizedResidueHilbert_sequence _ _⟩
      exact Submodule.subset_span ⟨⟨d, hd, (fun x hx => hL x (dvd_trans hx hdL))⟩, rfl⟩
    obtain ⟨g, hg, hgf⟩ := hmap hfL
    have he : g = f := hilbertSequence_injective hgf
    change f ∈ S
    rw [← he]
    exact hg
  · apply Submodule.span_le.mpr
    rintro f ⟨d, rfl⟩
    refine ⟨d.val, d.property.2, ?_⟩
    rw [normalizedResidueHilbert_sequence]
    exact Submodule.subset_span ⟨d.val, d.property.1, dvd_refl _, rfl⟩

/-- Uniformly bounded finite tails with an exact head of every length.
There is no required rate or prescribed period schedule. -/
def SquarefreeExactHeadTailBound : Prop :=
  ∃ C : ℝ, ∀ M : ℕ, ∃ (L : ℕ) (F : ℕ → ℝ),
    Squarefree L ∧ F ∈ divisorResidueSpan L ∧
      (∀ n, 0 < n → n ≤ M → F n = 1) ∧
      (∑ a ∈ Finset.Icc (M + 1) L, |1 - F a| ^ 2 / (a : ℝ) ^ 2) ≤ C

/-- The geometric converse is unconditional. It characterizes squarefree
closure membership, not an assumed RH-to-density theorem. -/
theorem squarefreeClosure_iff_exact_head_tail_bound :
    hilbertOne ∈ squarefreeCRTSpan.topologicalClosure ↔
      SquarefreeExactHeadTailBound := by
  constructor
  · intro h1
    refine ⟨1, ?_⟩
    intro M
    obtain ⟨L, F, hL, hF, hh, ht⟩ :=
      squarefree_exact_head_small_tail_of_closure h1 M (by norm_num : (0 : ℝ) < 1)
    exact ⟨L, F, hL, hF, hh, ht.le⟩
  · rintro ⟨C, hC⟩
    choose L F hL hF hhead htail using hC
    choose f hf hseq hbound hp using fun M => divisorResidueSpan_lift (hF M)
    have hmem (M) : f M ∈ squarefreeCRTSpan := by
      refine ⟨L M, hL M, ?_⟩
      simpa only [hseq M] using hF M
    have henergy (M) :
        crtReciprocalEnergy (L M) (fun n => 1 - hilbertSequence (f M) n) ≤ C := by
      rw [hseq M, crtReciprocalEnergy_eq_Icc_tail M (L M) _
        (by intro n hn hnM; rw [hhead M n hn hnM]; ring)]
      exact htail M
    have hnonneg : 0 ≤ C := (crtReciprocalEnergy_nonneg _ _).trans (henergy 0)
    have hn (M) : ‖hilbertOne - f M‖ ^ 2 ≤ 2 * C := by
      obtain ⟨D, hD⟩ := hbound M
      rw [hilbertOne_sub_norm_sq_eq_paretoError]
      have he := periodic_paretoError_le_crtReciprocalEnergy (L M)
        (Nat.pos_of_ne_zero (hL M).ne_zero) (F M) hD (hp M)
      rw [← hseq M] at he
      exact he.trans (mul_le_mul_of_nonneg_left (henergy M) (by norm_num))
    apply hilbertOne_mem_closure_of_bounded_exact_heads squarefreeCRTSpan f hmem
      (C := 2 * C + 2)
    · intro M n hn hnM
      simpa only [hseq M] using hhead M n hn hnM
    · intro M
      have ht := norm_sub_le hilbertOne (hilbertOne - f M)
      have he : hilbertOne - (hilbertOne - f M) = f M := by abel
      rw [he] at ht
      have hone : ‖hilbertOne‖ ≤ 1 := by
        nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
      have herr : ‖hilbertOne - f M‖ ≤ 2 * C + 1 := by
        nlinarith [hn M, sq_nonneg (‖hilbertOne - f M‖ - 1)]
      exact (ht.trans (add_le_add hone herr)).trans_eq (by ring)


end RiemannResearch.RH.Pareto
