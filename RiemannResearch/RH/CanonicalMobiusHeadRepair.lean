/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusWindowMinimum
import RiemannResearch.RH.ResidueClosureDensity

/-!
# Continuous finite head repair in the genuine legal span

Source: user-provided affine-exhaustion handoff, Section 12. The repair
uses the proved consecutive residue triangular basis. Density is an
explicit hypothesis of the approximation results, not an asserted fact.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Repair finitely many physical coordinates using legal triangular steps. -/
def legalHeadRepair (z : ThresholdHilbert) : ℕ → ThresholdHilbert → ThresholdHilbert
  | 0, x => x
  | n + 1, x => legalHeadRepair z n x +
      ((hilbertSequence z (n + 1) -
        hilbertSequence (legalHeadRepair z n x) (n + 1)) / ((n + 1 : ℕ) : ℝ)) •
        consecutiveResidueHilbert n

theorem legalHeadRepair_exact (z x : ThresholdHilbert) (N : ℕ)
    (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    hilbertSequence (legalHeadRepair z N x) j = hilbertSequence z j := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [legalHeadRepair, hilbertSequence_add, hilbertSequence_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : j ≤ N
    · rw [consecutiveResidueHilbert_head_zero N j h, mul_zero, add_zero]
      exact ih h
    · have he : j = N + 1 := by omega
      subst j
      rw [consecutiveResidueHilbert_diagonal]
      have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring

theorem legalHeadRepair_self (z : ThresholdHilbert) (N : ℕ) :
    legalHeadRepair z N z = z := by
  induction N with
  | zero => rfl
  | succ N ih => simp [legalHeadRepair, ih]

theorem legalHeadRepair_continuous (z : ThresholdHilbert) (N : ℕ) :
    Continuous (legalHeadRepair z N) := by
  induction N with
  | zero => exact continuous_id
  | succ N ih =>
    change Continuous (fun x => legalHeadRepair z N x +
      ((hilbertSequence z (N + 1) -
        hilbertSequence (legalHeadRepair z N x) (N + 1)) /
          ((N + 1 : ℕ) : ℝ)) • consecutiveResidueHilbert N)
    simp_rw [← anchoredEvaluationCLM_apply (N + 1)]
    exact ih.add (((continuous_const.sub
      ((anchoredEvaluationCLM (N + 1)).continuous.comp ih)).div_const _).smul
        continuous_const)

/-- Repairing N observations introduces no conductor beyond max(M,N)+1. -/
theorem legalHeadRepair_mem_finiteSpace (z x : ThresholdHilbert) (N M : ℕ)
    (hx : x ∈ finiteSpace M) :
    legalHeadRepair z N x ∈ finiteSpace (max M N) := by
  induction N with
  | zero => simpa [legalHeadRepair] using hx
  | succ N ih =>
    apply (finiteSpace (max M (N + 1))).add_mem
    · exact walkSpan_mono residueAtom id (by omega : max M N ≤ max M (N + 1)) ih
    · apply Submodule.smul_mem
      rw [← canonicalMobiusSpan_eq_finiteSpace]
      exact consecutiveResidueHilbert_mem_canonicalMobiusSpan _ N (by omega)

/-- Every target in the closed residue span has finite legal approximants
with any fixed initial segment imposed exactly. -/
theorem exists_legal_exact_head_approximants
    (z : ThresholdHilbert) (hz : z ∈ closedSpace) (N : ℕ) :
    ∃ f : ℕ → ThresholdHilbert,
      (∀ M, f M ∈ finiteSpace (max M N)) ∧
      (∀ M j, 0 < j → j ≤ N → hilbertSequence (f M) j = hilbertSequence z j) ∧
      Tendsto f atTop (𝓝 z) := by
  let f : ℕ → ThresholdHilbert := fun M =>
    legalHeadRepair z N ((finiteSpace M).starProjection z)
  have ht : Tendsto (fun M => (finiteSpace M).starProjection z) atTop (𝓝 z) := by
    have h := walkProjection_tendsto residueAtom id Function.surjective_id z
    have he : closedSpace.starProjection z = z :=
      (Submodule.starProjection_eq_self_iff).2 hz
    change Tendsto (fun M => (finiteSpace M).starProjection z)
      atTop (𝓝 (closedSpace.starProjection z)) at h
    rwa [he] at h
  refine ⟨f, ?_, ?_, ?_⟩
  · intro M
    exact legalHeadRepair_mem_finiteSpace z _ N M
      ((finiteSpace M).starProjection_apply_mem z)
  · intro M j hj hjN
    exact legalHeadRepair_exact z _ N j hj hjN
  · simpa only [f, Function.comp_def, legalHeadRepair_self] using
      ((legalHeadRepair_continuous z N).tendsto z).comp ht

/-- Fixed-head interpolation is dense in its corresponding closed affine slice. -/
theorem exists_legal_exact_head_near
    (z : ThresholdHilbert) (hz : z ∈ closedSpace) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M, N ≤ M ∧ ∃ x : ThresholdHilbert, x ∈ finiteSpace M ∧
      (∀ j, 0 < j → j ≤ N → hilbertSequence x j = hilbertSequence z j) ∧
      ‖x - z‖ ^ 2 < ε := by
  obtain ⟨f, hmem, hhead, ht⟩ := exists_legal_exact_head_approximants z hz N
  have he : Tendsto (fun M => ‖f M - z‖ ^ 2) atTop (𝓝 0) := by
    simpa using (ht.sub (tendsto_const_nhds (x := z))).norm.pow 2
  have hsmall : ∀ᶠ M in atTop, ‖f M - z‖ ^ 2 < ε :=
    (tendsto_order.1 he).2 ε hε
  obtain ⟨M, hM⟩ := hsmall.exists
  exact ⟨max M N, le_max_right _ _, f M, hmem M, hhead M, hM⟩

private theorem finiteSpace_mem_closedSpace_aux (M : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ finiteSpace M) : x ∈ closedSpace := by
  exact Submodule.le_topologicalClosure _ (walkSpan_le residueAtom id M hx)

/-- A fixed head with arbitrary conductor support and complete error norm. -/
def FixedHeadApproximation (z : ThresholdHilbert) (N : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, N ≤ M ∧ ∃ x : ThresholdHilbert,
    x ∈ finiteSpace M ∧
    (∀ j, 0 < j → j ≤ N → hilbertSequence x j = hilbertSequence z j) ∧
    ‖x - z‖ ^ 2 < ε

/-- Prescribing any fixed physical head imposes no additional closure
condition when the conductor budget is allowed to grow. -/
theorem fixedHeadApproximation_iff_mem_closedSpace
    (z : ThresholdHilbert) (N : ℕ) :
    FixedHeadApproximation z N ↔ z ∈ closedSpace := by
  constructor
  · intro h
    have hc : IsClosed (closedSpace : Set ThresholdHilbert) :=
      Submodule.isClosed_topologicalClosure _
    apply hc.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨M, hNM, x, hx, hhead, herr⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨x, finiteSpace_mem_closedSpace_aux M x hx, ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [norm_nonneg (x - z)]
  · intro hz ε hε
    exact exists_legal_exact_head_near z hz N ε hε

/-- Every prescribed positive error budget can be met while the exact head
grows, under the actual closure criterion. There is no quantitative upper
bound on the chosen conductor schedule. -/
theorem exists_legal_exact_head_arbitrary_error_budget
    (z : ThresholdHilbert) (hz : z ∈ closedSpace)
    (budget : ℕ → ℝ) (hbudget : ∀ N, 0 < budget N) :
    ∃ support : ℕ → ℕ, ∃ x : ℕ → ThresholdHilbert,
      ∀ N, N ≤ support N ∧ x N ∈ finiteSpace (support N) ∧
        (∀ j, 0 < j → j ≤ N → hilbertSequence (x N) j = hilbertSequence z j) ∧
        ‖x N - z‖ ^ 2 < budget N := by
  classical
  have h (N : ℕ) := exists_legal_exact_head_near z hz N (budget N) (hbudget N)
  choose support hsupport x hmem hhead herr using h
  exact ⟨support, x, fun N => ⟨hsupport N, hmem N, hhead N, herr N⟩⟩


end RiemannResearch.RH.Pareto.CoefficientStabilization
