import RiemannResearch.RH.ThresholdJointAdjointRigidity
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.GibbsLegalSeed
import RiemannResearch.RH.MertensBaezDuarteConverse
import RiemannResearch.RH.ParetoDensityDilation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two adjoints, actual residual defects, and the RH boundary

Source: the user's dilation discussion, 14 November 2026.
The new equivalences with full residue density are unconditional, using
the existing two/three adjoint rigidity theorem. The RH implication is
unconditional. The reverse implication retains BaezDuarteMobiusApproximation,
the repository's explicitly unformalized published analytic provider.
Reference: Bagchi, Theorem 1, https://arxiv.org/abs/math/0607733 (density
criterion); Xue, Corollary 1.5, https://arxiv.org/abs/1911.04029 (the
all-integer adjoint-invariance criterion). The two-adjoint reduction uses
the existing repository rigidity theorem, rather than assuming it.
Stage n contains g_2 through g_(n+1), in the complete Pareto norm.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.DilationAdjointCriterion
open CoefficientStabilization
open RiemannResearch.RH.ParetoDensityDilation

private theorem atom_mem (i : ℕ) : residueAtom i ∈ closedSpace :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem atom_zero_mean_pos : 0 < inner ℝ (residueAtom 0) hilbertOne := by
  change 0 < inner ℝ ((1 / (2 : ℝ)) • digitHilbert 2 1 (by norm_num) (by norm_num))
    hilbertOne
  rw [inner_smul_left, hilbert_mean_digit_two]
  norm_num
  exact Real.log_pos (by norm_num)

/-- A genuine fixed-point criterion for the actual limiting residual. -/
theorem residual_zero_iff_two_adjoint_fixed :
    limitResidual = 0 ↔
      hilbertDilationAdjoint 2 (by norm_num) limitResidual = limitResidual ∧
      hilbertDilationAdjoint 3 (by norm_num) limitResidual = limitResidual := by
  constructor
  · intro h
    simp [h]
  · intro h
    obtain ⟨c, hc⟩ := (hilbertDilationAdjoint_two_three_fixed_iff limitResidual).mp h
    have ho := Submodule.inner_right_of_mem_orthogonal (atom_mem 0)
      limitResidual_mem_orthogonal
    rw [hc, inner_smul_right] at ho
    have hc0 : c = 0 := (mul_eq_zero.mp ho).resolve_right (ne_of_gt atom_zero_mean_pos)
    simpa only [hc0, zero_smul] using hc

def AdjointInvariant (m : ℕ) (hm : 0 < m) : Prop :=
  ∀ f ∈ closedSpace, hilbertDilationAdjoint m hm f ∈ closedSpace

/-- Only the adjoint image of the fitted constant is needed at this scale. -/
theorem residual_fixed_of_projection_adjoint_mem (m : ℕ) (hm : 0 < m)
    (hmem : hilbertDilationAdjoint m hm limitProjection ∈ closedSpace) :
    hilbertDilationAdjoint m hm limitResidual = limitResidual := by
  have hd : hilbertDilationAdjoint m hm limitResidual ∈ closedSpaceᗮ := by
    apply (closedSpace.mem_orthogonal _).mpr
    intro f hf
    change inner ℝ f ((hilbertDilationContinuous m hm).adjoint limitResidual) = 0
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.inner_right_of_mem_orthogonal (closedSpace_dilation hf m hm)
      limitResidual_mem_orthogonal
  have horth := closedSpaceᗮ.sub_mem hd limitResidual_mem_orthogonal
  have hlegal : hilbertDilationAdjoint m hm limitResidual - limitResidual ∈ closedSpace := by
    have he : hilbertDilationAdjoint m hm limitResidual - limitResidual =
        limitProjection - hilbertDilationAdjoint m hm limitProjection := by
      rw [limitResidual, map_sub, hilbertDilationAdjoint_one]
      abel
    rw [he]
    exact closedSpace.sub_mem (closedSpace.starProjection_apply_mem hilbertOne) hmem
  have hz := Submodule.inner_right_of_mem_orthogonal hlegal horth
  rw [real_inner_self_eq_norm_sq] at hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem totality_iff_two_projection_adjoint_mem :
    closedSpace = ⊤ ↔
      hilbertDilationAdjoint 2 (by norm_num) limitProjection ∈ closedSpace ∧
      hilbertDilationAdjoint 3 (by norm_num) limitProjection ∈ closedSpace := by
  constructor
  · intro h
    simp [h]
  · rintro ⟨h2, h3⟩
    have hz := residual_zero_iff_two_adjoint_fixed.mpr
      ⟨residual_fixed_of_projection_adjoint_mem 2 (by norm_num) h2,
        residual_fixed_of_projection_adjoint_mem 3 (by norm_num) h3⟩
    exact closedSpace_eq_top_iff_one_mem.mpr
      (limitEnergy_zero_iff_mem.mp (limitResidual_zero_iff_energy_zero.mp hz))

theorem totality_iff_two_adjoint_invariant :
    closedSpace = ⊤ ↔
      AdjointInvariant 2 (by norm_num) ∧ AdjointInvariant 3 (by norm_num) := by
  constructor
  · intro h
    simp [AdjointInvariant, h]
  · rintro ⟨h2, h3⟩
    exact totality_iff_two_projection_adjoint_mem.mpr
      ⟨h2 _ (closedSpace.starProjection_apply_mem hilbertOne),
        h3 _ (closedSpace.starProjection_apply_mem hilbertOne)⟩

theorem normalized_adjoint_apply (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    (normalizedP m hm).adjoint f =
      (1 / Real.sqrt (m : ℝ)) • hilbertDilationAdjoint m hm f := by
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((1 / Real.sqrt (m : ℝ)) • hilbertDilation m hm g) f = _
  rw [inner_smul_left, inner_smul_right]
  congr 1
  exact (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous m hm) g f).symm

theorem normalized_adjoint_invariant_iff (m : ℕ) (hm : 0 < m) :
    (∀ f ∈ closedSpace, (normalizedP m hm).adjoint f ∈ closedSpace) ↔
      AdjointInvariant m hm := by
  have hs : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hm))
  constructor
  · intro h f hf
    have hh := closedSpace.smul_mem (Real.sqrt (m : ℝ)) (h f hf)
    rw [normalized_adjoint_apply, smul_smul, mul_one_div_cancel hs, one_smul] at hh
    exact hh
  · intro h f hf
    rw [normalized_adjoint_apply]
    exact closedSpace.smul_mem _ (h f hf)

/-- The normalized U_2 and U_3 version of the exact density criterion. -/
theorem totality_iff_two_normalized_adjoint_invariant :
    closedSpace = ⊤ ↔
      (∀ f ∈ closedSpace, (normalizedP 2 (by norm_num)).adjoint f ∈ closedSpace) ∧
      (∀ f ∈ closedSpace, (normalizedP 3 (by norm_num)).adjoint f ∈ closedSpace) := by
  rw [normalized_adjoint_invariant_iff, normalized_adjoint_invariant_iff]
  exact totality_iff_two_adjoint_invariant

def finiteResidual (n : ℕ) : ThresholdHilbert := hilbertOne - projection n

def defectNormSum (f : ThresholdHilbert) : ℝ :=
  ‖hilbertDilationAdjoint 2 (by norm_num) f - f‖ +
    ‖hilbertDilationAdjoint 3 (by norm_num) f - f‖

theorem finiteResidual_tendsto :
    Tendsto finiteResidual atTop (𝓝 limitResidual) :=
  tendsto_const_nhds.sub projection_tendsto

theorem defectNormSum_tendsto :
    Tendsto (fun n => defectNormSum (finiteResidual n)) atTop
      (𝓝 (defectNormSum limitResidual)) := by
  have h2 := (((hilbertDilationAdjoint 2 (by norm_num)).continuous.tendsto limitResidual).comp
    finiteResidual_tendsto).sub finiteResidual_tendsto
  have h3 := (((hilbertDilationAdjoint 3 (by norm_num)).continuous.tendsto limitResidual).comp
    finiteResidual_tendsto).sub finiteResidual_tendsto
  exact h2.norm.add h3.norm

theorem defectNormSum_zero_iff (f : ThresholdHilbert) :
    defectNormSum f = 0 ↔
      hilbertDilationAdjoint 2 (by norm_num) f = f ∧
      hilbertDilationAdjoint 3 (by norm_num) f = f := by
  unfold defectNormSum
  rw [add_eq_zero_iff_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [norm_eq_zero, sub_eq_zero]

theorem totality_iff_residual_defects_tendsto_zero :
    closedSpace = ⊤ ↔
      Tendsto (fun n => defectNormSum (finiteResidual n)) atTop (𝓝 0) := by
  have ht : closedSpace = ⊤ ↔ limitResidual = 0 :=
    closedSpace_eq_top_iff_one_mem.trans
      (limitEnergy_zero_iff_mem.symm.trans limitResidual_zero_iff_energy_zero.symm)
  rw [ht, residual_zero_iff_two_adjoint_fixed, ← defectNormSum_zero_iff]
  constructor
  · intro h
    simpa only [h] using defectNormSum_tendsto
  · intro h
    exact tendsto_nhds_unique defectNormSum_tendsto h

theorem riemannHypothesis_of_two_adjoint_invariant
    (h2 : AdjointInvariant 2 (by norm_num)) (h3 : AdjointInvariant 3 (by norm_num)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n} (fun _ hn => hn)
  apply closedSpace_le_legalClosure
  rw [totality_iff_two_adjoint_invariant.mpr ⟨h2, h3⟩]
  trivial


theorem riemannHypothesis_of_two_normalized_adjoint_invariant
    (h2 : ∀ f ∈ closedSpace, (normalizedP 2 (by norm_num)).adjoint f ∈ closedSpace)
    (h3 : ∀ f ∈ closedSpace, (normalizedP 3 (by norm_num)).adjoint f ∈ closedSpace) :
    RiemannHypothesis :=
  riemannHypothesis_of_two_adjoint_invariant
    ((normalized_adjoint_invariant_iff 2 (by norm_num)).mp h2)
    ((normalized_adjoint_invariant_iff 3 (by norm_num)).mp h3)

theorem riemannHypothesis_of_two_projection_adjoint_mem
    (h2 : hilbertDilationAdjoint 2 (by norm_num) limitProjection ∈ closedSpace)
    (h3 : hilbertDilationAdjoint 3 (by norm_num) limitProjection ∈ closedSpace) :
    RiemannHypothesis := by
  have ht := totality_iff_two_projection_adjoint_mem.mpr ⟨h2, h3⟩
  exact riemannHypothesis_of_two_adjoint_invariant
    (totality_iff_two_adjoint_invariant.mp ht).1
    (totality_iff_two_adjoint_invariant.mp ht).2

theorem riemannHypothesis_of_residual_defects_tendsto_zero
    (h : Tendsto (fun n => defectNormSum (finiteResidual n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have ht := totality_iff_residual_defects_tendsto_zero.mpr h
  exact riemannHypothesis_of_two_adjoint_invariant
    (totality_iff_two_adjoint_invariant.mp ht).1
    (totality_iff_two_adjoint_invariant.mp ht).2

private theorem squarefree_le_closedSpace : squarefreeCRTSpan ≤ closedSpace := by
  rw [squarefreeCRTSpan_eq_span]
  apply Submodule.span_le.mpr
  rintro f ⟨d, rfl⟩
  have hd : 2 ≤ (d : ℕ) := d.property.1
  refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(d : ℕ) - 2, ?_⟩)
  simp only [residueAtom, Nat.sub_add_cancel hd]

/-- The published RH-to-density implication is kept as an explicit provider. -/
theorem riemannHypothesis_iff_totality
    (hBD : BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ closedSpace = ⊤ := by
  constructor
  · intro hRH
    apply closedSpace_eq_top_iff_one_mem.mpr
    exact (Submodule.topologicalClosure_minimal _ squarefree_le_closedSpace
      (Submodule.isClosed_topologicalClosure _))
      (BaezDuarte.squarefreeClosure_of_baezDuarteMobiusApproximation hBD hRH)
  · intro h
    exact riemannHypothesis_of_two_adjoint_invariant
      (totality_iff_two_adjoint_invariant.mp h).1
      (totality_iff_two_adjoint_invariant.mp h).2


theorem riemannHypothesis_iff_two_adjoint_invariant
    (hBD : BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔
      AdjointInvariant 2 (by norm_num) ∧ AdjointInvariant 3 (by norm_num) :=
  (riemannHypothesis_iff_totality hBD).trans totality_iff_two_adjoint_invariant

theorem riemannHypothesis_iff_two_projection_adjoint_mem
    (hBD : BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔
      hilbertDilationAdjoint 2 (by norm_num) limitProjection ∈ closedSpace ∧
      hilbertDilationAdjoint 3 (by norm_num) limitProjection ∈ closedSpace :=
  (riemannHypothesis_iff_totality hBD).trans totality_iff_two_projection_adjoint_mem

theorem riemannHypothesis_iff_two_normalized_adjoint_invariant
    (hBD : BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔
      (∀ f ∈ closedSpace, (normalizedP 2 (by norm_num)).adjoint f ∈ closedSpace) ∧
      (∀ f ∈ closedSpace, (normalizedP 3 (by norm_num)).adjoint f ∈ closedSpace) :=
  (riemannHypothesis_iff_totality hBD).trans totality_iff_two_normalized_adjoint_invariant

theorem riemannHypothesis_iff_residual_defects_tendsto_zero
    (hBD : BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔
      Tendsto (fun n => defectNormSum (finiteResidual n)) atTop (𝓝 0) :=
  (riemannHypothesis_iff_totality hBD).trans totality_iff_residual_defects_tendsto_zero

#print axioms totality_iff_two_normalized_adjoint_invariant
#print axioms riemannHypothesis_of_residual_defects_tendsto_zero
#print axioms riemannHypothesis_iff_residual_defects_tendsto_zero

end RiemannResearch.RH.Pareto.DilationAdjointCriterion
