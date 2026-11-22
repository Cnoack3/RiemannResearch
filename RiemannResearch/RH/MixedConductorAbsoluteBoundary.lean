import RiemannResearch.RH.MixedConductorGramZeroFree
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.ParetoParityPeriodSection

/-!
# The absolute value of the screened section and the ambient boundary

The physical absolute value is taken in the ambient Pareto sequence space.
Its pairing with the legal projection residual is an exact sum of two
nonnegative quantities. Thus a single scalar sign, or closure of the legal
space under absolute value just at the screened vector, implies that the
constant belongs to the legal space.
-/

noncomputable section
open scoped BigOperators Matrix
namespace RiemannResearch.RH.Pareto.PrimePowerSchur

open CoefficientStabilization

private theorem abs_constant : hilbertAbs hilbertOne = hilbertOne := by
  apply hilbertSequence_injective
  funext k
  rw [hilbertAbs_sequence, hilbertOne_sequence]
  by_cases hk : k = 0 <;> simp [zeroAnchor, hk]

/-- The legal span on conductors two and three fails to be closed under physical absolute value. -/
theorem exists_two_stage_abs_outside :
    ∃ v : ThresholdHilbert, v ∈ finiteSpace 2 ∧ hilbertAbs v ∉ finiteSpace 2 := by
  have hrow (w : ThresholdHilbert) (hw : w ∈ finiteSpace 2) :
      2 * hilbertSequence w 1 = hilbertSequence w 2 + 2 * hilbertSequence w 3 := by
    obtain ⟨b, rfl⟩ := finiteSpace_expansion 2 w hw
    rw [hilbertSequence_sum_residueAtom]
    norm_num [finiteResidueProfile, Fin.sum_univ_two, ArithmeticCumulative.residueFraction]
    <;> ring
  let a : Fin 2 → ℝ := ![2, -3]
  let v := ∑ i : Fin 2, a i • residueAtom i.val
  have hv : v ∈ finiteSpace 2 := by
    change (∑ i : Fin 2, a i • residueAtom i.val) ∈
      Submodule.span ℝ (Set.range (fun i : Fin 2 => residueAtom i.val))
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩))
  refine ⟨v, hv, fun ha => ?_⟩
  have h := hrow _ ha
  have hvseq : hilbertSequence v = finiteResidueProfile a := hilbertSequence_sum_residueAtom a
  rw [hilbertAbs_sequence, hvseq] at h
  norm_num [a, finiteResidueProfile, Fin.sum_univ_two, ArithmeticCumulative.residueFraction] at h

/-- The exact pairing measures both the weighted mass and squared norm of the negative part. -/
theorem abs_screened_residual_pairing :
    inner ℝ (hilbertAbs normalizedScreenedTwo) limitResidual =
      2 * hilbertNegativeMass normalizedScreenedTwo +
      ((1 - limitEnergy) / 2) * ‖hilbertAbs normalizedScreenedTwo - normalizedScreenedTwo‖^2 := by
  rw [limitResidual, inner_sub_right, limitProjection_eq_scaled_screenedTwo, real_inner_smul_right,
    hilbertNegativeMass_eq, normalizedScreenedTwo_mean, ← hilbertL1Norm_eq_inner_abs,
    norm_sub_sq_real, hilbertAbs_norm]
  nlinarith only [normalizedScreenedTwo_energy_product]

/-- Every legal trial has an explicit lower bound for its distance to the absolute value. -/
theorem negative_mass_le_abs_legal_distance (v : ThresholdHilbert) (hv : v ∈ closedSpace) :
    2 * hilbertNegativeMass normalizedScreenedTwo +
      ((1 - limitEnergy) / 2) * ‖hilbertAbs normalizedScreenedTwo - normalizedScreenedTwo‖^2 ≤
        ‖hilbertAbs normalizedScreenedTwo - v‖ * ‖limitResidual‖ := by
  have hv0 := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal v hv
  have h := real_inner_le_norm (hilbertAbs normalizedScreenedTwo - v) limitResidual
  rwa [inner_sub_left, hv0, sub_zero, abs_screened_residual_pairing] at h

/-- One scalar sign determines whether the screened vector is the constant. -/
theorem screened_eq_one_iff_abs_pairing_nonpos :
    normalizedScreenedTwo = hilbertOne ↔
      inner ℝ (hilbertAbs normalizedScreenedTwo) limitResidual ≤ 0 := by
  constructor
  · intro hu
    have hv := screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
    rw [hu] at hv ⊢
    rw [abs_constant]
    exact ((closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hv).le
  · intro h
    rw [abs_screened_residual_pairing] at h
    have hh : ‖hilbertAbs normalizedScreenedTwo - normalizedScreenedTwo‖^2 = 0 := by
      by_contra hn
      have hp := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
      have hpos := mul_pos (half_pos one_sub_limitEnergy_pos) hp
      linarith only [h, hpos, hilbertNegativeMass_nonneg normalizedScreenedTwo]
    have hn : ‖hilbertAbs normalizedScreenedTwo - normalizedScreenedTwo‖ = 0 := by
      nlinarith only [hh]
    have he := sub_eq_zero.mp (norm_eq_zero.mp hn)
    apply normalizedScreenedTwo_eq_one_of_oneSidedBound
    refine Or.inl ⟨0, fun k _ => ?_⟩
    have hk := congrArg (fun f : ThresholdHilbert => hilbertSequence f k) he
    rw [hilbertAbs_sequence] at hk
    exact hk ▸ abs_nonneg (hilbertSequence normalizedScreenedTwo k)

/-- It suffices to preserve the absolute value of this one legal vector. -/
theorem abs_screened_mem_iff_boundary_zero :
    hilbertAbs normalizedScreenedTwo ∈ closedSpace ↔ CenteredMeanSnake.boundary = 0 := by
  constructor
  · intro hv
    exact CenteredMeanSnake.boundary_eq_zero_iff_screened.mpr
      (screened_eq_one_iff_abs_pairing_nonpos.mpr
        ((closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hv).le)
  · intro hb
    have hu := CenteredMeanSnake.boundary_eq_zero_iff_screened.mp hb
    rw [hu, abs_constant]
    exact CenteredMeanSnake.boundary_eq_zero_iff_one_mem.mp hb

/-- The sign of the projected constant at each positive physical site characterizes the boundary. -/
theorem boundary_zero_iff_projected_one_nonnegative :
    CenteredMeanSnake.boundary = 0 ↔ ∀ k : ℕ, 0 < k → 0 ≤ hilbertSequence limitProjection k := by
  constructor
  · intro hb k hk
    have hu := CenteredMeanSnake.boundary_eq_zero_iff_screened.mp hb
    rw [limitProjection_eq_scaled_screenedTwo, ← anchoredEvaluationCLM_apply, map_smul,
      smul_eq_mul, anchoredEvaluationCLM_apply, hu, hilbertOne_sequence]
    simpa [zeroAnchor, hk.ne'] using one_sub_limitEnergy_pos.le
  · intro hv
    apply CenteredMeanSnake.boundary_eq_zero_iff_screened.mpr
    apply normalizedScreenedTwo_eq_one_of_oneSidedBound
    refine Or.inl ⟨0, fun k hk => ?_⟩
    have h := hv k hk
    rw [limitProjection_eq_scaled_screenedTwo, ← anchoredEvaluationCLM_apply, map_smul,
      smul_eq_mul, anchoredEvaluationCLM_apply] at h
    exact (mul_nonneg_iff_of_pos_left one_sub_limitEnergy_pos).mp h

theorem riemannHypothesis_of_abs_screened_mem (h : hilbertAbs normalizedScreenedTwo ∈ closedSpace) :
    RiemannHypothesis :=
  CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero (abs_screened_mem_iff_boundary_zero.mp h)

end RiemannResearch.RH.Pareto.PrimePowerSchur
