import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QAnnihilatorDilationEscape
import RiemannResearch.RH.QFloorDilationEnergy
import RiemannResearch.RH.QFullTargetTotality
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.Tactic.Ring

/-!
# Residual floor-dilation correlations with their remainder intact

Source: PQ_Density_Operators_and_RH_Agenda.pdf, agenda 3,
12 November 2026. These exact identities use arithmetic preservation of the
legal closure. The residual is not set to zero; its self-correlation survives.
-/

noncomputable section
namespace RiemannResearch.RH.QResidualDilationCorrelation
open ZetaTwoHilbert QFullResidueProjection QFloorDilation QAnnihilatorTailEscape

/-- Pairing a dilated constant against r equals the self-correlation of r. -/
theorem residual_dilation_identity (m : ℕ) (hm : 0 < m) :
    inner ℝ (floorDilation m hm qOne) actualResidual =
      inner ℝ (floorDilation m hm actualResidual) actualResidual := by
  have hz := Submodule.inner_right_of_mem_orthogonal
    (floorDilation_mem_legalClosure m hm _ (closure.starProjection_apply_mem qOne))
    actualResidual_mem_orthogonal
  change inner ℝ (floorDilation m hm qOne) actualResidual =
    inner ℝ (floorDilation m hm (qOne - closure.starProjection qOne)) actualResidual
  rw [map_sub, inner_sub_left, hz, sub_zero]

/-- Full Q norm bound, using the sharp 1/m dilation-energy estimate. -/
theorem residual_dilation_bound (m : ℕ) (hm : 0 < m) :
    |inner ℝ (floorDilation m hm qOne) actualResidual| ≤
      Real.sqrt (1 / (m : ℝ)) * ‖actualResidual‖ ^ 2 := by
  rw [residual_dilation_identity]
  calc
    _ ≤ ‖floorDilation m hm actualResidual‖ * ‖actualResidual‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (Real.sqrt (1 / (m : ℝ)) * ‖actualResidual‖) * ‖actualResidual‖ :=
      mul_le_mul_of_nonneg_right (floorDilation_norm_le_sharp m hm actualResidual)
        (norm_nonneg _)
    _ = _ := by ring

/-- Adjacent dilation correlations recover every weighted residual coordinate. -/
theorem residual_coordinate_identity (n : ℕ) :
    inner ℝ
      (floorDilation (n + 1) (Nat.succ_pos n) actualResidual -
        floorDilation (n + 2) (by omega) actualResidual) actualResidual =
      inner ℝ (lp.single 2 n (Real.sqrt (qWeight n))) actualResidual := by
  rw [inner_sub_left, ← residual_dilation_identity, ← residual_dilation_identity,
    ← inner_sub_left, QAnnihilatorDilationEscape.step_difference_single]

theorem residual_zero_iff_totality : actualResidual = 0 ↔ closure = ⊤ := by
  change qOne - closure.starProjection qOne = 0 ↔ _
  rw [sub_eq_zero]
  exact (eq_comm.trans Submodule.starProjection_eq_self_iff).trans
    QFullTargetTotality.closure_eq_top_iff_one_mem.symm

end RiemannResearch.RH.QResidualDilationCorrelation
