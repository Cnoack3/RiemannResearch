/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.TriangularCoefficientBounds
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QConductorLimits
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Q residue normalization bounds

Source: the user's triangular-matrix request, 4 November 2026.
Reuses the existing full-Q conductor norm bound, including its entire tail.
-/

noncomputable section
open Filter InnerProductSpace
open scoped Topology

namespace RiemannResearch.RH.QResidueNormalizationBounds

open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.TriangularCoefficientBounds

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- The exact reciprocal innovation scale has the claimed conductor lower bound. -/
theorem inverse_scale_lower (d : ι → ℕ) (j : ι) (hd : 2 ≤ d j)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) :
    Real.sqrt (zetaTwo * (d j : ℝ) / 2) ≤
      (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹ := by
  have hZ := zetaTwo_pos
  have hdR : (0 : ℝ) < d j := by exact_mod_cast (by omega : 0 < d j)
  have hs : 0 < ‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖ :=
    norm_pos_iff.mpr (gramSchmidt_ne_zero j hv)
  have hsmall : ‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖ ≤
      Real.sqrt (2 / (zetaTwo * (d j : ℝ))) :=
    (norm_gramSchmidt_le _ j).trans
      (Real.le_sqrt_of_sq_le (qResidue_norm_sq_le_two_div (d j) hd))
  have hprod : Real.sqrt (zetaTwo * (d j : ℝ) / 2) *
      Real.sqrt (2 / (zetaTwo * (d j : ℝ))) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ zetaTwo * (d j : ℝ) / 2)]
    have he : (zetaTwo * (d j : ℝ) / 2) *
        (2 / (zetaTwo * (d j : ℝ))) = 1 := by
      field_simp [ne_of_gt hZ, ne_of_gt hdR]
    rw [he, Real.sqrt_one]
  rw [← one_div]
  apply (le_div_iff₀ hs).mpr
  calc
    _ ≤ Real.sqrt (zetaTwo * (d j : ℝ) / 2) *
        Real.sqrt (2 / (zetaTwo * (d j : ℝ))) :=
      mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _)
    _ = 1 := hprod

/-- Positive reciprocal scales diverge whenever the conductors escape to infinity. -/
theorem inverse_scale_tendsto_atTop (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) :
    Tendsto (fun j => (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹)
      atTop atTop := by
  have hn : Tendsto (fun j => ‖qResidue (d j)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (qResidue_tendsto_zero d hd).norm
  apply tendsto_atTop.mpr
  intro b
  let M : ℝ := max b 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he := hn.eventually (gt_mem_nhds (one_div_pos.mpr hM))
  filter_upwards [he] with j hj
  have hs : 0 < ‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖ :=
    norm_pos_iff.mpr (gramSchmidt_ne_zero j hv)
  have hsmall : ‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖ < 1 / M :=
    lt_of_le_of_lt (norm_gramSchmidt_le _ j) hj
  have hmul : M * ‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖ < 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hM).mp hsmall
  have hi : M < (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹ := by
    rw [← one_div]
    exact (lt_div_iff₀ hs).mpr hmul
  exact (le_max_left b 1).trans hi.le

/-- Application to the standard l2 coefficient matrix, using its proved diagonal formula. -/
theorem no_bounded_normalization_matrix (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (A : ℕ → ℕ → ℝ)
    (hdiag : ∀ j, A j j = (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹) :
    ¬ ∃ T : Coefficients →L[ℝ] Coefficients,
      ∀ i j, (T (coordinateUnit j)) i = A i j := by
  apply no_bounded_matrix_columns A
  simpa only [hdiag] using inverse_scale_tendsto_atTop d hd hv

/-- A separate physical-space obstruction: a bounded Q operator cannot normalize all escaping atoms. -/
theorem no_continuous_atom_normalizer (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i))) :
    ¬ ∃ T : QHilbert →L[ℝ] QHilbert,
      ∀ j, T (qResidue (d j)) = gramSchmidtNormed ℝ (fun i => qResidue (d i)) j := by
  rintro ⟨T, hT⟩
  have ht := (T.continuous.tendsto 0).comp (qResidue_tendsto_zero d hd)
  have hn : Tendsto (fun j => ‖T (qResidue (d j))‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, map_zero, norm_zero] using ht.norm
  have hone : (fun j => ‖T (qResidue (d j))‖) = fun _ => (1 : ℝ) := by
    funext j
    rw [hT j, gramSchmidtNormed_unit_length j hv]
  rw [hone] at hn
  have hz : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
  norm_num at hz

end RiemannResearch.RH.QResidueNormalizationBounds
