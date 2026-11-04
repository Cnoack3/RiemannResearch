/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GramSchmidtCofactors
import RiemannResearch.RH.ZetaTwoParitySignal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact first Q residue normalization

The existing full-Q parity norm gives the first Gram--Schmidt scale and
triangular diagonal exactly. The source is the user's triangular-matrix
verification request, 4 November 2026. No numerical quadrature is used.
-/

noncomputable section
namespace RiemannResearch.RH.QResidueFirstNormalization

open InnerProductSpace ZetaTwoHilbert ZetaTwoParitySignal
open RiemannResearch.Analysis.GramSchmidtCofactors

theorem qResidue_two_norm_sq : ‖qResidue 2‖ ^ 2 = (3 / 16 : ℝ) := by
  have h := qOdd_norm_sq
  norm_num [qOdd, norm_smul] at h
  nlinarith

theorem qResidue_two_norm : ‖qResidue 2‖ = Real.sqrt 3 / 4 := by
  have h := qResidue_two_norm_sq
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [norm_nonneg (qResidue 2), Real.sqrt_nonneg (3 : ℝ)]

theorem first_scale (v : ℕ → QHilbert) (hv0 : v 0 = qResidue 2) :
    scale v 0 = Real.sqrt 3 / 4 := by
  change ‖gramSchmidt ℝ v (⊥ : ℕ)‖ = _
  rw [gramSchmidt_bot]
  change ‖v 0‖ = _
  rw [hv0, qResidue_two_norm]

theorem first_coefficient {v : ℕ → QHilbert} (hv : LinearIndependent ℝ v)
    (hv0 : v 0 = qResidue 2) :
    coefficient v 0 (Fin.last 0) = 4 / Real.sqrt 3 := by
  have h := coefficient_diagonal_mul_scale hv 0
  rw [first_scale v hv0] at h
  apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)))).mpr
  nlinarith

theorem first_mode (v : ℕ → QHilbert) (hv0 : v 0 = qResidue 2) :
    mode v 0 = (4 / Real.sqrt 3) • qResidue 2 := by
  change (scale v 0)⁻¹ • gramSchmidt ℝ v (⊥ : ℕ) = _
  rw [first_scale v hv0, gramSchmidt_bot]
  change (Real.sqrt 3 / 4)⁻¹ • v 0 = _
  rw [hv0]
  congr 1
  field_simp

end RiemannResearch.RH.QResidueFirstNormalization
