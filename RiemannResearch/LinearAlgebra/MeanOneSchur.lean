/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RankTwoResidualMean

/-!
# Complete scalar Schur updates on the affine mean-one constraint

The scalar `c` is the old inverse-core charge, `s` the positive ordinary
Schur complement, and `v` its mean-source mismatch. The effective constrained
Schur complement is `s + v^2/c`: its negative rank-one correction is retained.
These are finite algebraic statements. Arithmetic Gram identification, inertia,
and saturation of the limiting inverse-core charge are separate obligations.

Source: elementary scalar specialization of the user-directed complete
mean-one Schur calculation, 8 October 2026.
-/

noncomputable section
namespace RiemannResearch.LinearAlgebra.MeanOneSchur

def reducedQuadratic (c s v x : ℝ) : ℝ :=
  (2 - v * x) ^ 2 / c + s * x ^ 2

def constrainedSchur (c s v : ℝ) : ℝ := s + v ^ 2 / c

def updatedCharge (c s v : ℝ) : ℝ := c + v ^ 2 / s

def scalarOptimizer (c s v : ℝ) : ℝ := 2 * v / (c * s + v ^ 2)

def meanOneError (p c : ℝ) : ℝ := 1 + 4 * p / c

/-- Full completion; the correction `v^2/c` is negative for a negative charge. -/
theorem reducedQuadratic_completion (c s v x : ℝ)
    (hc : c ≠ 0) (hdet : c * s + v ^ 2 ≠ 0) :
    reducedQuadratic c s v x = 4 * s / (c * s + v ^ 2) +
      constrainedSchur c s v * (x - scalarOptimizer c s v) ^ 2 := by
  unfold reducedQuadratic constrainedSchur scalarOptimizer
  field_simp [hc, hdet]
  ring

theorem constrainedSchur_eq_det_div (c s v : ℝ) (hc : c ≠ 0) :
    constrainedSchur c s v = (c * s + v ^ 2) / c := by
  unfold constrainedSchur
  field_simp [hc]

theorem constrainedSchur_pos (c s v : ℝ)
    (hc : c < 0) (hdet : c * s + v ^ 2 < 0) :
    0 < constrainedSchur c s v := by
  rw [constrainedSchur_eq_det_div c s v (ne_of_lt hc)]
  exact div_pos_of_neg_of_neg hdet hc

/-- The physical update has negative old and new charges and positive ordinary
Schur complement. These assumptions imply positive constrained curvature. -/
theorem constrainedSchur_pos_of_updatedCharge_neg (c s v : ℝ)
    (hc : c < 0) (hs : 0 < s) (hnew : updatedCharge c s v < 0) :
    0 < constrainedSchur c s v := by
  apply constrainedSchur_pos c s v hc
  have hid : updatedCharge c s v * s = c * s + v ^ 2 := by
    unfold updatedCharge
    field_simp [ne_of_gt hs]
  rw [← hid]
  exact mul_neg_of_neg_of_pos hnew hs

theorem reducedQuadratic_at_optimizer (c s v : ℝ)
    (hc : c ≠ 0) (hdet : c * s + v ^ 2 ≠ 0) :
    reducedQuadratic c s v (scalarOptimizer c s v) =
      4 * s / (c * s + v ^ 2) := by
  rw [reducedQuadratic_completion c s v (scalarOptimizer c s v) hc hdet]
  simp

theorem reducedQuadratic_minimum (c s v x : ℝ)
    (hc : c < 0) (hdet : c * s + v ^ 2 < 0) :
    4 * s / (c * s + v ^ 2) ≤ reducedQuadratic c s v x := by
  rw [reducedQuadratic_completion c s v x (ne_of_lt hc) (ne_of_lt hdet)]
  exact le_add_of_nonneg_right
    (mul_nonneg (le_of_lt (constrainedSchur_pos c s v hc hdet)) (sq_nonneg _))

theorem reducedQuadratic_eq_minimum_iff (c s v x : ℝ)
    (hc : c < 0) (hdet : c * s + v ^ 2 < 0) :
    reducedQuadratic c s v x = 4 * s / (c * s + v ^ 2) ↔
      x = scalarOptimizer c s v := by
  rw [reducedQuadratic_completion c s v x (ne_of_lt hc) (ne_of_lt hdet)]
  have heff : 0 < constrainedSchur c s v := constrainedSchur_pos c s v hc hdet
  constructor
  · intro h
    have hprod : constrainedSchur c s v * (x - scalarOptimizer c s v) ^ 2 = 0 := by
      linarith only [h]
    have hsquare : (x - scalarOptimizer c s v) ^ 2 = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt heff)
    nlinarith only [hsquare]
  · intro h
    rw [h]
    simp

/-- Exact gain with the complete constrained Schur denominator. -/
theorem meanOneError_gain (p c s v : ℝ)
    (hc : c ≠ 0) (hs : s ≠ 0) (hdet : c * s + v ^ 2 ≠ 0) :
    meanOneError p c - meanOneError p (updatedCharge c s v) =
      4 * p * v ^ 2 / (c * (c * s + v ^ 2)) := by
  have hnew : updatedCharge c s v ≠ 0 := by
    intro h
    apply hdet
    have hid : updatedCharge c s v * s = c * s + v ^ 2 := by
      unfold updatedCharge
      field_simp [hs]
    rw [h, zero_mul] at hid
    exact hid.symm
  unfold meanOneError updatedCharge at *
  field_simp [hc, hs, hdet, hnew]
  ring

theorem updatedCharge_mono (c s v : ℝ) (hs : 0 < s) :
    c ≤ updatedCharge c s v := by
  unfold updatedCharge
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg v) (le_of_lt hs))

theorem updatedCharge_strict_mono (c s v : ℝ)
    (hs : 0 < s) (hv : v ≠ 0) : c < updatedCharge c s v := by
  unfold updatedCharge
  exact lt_add_of_pos_right c (div_pos (sq_pos_of_ne_zero hv) hs)

/-- A finite lower error obstruction implies a quantitatively stronger charge
bound. An application may take `w` to be the complete mass of common-period
sites, or a finite prefix of that mass. -/
theorem inverseCharge_bound_of_error_lower (p gamma w : ℝ)
    (hgamma : 0 < gamma) (hw : w < 1)
    (herr : w ≤ 1 - 4 * p / gamma) :
    4 * p / (1 - w) ≤ gamma := by
  apply (div_le_iff₀ (sub_pos.mpr hw)).2
  have hfrac : 4 * p / gamma ≤ 1 - w := by linarith only [herr]
  have hmul := (div_le_iff₀ hgamma).1 hfrac
  nlinarith only [hmul]

theorem inverseCharge_strict_boundary (p gamma w : ℝ)
    (_hp : 0 < p) (hgamma : 0 < gamma) (hw0 : 0 < w) (hw1 : w < 1)
    (herr : w ≤ 1 - 4 * p / gamma) : 4 * p < gamma := by
  have hb := inverseCharge_bound_of_error_lower p gamma w hgamma hw1 herr
  have hmul := (div_le_iff₀ (sub_pos.mpr hw1)).1 hb
  nlinarith only [hmul, mul_pos hgamma hw0]

/-- The unconstrained gain retains both signed endpoint penalties. -/
theorem complete_gain_of_mean_penalties
    (eOld eNew eMeanOld eMeanNew penaltyOld penaltyNew : ℝ)
    (hOld : eOld = eMeanOld - penaltyOld)
    (hNew : eNew = eMeanNew - penaltyNew) :
    eOld - eNew = eMeanOld - eMeanNew - penaltyOld + penaltyNew := by
  rw [hOld, hNew]
  ring

/-- The arithmetic feedback provider is an explicit hypothesis. When
`0 < theta < 1`, the resulting inequality is a strict gap contraction. -/
theorem boundary_gap_contraction
    (boundary gamma gammaNew drop theta : ℝ)
    (hupdate : gammaNew = gamma - drop)
    (hfeedback : theta * (gamma - boundary) ≤ drop) :
    gammaNew - boundary ≤ (1 - theta) * (gamma - boundary) := by
  rw [hupdate]
  nlinarith only [hfeedback]

/-- The exact core drop gives the complete constrained error gain. Positivity
of the charges or drop can be supplied separately when an order bound is needed. -/
theorem meanOneError_gain_of_positive_charges
    (p gamma gammaNew drop : ℝ)
    (hgamma : gamma ≠ 0) (hgammaNew : gammaNew ≠ 0)
    (hupdate : gammaNew = gamma - drop) :
    (1 - 4 * p / gamma) - (1 - 4 * p / gammaNew) =
      4 * p * drop / (gamma * gammaNew) := by
  have hdrop : drop = gamma - gammaNew := by linarith only [hupdate]
  rw [hdrop]
  field_simp [hgamma, hgammaNew]
  ring

end RiemannResearch.LinearAlgebra.MeanOneSchur
