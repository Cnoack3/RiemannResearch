/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MellinModeOrthonormality
import RiemannResearch.RH.ParetoHorizontalZeroBridge
import Mathlib.Tactic.Ring

/-!
# Exact boundary Plancherel energy of actual finite Pareto residuals

Source: the user's paper-first continuation, 11 October 2026. The existing
`MellinModeOrthonormality` supplies the actual ordinary Fourier / Mellin
substitution and the L1/L2 boundary representative for bounded sequences.
The existing actual logarithmic isometry supplies Plancherel. All signs,
cross terms and the complete physical norm are retained.

This module proves the boundary integral of the literal actual residual
Mellin transform. The sibling `ParetoFiniteMellinHalfPlane` extends the finite
signed transform identity to Re(s)>0 and supplies its explicit critical-line
zeta numerator, without adding an analytic premise.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators

namespace RiemannResearch.RH.ParetoResidualBoundaryEnergy

open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoHorizontalZeroBridge

theorem paretoMellinLogFourier_integral_energy (f : ThresholdHilbert) :
    (∫ ξ, ‖paretoMellinLogFourier f ξ‖ ^ 2) = ‖f‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ)
    (paretoMellinLogFourier f) (paretoMellinLogFourier f)
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  have hn : ‖paretoMellinLogFourier f‖ = ‖f‖ := by
    change ‖𝓕 (paretoMellinLogLp f)‖ = ‖f‖
    rw [Lp.norm_fourier_eq, paretoMellinLogLp_norm]
  rw [hn] at h
  exact h.symm

/-- Actual boundary Mellin Plancherel, with exact angular density 1/(2π).
Boundedness ensures the literal convergent Mellin integral represents the
L2 boundary function; it is not a desired energy-equality premise. -/
theorem paretoMellin_boundary_energy_of_bounded (f : ThresholdHilbert)
    {C : ℝ} (hC : ∀ k, |hilbertSequence f k| ≤ C) :
    (1 / (2 * Real.pi) : ℝ) *
      (∫ t, ‖paretoMellin f (MellinFrequency.criticalPoint t)‖ ^ 2) = ‖f‖ ^ 2 := by
  have hae := paretoMellinLogFourier_ae_eq_of_bounded f hC
  have hordinary :
      (∫ ξ, ‖paretoMellin f
        (MellinFrequency.criticalPoint (2 * Real.pi * ξ))‖ ^ 2) = ‖f‖ ^ 2 := by
    calc
      _ = ∫ ξ, ‖paretoMellinLogFourier f ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hae] with ξ hξ
        rw [hξ]
      _ = _ := paretoMellinLogFourier_integral_energy f
  have hs := Measure.integral_comp_mul_left
    (fun t => ‖paretoMellin f (MellinFrequency.criticalPoint t)‖ ^ 2)
    (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [abs_of_pos (inv_pos.mpr hpi)] at hs
  simpa only [one_div, smul_eq_mul] using hs.symm.trans hordinary

theorem finiteResidueCandidate_sequence_bound
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) (k : ℕ) :
    |hilbertSequence (finiteResidueCandidate D c) k| ≤ ∑ d ∈ D, |c d| := by
  have hseq : hilbertSequence (finiteResidueCandidate D c) k =
      ∑ d ∈ D, c d * hilbertSequence
        (normalizedResidueHilbert d.1 (by omega)) k := by
    change hilbertSequenceLinear
      (∑ d ∈ D, c d • normalizedResidueHilbert d.1 (by omega)) k = _
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hseq]
  calc
    _ ≤ ∑ d ∈ D, |c d * hilbertSequence
        (normalizedResidueHilbert d.1 (by omega)) k| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le D
        (fun d => c d * hilbertSequence (normalizedResidueHilbert d.1 (by omega)) k)
    _ ≤ ∑ d ∈ D, |c d| := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, normalizedResidueHilbert_sequence]
      exact (mul_le_mul_of_nonneg_left
        (normalizedAtom_abs_le_one d.1 k (by omega)) (abs_nonneg (c d))).trans_eq
          (mul_one _)

theorem hilbertOne_sequence_bound (k : ℕ) : |hilbertSequence hilbertOne k| ≤ 1 := by
  rw [hilbertOne_sequence]
  by_cases hk : k = 0 <;> simp [zeroAnchor, hk]

theorem finiteResidueError_sequence_bound
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) (k : ℕ) :
    |hilbertSequence (hilbertOne - finiteResidueCandidate D c) k| ≤
      1 + ∑ d ∈ D, |c d| := by
  have hseq : hilbertSequence (hilbertOne - finiteResidueCandidate D c) k =
      hilbertSequence hilbertOne k - hilbertSequence (finiteResidueCandidate D c) k := by
    change hilbertSequenceLinear (hilbertOne - finiteResidueCandidate D c) k = _
    rw [map_sub]
    rfl
  rw [hseq]
  have htriangle :
      |hilbertSequence hilbertOne k - hilbertSequence (finiteResidueCandidate D c) k| ≤
        |hilbertSequence hilbertOne k| + |hilbertSequence (finiteResidueCandidate D c) k| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le
      (hilbertSequence hilbertOne k) (hilbertSequence (finiteResidueCandidate D c) k)
  exact htriangle.trans (add_le_add (hilbertOne_sequence_bound k)
    (finiteResidueCandidate_sequence_bound D c k))

/-- Every finite legal signed candidate has the exact actual residual
boundary energy, without a regularity provider premise. -/
theorem finiteResidueError_boundary_energy
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    (1 / (2 * Real.pi) : ℝ) *
      (∫ t, ‖paretoMellin (hilbertOne - finiteResidueCandidate D c)
        (MellinFrequency.criticalPoint t)‖ ^ 2) =
      ‖hilbertOne - finiteResidueCandidate D c‖ ^ 2 :=
  paretoMellin_boundary_energy_of_bounded _ (finiteResidueError_sequence_bound D c)

/-- The signed target cross term and the full candidate square are both
retained as an exact equality. -/
theorem finiteResidueError_boundary_energy_cross_terms
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    (1 / (2 * Real.pi) : ℝ) *
      (∫ t, ‖paretoMellin (hilbertOne - finiteResidueCandidate D c)
        (MellinFrequency.criticalPoint t)‖ ^ 2) =
      1 - 2 * inner ℝ hilbertOne (finiteResidueCandidate D c) +
        ‖finiteResidueCandidate D c‖ ^ 2 := by
  rw [finiteResidueError_boundary_energy, norm_sub_sq_real, hilbertOne_norm_sq]

end RiemannResearch.RH.ParetoResidualBoundaryEnergy
