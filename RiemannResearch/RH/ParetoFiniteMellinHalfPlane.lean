/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidualBoundaryEnergy
import RiemannResearch.RH.ParetoBoundedMellinLinearity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact finite Pareto Mellin identities on the full positive half-plane

The literal finite signed candidate is bounded, so its Mellin integrand is
absolutely integrable for Re(s)>0. This extends the actual integral identity
to the boundary Re(s)=1/2 and rewrites the already proved Plancherel formula
into the explicit critical-line zeta numerator. All signed coefficients,
target cross terms, and complete candidate squares are retained.

-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.ParetoFiniteMellinHalfPlane

open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoAtomMellinSignature
open RiemannResearch.RH.ParetoHorizontalZeroBridge
open RiemannResearch.RH.ParetoResidualBoundaryEnergy

/-- Subtraction is genuine integral linearity for bounded physical steps. -/
theorem paretoMellin_sub_of_bounded (f g : ThresholdHilbert)
    {Cf Cg : ℝ} (hf : ∀ k, |hilbertSequence f k| ≤ Cf)
    (hg : ∀ k, |hilbertSequence g k| ≤ Cg)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (f - g) s = paretoMellin f s - paretoMellin g s := by
  have hneg : ∀ k, |hilbertSequence (-g) k| ≤ Cg := by
    intro k
    have hseq : hilbertSequence (-g) k = -hilbertSequence g k := by
      change hilbertSequenceLinear (-g) k = _
      rw [map_neg]
      rfl
    simpa only [hseq, abs_neg] using hg k
  have hMneg : paretoMellin (-g) s = -paretoMellin g s := by
    simpa only [neg_one_smul] using paretoMellin_smul (-1 : ℝ) g s
  rw [sub_eq_add_neg,
    paretoMellin_add_of_bounded f (-g) hf hneg s hs, hMneg, sub_eq_add_neg]

/-- The target transform is 1/s on its full bounded-step half-plane. -/
theorem paretoMellin_one_of_pos (s : ℂ) (hs : 0 < s.re) :
    paretoMellin hilbertOne s = 1 / s := by
  rw [paretoMellin_eq_step_integral]
  have he : (∫ x in Ioi (1 : ℝ), (hilbertSequence hilbertOne ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx' : (1 : ℝ) < x := hx
    have hf : 1 ≤ ⌊x⌋₊ :=
      (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)).2 (by simpa using hx'.le)
    rw [hilbertOne_sequence]
    simp [zeroAnchor, show ⌊x⌋₊ ≠ 0 by omega]
  have hexp : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [he, integral_Ioi_cpow_of_lt hexp (by norm_num : (0 : ℝ) < 1)]
  simp

/-- The finite signed atom synthesis is transformed term by term using
absolute integrability, without the Hilbert continuity half-plane premise. -/
theorem paretoMellin_finiteResidue_of_pos
    (D : Finset LegalConductor) (c : LegalConductor → ℝ)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    paretoMellin (finiteResidueCandidate D c) s =
      riemannZeta s / s * ∑ d ∈ D,
        (c d : ℂ) * ((1 / (d.1 : ℂ)) - (d.1 : ℂ) ^ (-s)) := by
  classical
  have hseq (x : ℝ) : hilbertSequence (finiteResidueCandidate D c) ⌊x⌋₊ =
      ∑ d ∈ D, c d * hilbertSequence
        (normalizedResidueHilbert d.1 (by omega)) ⌊x⌋₊ := by
    change hilbertSequenceLinear
      (∑ d ∈ D, c d • normalizedResidueHilbert d.1 (by omega)) ⌊x⌋₊ = _
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  have he : (fun x : ℝ => (hilbertSequence (finiteResidueCandidate D c) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) =
      (fun x : ℝ => ∑ d ∈ D, (c d : ℂ) *
        ((hilbertSequence (normalizedResidueHilbert d.1 (by omega)) ⌊x⌋₊ : ℂ) *
          (x : ℂ) ^ (-s - 1))) := by
    funext x
    rw [hseq]
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hi (d : LegalConductor) : IntegrableOn
      (fun x : ℝ => (hilbertSequence (normalizedResidueHilbert d.1 (by omega)) ⌊x⌋₊ : ℂ) *
        (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
    apply paretoMellin_step_integrable_of_bounded _ (C := 1) ?_ s hs
    intro k
    rw [normalizedResidueHilbert_sequence]
    exact normalizedAtom_abs_le_one d.1 k (by omega)
  rw [paretoMellin_eq_step_integral, he,
    integral_finsetSum D (fun d _ => (hi d).const_mul (c d : ℂ))]
  calc
    _ = ∑ d ∈ D, (c d : ℂ) *
        (riemannZeta s / s * ((1 / (d.1 : ℂ)) - (d.1 : ℂ) ^ (-s))) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_const_mul, ← paretoMellin_eq_step_integral,
        paretoMellin_normalizedResidue_zeta d.1 (by omega) s hs hs1]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- Exact signed residual formula on Re(s)>0, including the critical line. -/
theorem paretoMellin_finiteResidue_error_of_pos
    (D : Finset LegalConductor) (c : LegalConductor → ℝ)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    paretoMellin (hilbertOne - finiteResidueCandidate D c) s =
      (1 - riemannZeta s * ∑ d ∈ D,
        (c d : ℂ) * ((1 / (d.1 : ℂ)) - (d.1 : ℂ) ^ (-s))) / s := by
  rw [paretoMellin_sub_of_bounded hilbertOne (finiteResidueCandidate D c)
    hilbertOne_sequence_bound (finiteResidueCandidate_sequence_bound D c) s hs,
    paretoMellin_one_of_pos s hs, paretoMellin_finiteResidue_of_pos D c s hs hs1]
  ring

/-- Exact boundary Plancherel with the explicit zeta numerator and the full
critical-line denominator. -/
theorem finiteResidueError_boundary_zeta_energy
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    (1 / (2 * Real.pi) : ℝ) *
      (∫ t : ℝ, ‖1 - riemannZeta (MellinFrequency.criticalPoint t) *
        ∑ d ∈ D, (c d : ℂ) * ((1 / (d.1 : ℂ)) -
          (d.1 : ℂ) ^ (-MellinFrequency.criticalPoint t))‖ ^ 2 / (1 / 4 + t ^ 2)) =
      ‖hilbertOne - finiteResidueCandidate D c‖ ^ 2 := by
  rw [← finiteResidueError_boundary_energy D c]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hs : 0 < (MellinFrequency.criticalPoint t).re := by
    simp [MellinFrequency.criticalPoint]
  have hs1 : MellinFrequency.criticalPoint t ≠ 1 := by
    exact MellinFrequency.criticalPoint_ne_one t
  have hn : ‖MellinFrequency.criticalPoint t‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num [MellinFrequency.criticalPoint]
    ring
  rw [paretoMellin_finiteResidue_error_of_pos D c _ hs hs1,
    norm_div, div_pow, hn]

/-- The explicit zeta boundary identity keeps the signed cross term and the
complete candidate square as an exact equality. -/
theorem finiteResidueError_boundary_zeta_energy_cross_terms
    (D : Finset LegalConductor) (c : LegalConductor → ℝ) :
    (1 / (2 * Real.pi) : ℝ) *
      (∫ t : ℝ, ‖1 - riemannZeta (MellinFrequency.criticalPoint t) *
        ∑ d ∈ D, (c d : ℂ) * ((1 / (d.1 : ℂ)) -
          (d.1 : ℂ) ^ (-MellinFrequency.criticalPoint t))‖ ^ 2 / (1 / 4 + t ^ 2)) =
      1 - 2 * inner ℝ hilbertOne (finiteResidueCandidate D c) +
        ‖finiteResidueCandidate D c‖ ^ 2 := by
  rw [finiteResidueError_boundary_zeta_energy, norm_sub_sq_real, hilbertOne_norm_sq]

end RiemannResearch.RH.ParetoFiniteMellinHalfPlane
