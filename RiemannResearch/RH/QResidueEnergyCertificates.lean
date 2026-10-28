/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueHeadSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed correction certificates and exact comparisons for head minima

Source: user-provided Minimum_Energy_Exact_Head_Research_Agenda_2026-10-28.md,
priorities 1, 2, and 4 (statements and proof strategy). Every inner product
and norm is the complete Q quantity. No infinite-stage energy bound is assumed
or asserted by the comparison and completion identities.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QResidueEnergyCertificates
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace

/-- An actual correction in the zero-head subspace preserves the exact head. -/
theorem correction_same_head (s : Finset ℕ) (H : ℕ) (F u : QHilbert)
    (hF : F ∈ dictionary s) (hu : u ∈ dictionary s ⊓ headNull H) :
    F - u ∈ dictionary s ∧
      ∀ n, 0 < n → n ≤ H → qSequence (F - u) n = qSequence F n := by
  refine ⟨(dictionary s).sub_mem hF hu.1, ?_⟩
  intro n hn hnH
  change qSequenceLinear (F - u) n = _
  simp only [map_sub, Pi.sub_apply]
  change qSequence F n - qSequence u n = qSequence F n
  rw [hu.2 n hn hnH, sub_zero]

/-- The complete signed correction identity includes the distance from the optimum. -/
theorem correction_gain_completion (s : Finset ℕ) (H : ℕ) (F u : QHilbert)
    (hu : u ∈ dictionary s ⊓ headNull H) :
    2 * inner ℝ F u - ‖u‖ ^ 2 =
      ‖(dictionary s ⊓ headNull H).starProjection F‖ ^ 2 -
        ‖(dictionary s ⊓ headNull H).starProjection F - u‖ ^ 2 := by
  have hmem : (F - u) - F ∈ dictionary s ⊓ headNull H := by
    have he : (F - u) - F = -u := by abel
    rw [he]
    exact (dictionary s ⊓ headNull H).neg_mem hu
  have h := exactHeadAdjustment_completion_of_mem s H F (F - u) hmem
  have he : F - u - exactHeadAdjustment s H F =
      (dictionary s ⊓ headNull H).starProjection F - u := by
    dsimp [exactHeadAdjustment]
    abel
  rw [he, exactHeadAdjustment_energy, norm_sub_sq_real] at h
  linarith

/-- Any signed zero-head correction gives a rigorous upper bound on the minimum. -/
theorem exactHeadAdjustment_le_correction (s : Finset ℕ) (H : ℕ) (F u : QHilbert)
    (hu : u ∈ dictionary s ⊓ headNull H) :
    ‖exactHeadAdjustment s H F‖ ^ 2 ≤
      ‖F‖ ^ 2 - 2 * inner ℝ F u + ‖u‖ ^ 2 := by
  have h := correction_gain_completion s H F u hu
  rw [exactHeadAdjustment_energy]
  nlinarith [sq_nonneg ‖(dictionary s ⊓ headNull H).starProjection F - u‖]

/-- The certificate is sufficient without evaluating an inverse Gram matrix. -/
theorem exactHeadAdjustment_le_of_correction_certificate
    (s : Finset ℕ) (H : ℕ) (F u : QHilbert)
    (hu : u ∈ dictionary s ⊓ headNull H) (C : ℝ)
    (hgain : ‖F‖ ^ 2 - C ≤ 2 * inner ℝ F u - ‖u‖ ^ 2) :
    ‖exactHeadAdjustment s H F‖ ^ 2 ≤ C := by
  have h := exactHeadAdjustment_le_correction s H F u hu
  linarith

/-- A nonzero structured zero-head block can be optimized along its scalar multiples. -/
theorem exactHeadAdjustment_le_one_direction
    (s : Finset ℕ) (H : ℕ) (F v : QHilbert)
    (hv : v ∈ dictionary s ⊓ headNull H) (hv0 : v ≠ 0) :
    ‖exactHeadAdjustment s H F‖ ^ 2 ≤
      ‖F‖ ^ 2 - (inner ℝ F v) ^ 2 / ‖v‖ ^ 2 := by
  have h := exactHeadAdjustment_le_correction s H F
    ((inner ℝ F v / ‖v‖ ^ 2) • v)
    ((dictionary s ⊓ headNull H).smul_mem _ hv)
  rw [real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)
  have he : ‖F‖ ^ 2 - 2 * ((inner ℝ F v / ‖v‖ ^ 2) * inner ℝ F v) +
      (inner ℝ F v / ‖v‖ ^ 2) ^ 2 * ‖v‖ ^ 2 =
      ‖F‖ ^ 2 - (inner ℝ F v) ^ 2 / ‖v‖ ^ 2 := by
    field_simp [hn]
    ring
  rw [he] at h
  exact h

open ZetaTwoHilbert QSquarefreeLatticePackets
theorem dictionary_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    dictionary s ≤ dictionary t := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, rfl⟩
  exact Submodule.subset_span ⟨⟨d, hst d.property⟩, rfl⟩
theorem exactHeadAdjustment_dictionary_gain {s t : Finset ℕ} (hst : s ⊆ t)
    (H : ℕ) (F : QHilbert) (hF : F ∈ dictionary s) :
    ‖exactHeadAdjustment s H F‖ ^ 2 = ‖exactHeadAdjustment t H F‖ ^ 2 +
      ‖exactHeadAdjustment s H F - exactHeadAdjustment t H F‖ ^ 2 := by
  have hs := exactHeadAdjustment_same_head s H F hF
  exact exactHeadAdjustment_completion t H F _ (dictionary_mono hst hF)
    (dictionary_mono hst hs.1) hs.2
theorem exactHeadAdjustment_head_gain (s : Finset ℕ) {H K : ℕ} (hHK : H ≤ K)
    (F : QHilbert) (hF : F ∈ dictionary s) :
    ‖exactHeadAdjustment s K F‖ ^ 2 = ‖exactHeadAdjustment s H F‖ ^ 2 +
      ‖exactHeadAdjustment s K F - exactHeadAdjustment s H F‖ ^ 2 := by
  have hk := exactHeadAdjustment_same_head s K F hF
  exact exactHeadAdjustment_completion s H F _ hF hk.1
    (fun n hn hnH => hk.2 n hn (hnH.trans hHK))

/-- More directions at a fixed head cannot increase the complete minimum energy. -/
theorem exactHeadAdjustment_antitone_dictionary {s t : Finset ℕ} (hst : s ⊆ t)
    (H : ℕ) (F : QHilbert) (hF : F ∈ dictionary s) :
    ‖exactHeadAdjustment t H F‖ ^ 2 ≤ ‖exactHeadAdjustment s H F‖ ^ 2 := by
  rw [exactHeadAdjustment_dictionary_gain hst H F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- More head constraints at a fixed dictionary cannot decrease the minimum. -/
theorem exactHeadAdjustment_monotone_head (s : Finset ℕ) {H K : ℕ} (hHK : H ≤ K)
    (F : QHilbert) (hF : F ∈ dictionary s) :
    ‖exactHeadAdjustment s H F‖ ^ 2 ≤ ‖exactHeadAdjustment s K F‖ ^ 2 := by
  rw [exactHeadAdjustment_head_gain s hHK F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.QResidueEnergyCertificates
