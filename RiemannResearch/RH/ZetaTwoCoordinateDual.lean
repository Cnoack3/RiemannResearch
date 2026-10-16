/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Riesz vectors of physical Q coordinates

The single-site vectors represent positive-coordinate evaluation in the
actual inverse-square weighted Hilbert space. The exact physical amplitude
and squared norm are both the inverse probability weight.

Source: the user-provided divisibility-legality research handoff,
16 October 2026, for the quantitative functional target. The construction
uses the standard weighted-coordinate Riesz representation.
-/

noncomputable section
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability

/-- Actual Riesz vector of a positive physical coordinate evaluation. -/
def qSiteRiesz (n : ℕ) : QHilbert :=
  (positiveQWeight n)⁻¹ • qPoint (n - 1)

/-- Pairing with the representer recovers the literal positive coordinate. -/
theorem qSiteRiesz_inner (n : ℕ) (hn : 0 < n) (x : QHilbert) :
    inner ℝ (qSiteRiesz n) x = qSequence x n := by
  have h : n - 1 + 1 = n := by omega
  rw [qSiteRiesz, real_inner_smul_left, qPoint_inner]
  simp only [qWeight, h]
  have hw : positiveQWeight n ≠ 0 := by
    unfold positiveQWeight
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hZ := zetaTwo_pos
    exact ne_of_gt (by positivity)
  field_simp [hw]

/-- The physical representer has one nonzero site, with inverse probability weight. -/
theorem qSequence_qSiteRiesz (n : ℕ) (hn : 0 < n) (k : ℕ) :
    qSequence (qSiteRiesz n) k =
      if k = n then (positiveQWeight n)⁻¹ else 0 := by
  have h : n - 1 + 1 = n := by omega
  change qSequenceLinear ((positiveQWeight n)⁻¹ • qPoint (n - 1)) k = _
  rw [map_smul]
  change (positiveQWeight n)⁻¹ * qSequence (qPoint (n - 1)) k = _
  simp [qSequence_qPoint, qPointSequence, h]


/-- Exact squared evaluation norm under the inverse-square probability law. -/
theorem qSiteRiesz_norm_sq (n : ℕ) (hn : 0 < n) :
    ‖qSiteRiesz n‖ ^ 2 = zetaTwo * (n : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, qSiteRiesz_inner n hn,
    qSequence_qSiteRiesz n hn n]
  simp [positiveQWeight]

end RiemannResearch.RH.ZetaTwoHilbert
