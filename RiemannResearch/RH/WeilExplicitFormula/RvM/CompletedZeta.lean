/-
Vendored from anthropics/formal-math, zeta23, commit
fbdc36bbf17d20af3fd0447c6d1a8a02773c9844.
Local modification (2026-09-07): intra-project imports relocated under
RiemannResearch.RH.WeilExplicitFormula; declarations and namespaces unchanged.
Original copyright notices and Apache-2.0 license are preserved.
-/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RiemannResearch.RH.WeilExplicitFormula.Statement
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Basic analytic and zero-set facts for completed zeta

Source: the six declarations below are moved verbatim from `RvM/CountByIntegral`.
They depend on the zeta statement layer and Mathlib, independently of the
contour integration used for the zero-counting theorem.
-/

open Complex Set Topology Filter Real
open scoped BigOperators

noncomputable section

namespace Zeta23
namespace RvM

lemma analyticAt_completedRiemannZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta s := by
  have hopen : IsOpen (({0, 1} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hdiff : DifferentiableOn ℂ completedRiemannZeta (({0, 1} : Set ℂ)ᶜ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds (by simp [h0, h1]))

lemma completedRiemannZeta_eq_Gammaℝ_mul {s : ℂ} (hs : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

lemma completedRiemannZeta_eq_zero_iff_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [completedRiemannZeta_eq_Gammaℝ_mul h0 hG, mul_eq_zero]
  simp [hG]

lemma completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  rw [Ne, completedRiemannZeta_eq_zero_iff_of_re_pos (by linarith)]
  exact riemannZeta_ne_zero_of_one_le_re hs

lemma completedRiemannZeta_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  exact completedRiemannZeta_ne_zero_of_one_le_re (by simp; linarith)

/-- The zeros of Λ are exactly the nontrivial zeros of ζ (everywhere: at the poles 0, 1 Mathlib's
junk values are nonzero too, since ζ(1) ≠ 0 in Mathlib and Λ(0) = Λ(1)). -/
lemma completedRiemannZeta_eq_zero_iff {s : ℂ} :
    completedRiemannZeta s = 0 ↔ IsNontrivialZero s := by
  constructor
  · intro h
    have h1 : 0 < s.re := by
      by_contra hle
      exact completedRiemannZeta_ne_zero_of_re_nonpos (not_lt.mp hle) h
    have h2 : s.re < 1 := by
      by_contra hle
      exact completedRiemannZeta_ne_zero_of_one_le_re (not_lt.mp hle) h
    exact ⟨(completedRiemannZeta_eq_zero_iff_of_re_pos h1).mp h, h1, h2⟩
  · rintro ⟨hz, h1, _⟩
    exact (completedRiemannZeta_eq_zero_iff_of_re_pos h1).mpr hz

end RvM
end Zeta23
