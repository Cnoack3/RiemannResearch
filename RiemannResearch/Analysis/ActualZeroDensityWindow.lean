/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroTailReflection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Actual finite-height density windows and strict boundary correction

The closed half-plane count agrees with the convention in Chourasiya--Simonic,
arXiv:2507.15184v2, Section 1 and Theorem 1:
https://arxiv.org/html/2507.15184v2.
The finite-sum and reflection transfers here are proved independently; the
paper's analytic estimate and finite-height RH verification are not imported.
Analytic multiplicities and the strict bad-mask boundary remain exact.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23
def rightInclusiveWindow (H T σ : ℝ) : ℝ :=
  realSum T (fun ρ => if H < ρ.im ∧ σ ≤ ρ.re then 1 else 0)

theorem rightInclusiveCount_nonneg (T σ : ℝ) :
    0 ≤ rightInclusiveCount T σ := by
  apply realSum_nonneg
  intro ρ hρ
  split_ifs <;> norm_num

theorem rightInclusiveCount_le_count (T σ : ℝ) :
    rightInclusiveCount T σ ≤ (Ncount 0 T : ℝ) := by
  rw [← realSum_one T]
  apply realSum_mono
  intro ρ hρ
  split_ifs <;> norm_num

theorem rightInclusiveWindow_nonneg (H T σ : ℝ) :
    0 ≤ rightInclusiveWindow H T σ := by
  apply realSum_nonneg
  intro ρ hρ
  split_ifs <;> norm_num

theorem rightInclusiveCount_split {H T : ℝ} (hHT : H ≤ T) (σ : ℝ) :
    rightInclusiveCount T σ =
      rightInclusiveCount H σ + rightInclusiveWindow H T σ := by
  classical
  have hsub : cutoff H ⊆ cutoff T := by
    intro ρ hρ
    obtain ⟨hz, h0, hH⟩ := mem_cutoff.mp hρ
    exact mem_cutoff.mpr ⟨hz, h0, hH.trans hHT⟩
  have hhead : realSum T
      (fun ρ => if ρ.im ≤ H ∧ σ ≤ ρ.re then (1 : ℝ) else 0) =
        rightInclusiveCount H σ := by
    unfold rightInclusiveCount realSum
    have hz : ∀ ρ ∈ cutoff T, ρ ∉ cutoff H →
        (zeroMult ρ : ℝ)*(if ρ.im ≤ H ∧ σ ≤ ρ.re then 1 else 0) = 0 := by
      intro ρ hρ hn
      have hnot : ¬ρ.im ≤ H := by
        intro hh
        exact hn (mem_cutoff.mpr ⟨(mem_cutoff.mp hρ).1,
          (mem_cutoff.mp hρ).2.1, hh⟩)
      simp [hnot]
    rw [← Finset.sum_subset hsub hz]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hH := (mem_cutoff.mp hρ).2.2
    simp only [hH, true_and]
  have hind (ρ : ℂ) :
      (if σ ≤ ρ.re then (1 : ℝ) else 0) =
        (if ρ.im ≤ H ∧ σ ≤ ρ.re then 1 else 0) +
          (if H < ρ.im ∧ σ ≤ ρ.re then 1 else 0) := by
    by_cases hh : ρ.im ≤ H <;> by_cases hs : σ ≤ ρ.re <;>
      simp [hh, hs, not_lt.mpr, lt_of_not_ge]
  have hsplit : rightInclusiveCount T σ = realSum T (fun ρ =>
      (if ρ.im ≤ H ∧ σ ≤ ρ.re then (1 : ℝ) else 0) +
        (if H < ρ.im ∧ σ ≤ ρ.re then 1 else 0)) := by
    unfold rightInclusiveCount
    congr 1
    funext ρ
    exact hind ρ
  rw [hsplit, realSum_add, hhead]
  rfl

/-- Exact height subtraction, with analytic multiplicity and a closed real-part
threshold. The lower height is strict in the window. -/
theorem rightInclusiveWindow_eq_sub {H T : ℝ} (hHT : H ≤ T) (σ : ℝ) :
    rightInclusiveWindow H T σ =
      rightInclusiveCount T σ - rightInclusiveCount H σ := by
  rw [rightInclusiveCount_split hHT]
  ring

/-- The actual finite-height term is bounded, never set to zero. -/
theorem strictTail_le_of_inclusiveWindow {H T δ F : ℝ}
    (hHT : H ≤ T) (hδ : 0 ≤ δ)
    (hwindow : rightInclusiveWindow H T (1/2+δ) ≤ F) :
    strictTail T δ ≤ 2*(F+rightInclusiveCount H (1/2+δ)) := by
  have h := strictTail_le_twice_inclusive T δ hδ
  rw [rightInclusiveCount_split hHT] at h
  linarith

theorem strictTail_le_of_inclusiveDifference {H T δ F : ℝ}
    (hHT : H ≤ T) (hδ : 0 ≤ δ)
    (hwindow : rightInclusiveCount T (1/2+δ) -
      rightInclusiveCount H (1/2+δ) ≤ F) :
    strictTail T δ ≤ 2*(F+(Ncount 0 H : ℝ)) := by
  have hw : rightInclusiveWindow H T (1/2+δ) ≤ F := by
    rwa [rightInclusiveWindow_eq_sub hHT]
  have h := strictTail_le_of_inclusiveWindow hHT hδ hw
  linarith [rightInclusiveCount_le_count H (1/2+δ)]

/-- Copies exactly on the closed density threshold are good at the strict
bad-mask boundary; their analytic multiplicities remain explicit. -/
def rightBoundaryCount (T σ : ℝ) : ℝ :=
  realSum T (fun ρ => if ρ.re = σ then 1 else 0)

theorem rightBoundaryCount_nonneg (T σ : ℝ) :
    0 ≤ rightBoundaryCount T σ := by
  apply realSum_nonneg
  intro ρ hρ
  split_ifs <;> norm_num

theorem rightInclusiveCount_eq_strict_add_boundary (T t : ℝ) :
    rightInclusiveCount T (1/2+t) =
      rightStrictTail T t + rightBoundaryCount T (1/2+t) := by
  have hind (ρ : ℂ) :
      (if 1/2+t ≤ ρ.re then (1:ℝ) else 0) =
        (if 1/2+t < ρ.re then 1 else 0)+
          (if ρ.re = 1/2+t then 1 else 0) := by
    by_cases hlt : 1/2+t < ρ.re
    · have hne : ρ.re ≠ 1/2+t := ne_of_gt hlt
      simp only [if_pos hlt.le, if_pos hlt, if_neg hne, add_zero]
    · by_cases heq : ρ.re = 1/2+t
      · simp [heq]
      · have hn : ¬1/2+t ≤ ρ.re := by
          intro h
          exact heq (le_antisymm (le_of_not_gt hlt) h)
        simp only [if_neg hn, if_neg hlt, if_neg heq, add_zero]
  unfold rightInclusiveCount
  simp_rw [hind]
  rw [realSum_add]
  rfl

/-- Exact strict/closed-threshold conversion; equality copies are subtracted,
not silently assigned to the strict bad set. -/
theorem strictTail_eq_inclusive_sub_boundary (T t : ℝ) (ht : 0 ≤ t) :
    strictTail T t =
      2*(rightInclusiveCount T (1/2+t)-rightBoundaryCount T (1/2+t)) := by
  rw [rightInclusiveCount_eq_strict_add_boundary, strictTail_eq_twice_right T t ht]
  ring

end RiemannResearch.Analysis.ActualZeroOrdinate
