/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.OrdinateCollisionCertificate
import Mathlib.Tactic.Linarith

/-!
# Analytic and ordinate diagonals for actual zeta zeros

Section 4 of the user-provided note `Montgomery_Pair_Correlation_Without_RH.md`
separates the equal-height atom into the analytic diagonal (the sum of squared
analytic multiplicities, denoted by `N^*(T)` in GLSS, arXiv:2503.15449v2)
and ordered pairs of distinct complex zeros sharing an ordinate.
Reflection detects off-line zeros in the second term.
-/

noncomputable section
open Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroCollisionCertificate
open ActualZeroOrdinate OrdinateCollisionCertificate

/-- Ordered occurrence pairs from the same complex zero. -/
def analyticPairCount (T : ℝ) : ℕ := by
  classical
  exact ∑ i : Copies T, ∑ j : Copies T, if i.1.1 = j.1.1 then 1 else 0

theorem analyticPairCount_eq_sum_sq (T : ℝ) :
    analyticPairCount T = ∑ ρ ∈ cutoff T, (zeroMult ρ) ^ 2 := by
  classical
  have row (i : Copies T) :
      (∑ j : Copies T, if i.1.1 = j.1.1 then (1 : ℕ) else 0) = zeroMult i.1.1 := by
    have hrel (j : {z // z ∈ cutoff T}) : i.1.1 = j.1 ↔ j = i.1 :=
      ⟨fun h => Subtype.ext h.symm, fun h => congrArg Subtype.val h.symm⟩
    rw [Fintype.sum_sigma]
    simp only [hrel, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  unfold analyticPairCount
  simp_rw [row]
  simp [Copies, Fintype.sum_sigma, pow_two,
    ← Finset.sum_attach (cutoff T) (fun ρ => zeroMult ρ * zeroMult ρ)]

private def crossEntry {T : ℝ} (i j : Copies T) : ℕ := by
  classical
  exact if copyOrdinate T i = copyOrdinate T j ∧ i.1.1 ≠ j.1.1 then 1 else 0

/-- Ordered pairs from distinct complex zeros sharing the same ordinate. -/
def distinctZeroCollision (T : ℝ) : ℕ := ∑ i : Copies T, ∑ j : Copies T, crossEntry i j

theorem collision_eq_analytic_add_distinctZeroCollision (T : ℝ) :
    actualCollision T = analyticPairCount T + distinctZeroCollision T := by
  classical
  unfold actualCollision occurrenceCollision analyticPairCount distinctZeroCollision
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : i.1.1 = j.1.1
  · have hy : copyOrdinate T i = copyOrdinate T j := congrArg Complex.im hz
    simp [crossEntry, hz, hy]
  · by_cases hy : copyOrdinate T i = copyOrdinate T j <;> simp [crossEntry, hz, hy]

private theorem reflected_companion {T : ℝ} (c : Copies T) (hoff : c.1.1.re ≠ 1 / 2) :
    ∃ d : Copies T, copyOrdinate T c = copyOrdinate T d ∧ c.1.1 ≠ d.1.1 := by
  let d : Copies T := ⟨⟨reflect c.1.1, reflect_mem c.1.2⟩,
    ⟨0, multiplicity_pos (reflect_mem c.1.2)⟩⟩
  refine ⟨d, (reflect_im c.1.1).symm, ?_⟩
  change c.1.1 ≠ reflect c.1.1
  intro h
  have hre := congrArg Complex.re h
  rw [reflect_re] at hre
  exact hoff (by linarith)

private theorem one_le_cross_row {T : ℝ} (i j : Copies T)
    (hy : copyOrdinate T i = copyOrdinate T j) (hz : i.1.1 ≠ j.1.1) :
    1 ≤ ∑ j' : Copies T, crossEntry i j' := by
  classical
  have h : crossEntry i j = 1 := by simp [crossEntry, hy, hz]
  rw [← h]
  exact Finset.single_le_sum (f := fun j' => crossEntry i j') (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)

theorem off_count_add_analytic_le_collision (T : ℝ) :
    offCount T + analyticPairCount T ≤ actualCollision T := by
  classical
  have hle : offCount T ≤ distinctZeroCollision T := by
    unfold offCount offCopies distinctZeroCollision
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : i.1.1.re ≠ 1 / 2
    · obtain ⟨j, hy, hz⟩ := reflected_companion i h
      simpa only [if_pos h] using one_le_cross_row i j hy hz
    · rw [if_neg h]
      exact Nat.zero_le _
  rw [collision_eq_analytic_add_distinctZeroCollision T]
  omega

theorem two_le_distinctZeroCollision_of_off_line {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff T)
    (hoff : ρ.re ≠ 1 / 2) : 2 ≤ distinctZeroCollision T := by
  classical
  let c : Copies T := ⟨⟨ρ, hρ⟩, ⟨0, multiplicity_pos hρ⟩⟩
  obtain ⟨d, hy, hz⟩ := reflected_companion c hoff
  have hne : c ≠ d := fun he => hz (congrArg (fun p : Copies T => p.1.1) he)
  let row := fun i : Copies T => ∑ j : Copies T, crossEntry i j
  have h₁ : 1 ≤ row c := one_le_cross_row c d hy hz
  have h₂ : 1 ≤ row d := one_le_cross_row d c hy.symm (Ne.symm hz)
  have hboth : (∑ i ∈ ({c, d} : Finset (Copies T)), row i) = row c + row d := by simp [hne]
  change 2 ≤ ∑ i : Copies T, row i
  calc
    2 ≤ row c + row d := by omega
    _ = ∑ i ∈ ({c, d} : Finset (Copies T)), row i := hboth.symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)

private theorem cross_zero_of_all_critical {T : ℝ} (hc : ∀ ρ ∈ cutoff T, ρ.re = 1 / 2) :
    distinctZeroCollision T = 0 := by
  classical
  unfold distinctZeroCollision
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases he : copyOrdinate T i = copyOrdinate T j
  · have hz : i.1.1 = j.1.1 := Complex.ext ((hc _ i.1.2).trans (hc _ j.1.2).symm) he
    simp [crossEntry, he, hz]
  · simp [crossEntry, he]

theorem collision_eq_analyticPairCount_iff (T : ℝ) :
    actualCollision T = analyticPairCount T ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  rw [collision_eq_analytic_add_distinctZeroCollision T]
  constructor
  · intro h ρ hρ
    by_contra hoff
    have htwo := two_le_distinctZeroCollision_of_off_line hρ hoff
    omega
  · intro h
    rw [cross_zero_of_all_critical h, Nat.add_zero]

end RiemannResearch.Analysis.ActualZeroCollisionCertificate
