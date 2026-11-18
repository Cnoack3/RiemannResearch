/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.OccurrenceCollisionMultiplicity
import Mathlib.Tactic.Ring

/-!
# Distinct and crowded ordinate counts

The elementary finite bounds are from Section 3 of the user-provided note
`Montgomery_Pair_Correlation_Without_RH.md`. They count ordered collisions
among a finite family, including repeated ordinates.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

theorem distinct_height_excess_bound {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    2 * Fintype.card ι ≤ 2 * (ordinateSupport t).card + occurrenceExcess t := by
  classical
  have row (m : ℕ) : 2 * m ≤ 2 + m * (m - 1) := by
    by_cases h : 2 ≤ m
    · have h' := Nat.mul_le_mul_right (m - 1) h
      omega
    · omega
  rw [card_eq_sum_ordinateMultiplicity t, occurrenceExcess_eq_multiplicityExcess, Finset.mul_sum]
  calc
    _ ≤ ∑ τ ∈ ordinateSupport t, (2 + ordinateMultiplicity t τ * (ordinateMultiplicity t τ - 1)) :=
      Finset.sum_le_sum (fun τ _ => row _)
    _ = _ := by simp [multiplicityExcess, Finset.sum_add_distrib, Nat.mul_comm]

theorem crowded_occurrence_excess_bound {ι : Type*} [Fintype ι] (t : ι → ℝ) (k : ℕ) :
    (k - 1) * (∑ τ ∈ ordinateSupport t,
      if k ≤ ordinateMultiplicity t τ then ordinateMultiplicity t τ else 0) ≤
      occurrenceExcess t := by
  classical
  rw [Finset.mul_sum, occurrenceExcess_eq_multiplicityExcess]
  unfold multiplicityExcess
  apply Finset.sum_le_sum
  intro τ _
  by_cases h : k ≤ ordinateMultiplicity t τ
  · simp only [if_pos h]
    exact (Nat.mul_le_mul_right (ordinateMultiplicity t τ) (Nat.sub_le_sub_right h 1)).trans_eq
      (Nat.mul_comm _ _)
  · simp [h]

theorem crowded_height_excess_bound {ι : Type*} [Fintype ι] (t : ι → ℝ) (k : ℕ) :
    k * (k - 1) * ((ordinateSupport t).filter (fun τ => k ≤ ordinateMultiplicity t τ)).card ≤
      occurrenceExcess t := by
  classical
  have hc : k * ((ordinateSupport t).filter (fun τ => k ≤ ordinateMultiplicity t τ)).card ≤
      ∑ τ ∈ ordinateSupport t, if k ≤ ordinateMultiplicity t τ then ordinateMultiplicity t τ
        else 0 := by
    rw [← Finset.sum_filter]
    calc
      _ = ∑ τ ∈ (ordinateSupport t).filter (fun τ => k ≤ ordinateMultiplicity t τ), k := by
        simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun τ hτ => (Finset.mem_filter.mp hτ).2)
  calc
    _ = (k - 1) * (k * ((ordinateSupport t).filter
        (fun τ => k ≤ ordinateMultiplicity t τ)).card) := by ring
    _ ≤ _ := (Nat.mul_le_mul_left (k - 1) hc).trans (crowded_occurrence_excess_bound t k)

end RiemannResearch.Analysis.OrdinateCollisionCertificate
