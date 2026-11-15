/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdCellProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The actual finite canonical trial coefficients and gcd-cell equations

Source: CanonicalPrimePowerUpdatesResearch20261107, Sections 3 and 6.
The zero atom g_1 is removed before choosing a coefficient vector. Every
matrix entry below is a complete Hilbert pairing.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTCellCoordinateSystem
open ZetaTwoHilbert QCRTFiniteCollocation QGcdCellRefinement QGcdCellProjection

abbrev TrialIndex (L : ℕ) := {d : ℕ // d ∈ L.divisors.erase 1}

theorem trialSpace_eq_span_nontrivial (L : ℕ) :
    trialSpace L = Submodule.span ℝ
      (qResidue '' (↑(L.divisors.erase 1) : Set ℕ)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨d, hd, rfl⟩
    by_cases hd1 : d = 1
    · simp only [hd1, qResidue_one]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨d, Finset.mem_erase.mpr ⟨hd1, hd⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨d, hd, rfl⟩
    exact Submodule.subset_span ⟨d, (Finset.mem_erase.mp hd).2, rfl⟩

theorem trialSpace_eq_span_range (L : ℕ) :
    trialSpace L = Submodule.span ℝ (Set.range (fun d : TrialIndex L => qResidue d)) := by
  rw [trialSpace_eq_span_nontrivial]
  congr 1
  ext f
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d, d.property, rfl⟩

/-- A coefficient vector for every actual finite trial vector. -/
theorem exists_trial_coefficients (L : ℕ) (f : trialSpace L) :
    ∃ c : TrialIndex L → ℝ, (∑ d, c d • qResidue d) = (f : QHilbert) := by
  have hle : trialSpace L ≤
      Submodule.span ℝ (Set.range (fun d : TrialIndex L => qResidue d)) :=
    (trialSpace_eq_span_range L).le
  have hf := hle f.property
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf

def canonicalCoefficients (L : ℕ) (hL : 2 ≤ L) : TrialIndex L → ℝ :=
  (exists_trial_coefficients L (canonical L hL)).choose

theorem canonicalCoefficients_spec (L : ℕ) (hL : 2 ≤ L) :
    (∑ d : TrialIndex L, canonicalCoefficients L hL d • qResidue d) =
      (canonical L hL : QHilbert) :=
  (exists_trial_coefficients L (canonical L hL)).choose_spec

/-- The complete physical pairing matrix between trial atoms and gcd cells. -/
def cellMatrix (L : ℕ) (e : ℕ) (d : TrialIndex L) : ℝ :=
  inner ℝ (qResidue d) (eventVector (gcdCell L e))

def cellTarget (L e : ℕ) : ℝ := inner ℝ (target L) (eventVector (gcdCell L e))

theorem canonical_cell_system (L : ℕ) (hL : 2 ≤ L) (e : ℕ)
    (he : e ∈ L.divisors) :
    (∑ d : TrialIndex L, canonicalCoefficients L hL d * cellMatrix L e d) =
      cellTarget L e := by
  have hp := conditional_inner L (canonical L hL) (eventVector (gcdCell L e))
    (eventVector_gcdCell_mem L e (by omega) he)
  rw [canonical_conditional L hL] at hp
  change _ = inner ℝ (target L) (eventVector (gcdCell L e))
  rw [hp, ← canonicalCoefficients_spec L hL, sum_inner]
  simp only [real_inner_smul_left, cellMatrix]

theorem canonical_coefficient_energy (L : ℕ) (hL : 2 ≤ L) :
    ‖(canonical L hL : QHilbert)‖ ^ 2 =
      ∑ d : TrialIndex L, ∑ e : TrialIndex L,
        canonicalCoefficients L hL d * canonicalCoefficients L hL e *
          inner ℝ (qResidue d) (qResidue e) := by
  rw [← real_inner_self_eq_norm_sq, ← canonicalCoefficients_spec L hL,
    sum_inner]
  apply Finset.sum_congr rfl
  intro d hd
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [inner_smul_right, real_inner_smul_left]
  ring

end RiemannResearch.RH.QCRTCellCoordinateSystem
