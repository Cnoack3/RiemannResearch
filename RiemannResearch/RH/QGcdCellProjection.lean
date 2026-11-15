/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdCellRefinement
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact complete-Q projection in gcd-cell coordinates

Source: CanonicalPrimePowerUpdatesResearch20261107, Section 5. These are
the physical cell averages and their complete orthogonal Gram/Parseval formula.
Every cell denominator is its actual full-tail probability mass.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QGcdCellProjection
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open QCRTFiniteCollocation QGcdCellRefinement

theorem gcdCell_mass_pos (L d : ℕ) (hd : d ∈ L.divisors) :
    0 < eventMass (gcdCell L d) := by
  have hdp := Nat.pos_of_mem_divisors hd
  have hs : ({d} : Set ℕ) ⊆ gcdCell L d := by
    intro n hn
    have he : n = d := Set.mem_singleton_iff.mp hn
    subst n
    exact Nat.gcd_eq_left (Nat.dvd_of_mem_divisors hd)
  have h := eventMass_mono hs
  rw [eventMass_singleton d hdp] at h
  have hw : 0 < positiveQWeight d := by
    have hZ := zetaTwo_pos
    unfold positiveQWeight
    positivity
  exact hw.trans_le h

theorem gcdCell_inner (L d e : ℕ) :
    inner ℝ (eventVector (gcdCell L d)) (eventVector (gcdCell L e)) =
      if d = e then eventMass (gcdCell L d) else 0 := by
  classical
  by_cases hde : d = e
  · subst e
    rw [if_pos rfl, real_inner_self_eq_norm_sq, eventVector_norm_sq]
  · rw [if_neg hde, eventVector_inner]
    have he : gcdCell L d ∩ gcdCell L e = ∅ := by
      ext n
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hd, he⟩
      exact hde (hd.symm.trans he)
    rw [he, eventMass_empty]

/-- The divisor incidence row is exactly the sum of the corresponding
disjoint gcd cells, including the endpoint cell. -/
theorem divisor_eq_sum_gcdCells (L d : ℕ) (hL : 0 < L) (hdL : d ∣ L) :
    qDivisor d = ∑ e ∈ L.divisors,
      (if d ∣ e then (1 : ℝ) else 0) • eventVector (gcdCell L e) := by
  classical
  apply qSequence_injective
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · change qSequence (qDivisor d) n =
      qSequenceLinear (∑ e ∈ L.divisors,
        (if d ∣ e then (1 : ℝ) else 0) • eventVector (gcdCell L e)) n
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    change qSequence (qDivisor d) n = ∑ e ∈ L.divisors,
      (if d ∣ e then (1 : ℝ) else 0) * qSequence (eventVector (gcdCell L e)) n
    simp only [qSequence_qDivisor, qSequence_eventVector]
    have hc : Nat.gcd n L ∈ L.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n L, ne_of_gt hL⟩
    have hdc : d ∣ Nat.gcd n L ↔ d ∣ n :=
      ⟨fun h => h.trans (Nat.gcd_dvd_left n L), fun h => Nat.dvd_gcd h hdL⟩
    symm
    rw [Finset.sum_eq_single (Nat.gcd n L)]
    · simp [eventSequence, gcdCell, hn, positiveDivisor, hdc]
    · intro e he hne
      have hg : Nat.gcd n L ≠ e := Ne.symm hne
      simp [eventSequence, gcdCell, hn, hg]
    · intro hnot
      exact (hnot hc).elim

def cellAverage (L : ℕ) (f : QHilbert) : QHilbert :=
  ∑ d ∈ L.divisors,
    (inner ℝ f (eventVector (gcdCell L d)) / eventMass (gcdCell L d)) •
      eventVector (gcdCell L d)

theorem cellAverage_mem (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    cellAverage L f ∈ cellSpace L := by
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  exact eventVector_gcdCell_mem L d hL hd

theorem cellAverage_inner_cell (L : ℕ) (f : QHilbert) (d : ℕ)
    (hd : d ∈ L.divisors) :
    inner ℝ (cellAverage L f) (eventVector (gcdCell L d)) =
      inner ℝ f (eventVector (gcdCell L d)) := by
  classical
  rw [cellAverage, sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_eq_single d]
  · rw [gcdCell_inner, if_pos rfl,
      div_mul_cancel₀ _ (ne_of_gt (gcdCell_mass_pos L d hd))]
  · intro e he hne
    rw [gcdCell_inner, if_neg hne, mul_zero]
  · intro hnot
    exact (hnot hd).elim

theorem conditionalProjection_eq_cellAverage (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    conditionalProjection L f = cellAverage L f := by
  apply conditional_eq_of_match L f _ (cellAverage_mem L hL f)
  intro d hd
  simp_rw [divisor_eq_sum_gcdCells L d hL (Nat.dvd_of_mem_divisors hd),
    inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro e he
  rw [cellAverage_inner_cell L f e he]

/-- The exact finite screened physical Gram formula. The infinite physical
tail is in every numerator and every strictly positive denominator. -/
theorem conditionalProjection_norm_sq (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    ‖conditionalProjection L f‖ ^ 2 =
      ∑ d ∈ L.divisors,
        (inner ℝ f (eventVector (gcdCell L d))) ^ 2 / eventMass (gcdCell L d) := by
  rw [conditionalProjection_eq_cellAverage L hL f]
  calc
    ‖cellAverage L f‖ ^ 2 = inner ℝ (cellAverage L f) (cellAverage L f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = _ := by
      change inner ℝ (cellAverage L f)
        (∑ d ∈ L.divisors,
          (inner ℝ f (eventVector (gcdCell L d)) / eventMass (gcdCell L d)) •
            eventVector (gcdCell L d)) = _
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [inner_smul_right, cellAverage_inner_cell L f d hd]
      ring

end RiemannResearch.RH.QGcdCellProjection
