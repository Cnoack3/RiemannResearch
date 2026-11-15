/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTCellCoordinateSystem
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact finite residue sums for the actual canonical cell system

Source: CanonicalPrimePowerUpdatesResearch20261107, Section 6. These formulas
attach finite rational residue calculations to the full infinite Q pairings.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPeriodicCellSystem
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open QCRTFiniteCollocation QGcdCellRefinement QGcdCellProjection QCRTCellCoordinateSystem
open ArithmeticCumulative

theorem residueFraction_abs_le_one (d n : ℕ) : |residueFraction d n| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, residueFraction]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hdR).mpr
    simpa only [one_mul] using (show ((n % d : ℕ) : ℝ) ≤ (d : ℝ) by
      exact_mod_cast (Nat.mod_lt n hdpos).le)

theorem cellMatrix_eq_residue_sum (L : ℕ) (hL : 0 < L) (e : ℕ)
    (d : TrialIndex L) :
    cellMatrix L e d = ∑ r : Fin L,
      residuePowerWeight 0 L (r.val + 1) *
        (residueFraction d (r.val + 1) *
          (if Nat.gcd (r.val + 1) L = e then (1 : ℝ) else 0)) := by
  classical
  let f : ℕ → ℝ := fun n => residueFraction d n *
    (if Nat.gcd n L = e then (1 : ℝ) else 0)
  have hf : ∀ n, |f n| ≤ 1 := by
    intro n
    dsimp [f]
    split_ifs <;> simp [residueFraction_abs_le_one]
  have hdL : (d : ℕ) ∣ L := Nat.dvd_of_mem_divisors (Finset.mem_erase.mp d.property).2
  have hp : ∀ n, f (n + L) = f n := by
    intro n
    dsimp [f]
    have hr : residueFraction d (n + L) = residueFraction d n := by
      simp only [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdL,
        add_zero, Nat.mod_mod]
    rw [hr, Nat.gcd_add_self_left]
  have he : cellMatrix L e d = inversePowerMean 0 f := by
    unfold cellMatrix
    rw [qInner_weighted,
      (qSequence_product_summable (qResidue d) (eventVector (gcdCell L e))).tsum_eq_zero_add]
    simp only [qSequence_zero, mul_zero, zero_add, qSequence_qResidue, qSequence_eventVector]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [f, eventSequence, Nat.succ_ne_zero, if_false, gcdCell, Set.mem_ofPred_eq,
      positiveQWeight, Nat.zero_add]
    ring
  rw [he, periodic_inversePowerMean 0 L hL f hf hp]

theorem gcdCell_mass_eq_residue_sum (L : ℕ) (hL : 0 < L) (e : ℕ) :
    eventMass (gcdCell L e) = ∑ r : Fin L,
      residuePowerWeight 0 L (r.val + 1) *
        (if Nat.gcd (r.val + 1) L = e then (1 : ℝ) else 0) := by
  classical
  let f : ℕ → ℝ := fun n => if Nat.gcd n L = e then 1 else 0
  have hf : ∀ n, |f n| ≤ 1 := by intro n; dsimp [f]; split_ifs <;> norm_num
  have hp : ∀ n, f (n + L) = f n := by intro n; simp only [f, Nat.gcd_add_self_left]
  have he : eventMass (gcdCell L e) = inversePowerMean 0 f := by
    unfold eventMass
    rw [(eventMass_summable (gcdCell L e)).tsum_eq_zero_add]
    rw [show eventSequence (gcdCell L e) 0 = 0 by simp [eventSequence], mul_zero, zero_add]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [f, eventSequence, Nat.succ_ne_zero, if_false, gcdCell, Set.mem_ofPred_eq,
      positiveQWeight, Nat.zero_add]
    ring
  rw [he, periodic_inversePowerMean 0 L hL f hf hp]

theorem cellTarget_eq_mass (L e : ℕ) (he : e ≠ L) :
    cellTarget L e = eventMass (gcdCell L e) := by
  classical
  unfold cellTarget
  rw [target, qInner_weighted]
  change (∑' n : ℕ, positiveQWeight n *
    qSequenceLinear (qOne - qDivisor L) n * qSequence (eventVector (gcdCell L e)) n) = _
  simp only [map_sub, Pi.sub_apply, qSequence_eventVector]
  simp only [qSequenceLinear]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [eventSequence, hn]
  · by_cases hg : Nat.gcd n L = e
    · have hnot : ¬ L ∣ n := by
        intro h
        have heq := Nat.gcd_eq_right h
        exact he (hg.symm.trans heq)
      simp [eventSequence, gcdCell, hg, hn, qOneSequence, positiveDivisor, hnot]
    · simp [eventSequence, gcdCell, hg, hn]

theorem cellTarget_eq_residue_sum (L : ℕ) (hL : 0 < L) (e : ℕ) (he : e ≠ L) :
    cellTarget L e = ∑ r : Fin L,
      residuePowerWeight 0 L (r.val + 1) *
        (if Nat.gcd (r.val + 1) L = e then (1 : ℝ) else 0) := by
  rw [cellTarget_eq_mass L e he, gcdCell_mass_eq_residue_sum L hL e]

end RiemannResearch.RH.QCRTPeriodicCellSystem
