/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PeriodicDivisorJumps
import RiemannResearch.RH.QSquarefreePeriodicJump
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.NumberTheory.SquarefreePowerCongruence
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q synthesis of periodic gcd-jump targets

This module integrates periodic gcd-class jumps into the actual Q Hilbert
space. The finite dictionary is the existing `divisorStage`, including
every composite divisor. The auxiliary physical coordinate zero is treated
separately: the periodic extension is shifted by one complete period.

The helper lemmas explicitly assume the gcd-jump relation; no arithmetic
provider or legal closure assertion is silently substituted for it.
For squarefree periods, the resulting cylinder target belongs to the
closed legal span precisely when its value at residue zero vanishes or
the constant itself belongs to that closure.

Source: `RH_CRT_Profinite_Research_Handoff_Verified_2100`, Section 10,
cylinder-intersection research target, and its finite divisor inversion.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeCylinder
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open SquarefreeRadicalDifference QSquarefreeLatticePackets PeriodicDivisorJumps

/-- Periodicity at every positive physical coordinate, without imposing a value at zero. -/
def PhysicalPeriodic (L : ℕ) (x : QHilbert) : Prop :=
  ∀ n : ℕ, 0 < n → qSequence x (n + L) = qSequence x n

/-- Positive physical periodicity iterates without changing the auxiliary zero site. -/
theorem qSequence_add_mul_period (L : ℕ) (x : QHilbert)
    (hp : PhysicalPeriodic L x) (n : ℕ) (hn : 0 < n) (k : ℕ) :
    qSequence x (n + k * L) = qSequence x n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, hp (n + k * L) (by omega), ih]

/-- Every complete positive jump inherits the period. -/
theorem qDifference_add_mul_period (L : ℕ) (x : QHilbert)
    (hp : PhysicalPeriodic L x) (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    qDifference x (n + k * L) = qDifference x n := by
  have he : n + k * L - 1 = (n - 1) + k * L := by omega
  unfold qDifference
  rw [qSequence_add_mul_period L x hp n (by omega), he,
    qSequence_add_mul_period L x hp (n - 1) (by omega)]

/-- Congruent positive jumps agree; both sites stay away from the auxiliary zero coordinate. -/
theorem qDifference_eq_of_modEq (L : ℕ) (x : QHilbert)
    (hp : PhysicalPeriodic L x) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (he : Nat.ModEq L n m) : qDifference x n = qDifference x m := by
  have hen : n % L + (n / L) * L = n := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div n L
  have hem : m % L + (m / L) * L = m := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div m L
  have hmod : n % L = m % L := he
  have hcross : n + (m / L) * L = m + (n / L) * L := by omega
  calc
    qDifference x n = qDifference x (n + (m / L) * L) :=
      (qDifference_add_mul_period L x hp n hn (m / L)).symm
    _ = qDifference x (m + (n / L) * L) := congrArg (qDifference x) hcross
    _ = qDifference x m := qDifference_add_mul_period L x hp m hm (n / L)

/-- Periodic members of the actual closed legal span have gcd-class jumps. -/
theorem squarefree_closure_gcd_jumps (L : ℕ) (hL : 0 < L) (hsf : Squarefree L)
    (x : QHilbert) (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure)
    (hp : PhysicalPeriodic L x) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hg : Nat.gcd n L = Nat.gcd m L) : qDifference x n = qDifference x m := by
  exact RiemannResearch.NumberTheory.SquarefreePowerCongruence.eq_of_gcd_eq
    L hL hsf (qDifference x) (qDifference_eq_of_modEq L x hp)
    (fun a k ha hk => QSquarefreePeriodicJump.squarefree_closure_difference_pow
      a k (by omega) hk x hx) n m hn hm hg

private theorem qSequence_synthesis (L : ℕ) (a : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    qSequence (a • qOne - ∑ d ∈ L.divisors, c d • qResidue d) n =
      a * qOneSequence n - ∑ d ∈ L.divisors, c d * residueFraction d n := by
  change qSequenceLinear (a • qOne - ∑ d ∈ L.divisors, c d • qResidue d) n = _
  simp only [map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  change a * qSequence qOne n - ∑ d ∈ L.divisors, c d * qSequence (qResidue d) n = _
  simp only [qSequence_qOne, qSequence_qResidue]

/-- A periodic Q vector with gcd-class jumps has an exact finite divisor synthesis. -/
theorem representation_of_gcd_jumps (L : ℕ) (hL : 0 < L)
    (x : QHilbert) (hp : PhysicalPeriodic L x)
    (hGcd : ∀ m a : ℕ, 2 ≤ m → 2 ≤ a → Nat.gcd m L = Nat.gcd a L →
      qDifference x m = qDifference x a) :
    ∃ v ∈ divisorStage L, x = (qSequence x L) • qOne + v := by
  let f : ℕ → ℝ := fun n => qSequence x (n + L)
  let h : ℕ → ℝ := fun d => qDifference x (d + L)
  let c : ℕ → ℝ := divisorCoefficients L h
  have hfper : f L = f 0 := by
    simpa only [f, zero_add] using hp L hL
  have hj : ∀ n, f (n + 1) - f n = h (Nat.gcd (n + 1) L) := by
    intro n
    have hgpos : 0 < Nat.gcd (n + 1) L := Nat.gcd_pos_of_pos_right (n + 1) hL
    have hg : Nat.gcd (n + 1 + L) L = Nat.gcd (Nat.gcd (n + 1) L + L) L := by
      simp [Nat.gcd_assoc]
    have he := hGcd (n + 1 + L) (Nat.gcd (n + 1) L + L)
      (by omega) (by omega) hg
    have hm : n + 1 + L - 1 = n + L := by omega
    simpa only [f, h, qDifference, hm] using he
  have hrep := periodic_gcd_jumps_representation L hL f h hfper hj
  have heq : x = (qSequence x L) • qOne -
      ∑ d ∈ L.divisors, c d • qResidue d := by
    apply qSequence_injective
    funext n
    rw [qSequence_synthesis]
    by_cases hn : n = 0
    · simp [hn, qOneSequence, residueFraction]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hh := hrep n
      dsimp only [f] at hh
      rw [hp n hnpos, zero_add] at hh
      simpa only [c, qOneSequence, if_neg hn, mul_one] using hh
  refine ⟨-(∑ d ∈ L.divisors, c d • qResidue d), ?_, ?_⟩
  · apply (divisorStage L).neg_mem
    apply (divisorStage L).sum_mem
    intro d hd
    exact (divisorStage L).smul_mem _
      (Submodule.subset_span ⟨d, Nat.dvd_of_mem_divisors hd, rfl⟩)
  · simpa only [sub_eq_add_neg] using heq

/-- The only potentially nonlegal component is the constant coefficient at residue zero. -/
theorem mem_closure_iff_of_gcd_jumps (L : ℕ) (hL : 0 < L)
    (hsf : Squarefree L) (x : QHilbert) (hp : PhysicalPeriodic L x)
    (hGcd : ∀ m a : ℕ, 2 ≤ m → 2 ≤ a → Nat.gcd m L = Nat.gcd a L →
      qDifference x m = qDifference x a) :
    x ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      qSequence x L = 0 ∨ qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  obtain ⟨v, hv, heq⟩ := representation_of_gcd_jumps L hL x hp hGcd
  have hvH : v ∈ qSquarefreeCRTSpan.topologicalClosure :=
    qSquarefreeCRTSpan.le_topologicalClosure
      (divisorStage_le_squarefreeSpan L hL hsf hv)
  constructor
  · intro hx
    by_cases hz : qSequence x L = 0
    · exact Or.inl hz
    · right
      have hc : (qSequence x L) • qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
        have hs := qSquarefreeCRTSpan.topologicalClosure.sub_mem hx hvH
        rw [heq, add_sub_cancel_right] at hs
        exact hs
      have hs := qSquarefreeCRTSpan.topologicalClosure.smul_mem (qSequence x L)⁻¹ hc
      simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using hs
  · rintro (hz | hone)
    · rw [heq, hz, zero_smul, zero_add]
      exact hvH
    · rw [heq]
      exact qSquarefreeCRTSpan.topologicalClosure.add_mem
        (qSquarefreeCRTSpan.topologicalClosure.smul_mem _ hone) hvH

/-- A nonzero residue-zero coefficient gives exactly the constant closure obligation. -/
theorem mem_closure_iff_qOne_of_gcd_jumps (L : ℕ) (hL : 0 < L)
    (hsf : Squarefree L) (x : QHilbert) (hp : PhysicalPeriodic L x)
    (hGcd : ∀ m a : ℕ, 2 ≤ m → 2 ≤ a → Nat.gcd m L = Nat.gcd a L →
      qDifference x m = qDifference x a) (hxL : qSequence x L ≠ 0) :
    x ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  rw [mem_closure_iff_of_gcd_jumps L hL hsf x hp hGcd]
  simp only [hxL, false_or]

/-- The cylinder-intersection theorem: every legal squarefree-periodic target
is its residue-zero value times the constant plus a legal finite divisor vector. -/
theorem squarefree_cylinder_representation (L : ℕ) (hL : 0 < L)
    (hsf : Squarefree L) (x : QHilbert)
    (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) (hp : PhysicalPeriodic L x) :
    ∃ v ∈ divisorStage L, x = (qSequence x L) • qOne + v :=
  representation_of_gcd_jumps L hL x hp (squarefree_closure_gcd_jumps L hL hsf x hx hp)

/-- A periodic legal target with nonzero value at residue zero forces constant membership. -/
theorem qOne_mem_closure_of_periodic_nonzero (L : ℕ) (hL : 0 < L)
    (hsf : Squarefree L) (x : QHilbert)
    (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) (hp : PhysicalPeriodic L x)
    (hxL : qSequence x L ≠ 0) : qOne ∈ qSquarefreeCRTSpan.topologicalClosure :=
  (mem_closure_iff_qOne_of_gcd_jumps L hL hsf x hp
    (squarefree_closure_gcd_jumps L hL hsf x hx hp) hxL).mp hx

/-- Zero residue-zero value removes the constant direction completely. -/
theorem mem_divisorStage_of_periodic_zero (L : ℕ) (hL : 0 < L)
    (hsf : Squarefree L) (x : QHilbert)
    (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) (hp : PhysicalPeriodic L x)
    (hxL : qSequence x L = 0) : x ∈ divisorStage L := by
  obtain ⟨v, hv, heq⟩ := squarefree_cylinder_representation L hL hsf x hx hp
  rw [hxL, zero_smul, zero_add] at heq
  exact heq.symm ▸ hv

end RiemannResearch.RH.QSquarefreeCylinder
