/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeCRTCarries
import RiemannResearch.RH.QUnconditionalAtomSeries
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Simultaneous CRT for the entire squarefree atom dictionary

Source: user-provided request to apply CRT to all squarefree atoms,
25 October 2026. The canonical floor-carry theorem is the existing
`QPrimeCRTCarries.canonical_prime_carry` and its Q-Hilbert encoding.
The global result is an exact equality of algebraic spans, hence of norm
closures. No summation rearrangement or target-density claim is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QSimultaneousCRT
open ZetaTwoHilbert ZetaTwoProbability QPrimeCRTCarries ArithmeticCumulative

abbrev SquarefreeConductor := {d : ℕ // 2 ≤ d ∧ Squarefree d}

/-- The finite prime synthesis attached to a single squarefree conductor. -/
def primeSynthesis (d : ℕ) : QHilbert :=
  ∑ p : d.primeFactors, (canonicalCoefficient d p.val : ℝ) • qResidue p.val

/-- The canonical CRT carry encoded by the existing literal carry vector. -/
def canonicalCarry (d : ℕ) : QHilbert :=
  carryVector d (fun p : d.primeFactors => p.val)
    (fun p : d.primeFactors => (canonicalCoefficient d p.val : ℤ))

theorem canonicalCarry_eq (d : ℕ) :
    canonicalCarry d = primeSynthesis d - qResidue d := by
  simp only [canonicalCarry, carryVector, primeSynthesis, Int.cast_natCast]

theorem residue_eq_prime_sub_carry (d : ℕ) :
    qResidue d = primeSynthesis d - canonicalCarry d := by
  rw [canonicalCarry_eq]
  abel

/-- The canonical encoded carry is genuinely the floor of the CRT prime sum. -/
theorem canonicalCarry_sequence (d : ℕ) (hd : 0 < d) (hsf : Squarefree d)
    (n : ℕ) :
    qSequence (canonicalCarry d) n =
      (⌊∑ p ∈ d.primeFactors, (canonicalCoefficient d p : ℝ) *
        residueFraction p n⌋ : ℝ) := by
  have hsumZ : (∑ p : d.primeFactors,
      ((d / p.val : ℕ) : ℤ) * (canonicalCoefficient d p.val : ℤ)) =
      ∑ p ∈ d.primeFactors,
        ((d / p : ℕ) : ℤ) * (canonicalCoefficient d p : ℤ) :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => ((d / p : ℕ) : ℤ) * (canonicalCoefficient d p : ℤ))
  have hsumR : (∑ p : d.primeFactors,
      (canonicalCoefficient d p.val : ℝ) * residueFraction p.val n) =
      ∑ p ∈ d.primeFactors,
        (canonicalCoefficient d p : ℝ) * residueFraction p n :=
    Finset.sum_coe_sort d.primeFactors
      (fun p : ℕ => (canonicalCoefficient d p : ℝ) * residueFraction p n)
  have hcert : ((∑ p : d.primeFactors,
      ((d / p.val : ℕ) : ℤ) * (canonicalCoefficient d p.val : ℤ) : ℤ) :
      ZMod d) = 1 := by
    rw [hsumZ]
    exact canonical_modular_certificate d hsf
  have h := carryVector_sequence d hd
    (fun p : d.primeFactors => p.val)
    (fun p => (Nat.mem_primeFactors.mp p.property).1.pos)
    (fun p => (Nat.mem_primeFactors.mp p.property).2.1)
    (fun p : d.primeFactors => (canonicalCoefficient d p.val : ℤ)) hcert n
  simpa only [canonicalCarry, carry, Int.cast_natCast, hsumR] using h

def primeSpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun p : {p : ℕ // p.Prime} => qResidue p.val))

def carrySpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun d : SquarefreeConductor => canonicalCarry d.val))

theorem primeSynthesis_mem_primeSpan (d : ℕ) : primeSynthesis d ∈ primeSpan := by
  unfold primeSynthesis
  apply primeSpan.sum_mem
  intro p _
  apply primeSpan.smul_mem
  exact Submodule.subset_span ⟨⟨p.val, (Nat.mem_primeFactors.mp p.property).1⟩, rfl⟩

theorem primeSpan_le_squarefreeSpan : primeSpan ≤ qSquarefreeCRTSpan := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact Submodule.subset_span ⟨⟨p.val, p.property.two_le, p.property.squarefree⟩, rfl⟩

theorem canonicalCarry_mem_squarefreeSpan (d : SquarefreeConductor) :
    canonicalCarry d.val ∈ qSquarefreeCRTSpan := by
  apply carryVector_mem_squarefreeSpan d.val (by have := d.property.1; omega)
    d.property.2
  intro p
  exact (Nat.mem_primeFactors.mp p.property).2.1

theorem carrySpan_le_squarefreeSpan : carrySpan ≤ qSquarefreeCRTSpan := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  exact canonicalCarry_mem_squarefreeSpan d

/-- Simultaneous CRT for every squarefree conductor is an exact change of generators. -/
theorem squarefreeSpan_eq_prime_sup_carry :
    qSquarefreeCRTSpan = primeSpan ⊔ carrySpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    have hp : primeSynthesis d.val ∈ primeSpan ⊔ carrySpan :=
      (show primeSpan ≤ primeSpan ⊔ carrySpan from le_sup_left)
        (primeSynthesis_mem_primeSpan d.val)
    have hc : canonicalCarry d.val ∈ primeSpan ⊔ carrySpan :=
      (show carrySpan ≤ primeSpan ⊔ carrySpan from le_sup_right)
        (Submodule.subset_span ⟨d, rfl⟩)
    change qResidue d.val ∈ primeSpan ⊔ carrySpan
    rw [residue_eq_prime_sub_carry d.val]
    exact (primeSpan ⊔ carrySpan).sub_mem hp hc
  · exact sup_le primeSpan_le_squarefreeSpan carrySpan_le_squarefreeSpan

theorem squarefreeClosedSpan_eq_prime_carry_closedSpan :
    qSquarefreeCRTSpan.topologicalClosure =
      (primeSpan ⊔ carrySpan).topologicalClosure := by
  rw [squarefreeSpan_eq_prime_sup_carry]

/-- All signed carries are retained for an arbitrary finite coefficient family. -/
theorem finite_synthesis_identity (s : Finset ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ s, c d • qResidue d) =
      (∑ d ∈ s, c d • primeSynthesis d) -
        ∑ d ∈ s, c d • canonicalCarry d := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← smul_sub, ← residue_eq_prime_sub_carry]

/-- Passing the CRT decomposition through an infinite sum requires actual
convergence of both separated series; no such convergence is supplied by CRT. -/
theorem hasSum_of_separated_prime_carry_sums
    (c : SquarefreeConductor → ℝ) (P C : QHilbert)
    (hP : HasSum (fun d => c d • primeSynthesis d.val) P)
    (hC : HasSum (fun d => c d • canonicalCarry d.val) C) :
    HasSum (fun d => c d • qResidue d.val) (P - C) := by
  convert hP.sub hC using 1
  funext d
  rw [← smul_sub, ← residue_eq_prime_sub_carry]

/-- Separately summing the prime and carry parts cannot reconstruct one as an
unordered sum of individual squarefree atoms. Ordered block limits are not excluded. -/
theorem separated_prime_carry_difference_ne_one
    (c : SquarefreeConductor → ℝ) (P C : QHilbert)
    (hP : HasSum (fun d => c d • primeSynthesis d.val) P)
    (hC : HasSum (fun d => c d • canonicalCarry d.val) C) :
    P - C ≠ qOne := by
  intro h
  have hs := hasSum_of_separated_prime_carry_sums c P C hP hC
  rw [h] at hs
  exact QUnconditionalAtomSeries.no_hasSum_squarefree_subtype_qOne c hs

end RiemannResearch.RH.QSimultaneousCRT
