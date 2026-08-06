/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib

/-!
# The quasisimple core of full-Weyl descent

This module formalizes the logical and finite-group core of the theorem
`The quasisimple core of full-Weyl descent` in the Serre II / `E₈` program.

Mathlib does not currently provide the split algebraic group of type `E₈`,
its Weyl group and root lattice, nonabelian Galois `H¹` for algebraic groups,
or Gille's restriction-kernel theorems. Consequently, the main theorem below
states those inputs explicitly:

* restriction across the quadratic field `k⁺ / k`;
* neutralization over `F` by cyclic-prime torus splitting;
* the identifications
  `Gal(F / k⁺) ≃ W⁺ / Z ≃ Ω₈⁺(2)`, together with the order and simplicity
  of the last group;
* the finite diagonalizable-subgroup criterion which turns a fixed lattice
  vector into neutrality over a Sylow fixed field.

No axiom is introduced. Under these named hypotheses, Lean proves parts
(i)--(iii), the displayed order, noncommutativity of the simple core, and a
precise version of the final reduction-to-core-descent sentence.

The Sylow fixed-vector step is proved intrinsically. For `p = 7`, orbit
counting is stronger and shorter than the semisimple-module argument in the
document: `2 ^ 8 = 256` is not congruent to one modulo seven.

The source theorem's title uses “quasisimple”, while its statement proves that
the quotient `W⁺ / Z` is simple. Proving that `W⁺` itself is quasisimple
would additionally require perfectness of `W⁺` and identification of its
center with `Z`; those are not asserted here.
-/

namespace RiemannResearch.E8

/-- The primes occurring in the Sylow fixed-field assertion. -/
def fullWeylPrimes : Finset ℕ := {2, 3, 5, 7}

/-- The primes whose lattice quotient in the document is `L / pL`. -/
def modularFixedVectorPrimes : Finset ℕ := {2, 3, 5}

/-- A nonzero point fixed by every element of a multiplicative action. -/
def HasNonzeroFixedPoint (G V : Type*) [Group G] [Zero V] [SMul G V] : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ g : G, g • v = v

/-- Orbit counting for a finite `p`-group action.

If the cardinality of the additive group is not congruent to one modulo `p`,
its fixed-point set cannot consist only of zero.
-/
theorem exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one
    {p : ℕ} {G V : Type*} [Group G] [AddGroup V]
    [DistribMulAction G V] [Finite V] [Fact (Nat.Prime p)]
    (hG : IsPGroup p G) (hcard : ¬ Nat.card V ≡ 1 [MOD p]) :
    HasNonzeroFixedPoint G V := by
  by_contra hfixed
  have hsubsingleton : Subsingleton (MulAction.fixedPoints G V) := by
    constructor
    intro v w
    apply Subtype.ext
    have hv : v.1 = 0 := by
      by_contra hv0
      exact hfixed ⟨v.1, hv0, v.2⟩
    have hw : w.1 = 0 := by
      by_contra hw0
      exact hfixed ⟨w.1, hw0, w.2⟩
    exact hv.trans hw.symm
  have hnonempty : Nonempty (MulAction.fixedPoints G V) :=
    ⟨⟨0, by simp⟩⟩
  have hfixedCard : Nat.card (MulAction.fixedPoints G V) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsubsingleton, hnonempty⟩
  apply hcard
  have hmod := hG.card_modEq_card_fixedPoints V
  rwa [hfixedCard] at hmod

/-- The displayed order of `Ω₈⁺(2)` in decimal form. -/
theorem omegaEightPlusTwo_order :
    2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 = 174182400 := by
  norm_num

/-- A simple group of the displayed composite order is nonabelian. -/
theorem nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder
    {Ω : Type*} [Group Ω] [Finite Ω]
    (hsimple : IsSimpleGroup Ω)
    (hcard : Nat.card Ω = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7) :
    ∃ a b : Ω, a * b ≠ b * a := by
  by_contra hnonabelian
  simp only [not_exists, not_not] at hnonabelian
  let _ : IsMulCommutative Ω :=
    ⟨⟨fun a b => hnonabelian a b⟩⟩
  have hprime : Nat.Prime (Nat.card Ω) :=
    Group.is_simple_iff_prime_card.mp hsimple
  rw [hcard] at hprime
  norm_num at hprime

/-- The Lean-visible conclusions of the quasisimple-core theorem.

Here `neutralAtBase`, `neutralAtEvenField`, and
`neutralAtCentralField` mean respectively that `ξ`, `ξ_{k⁺}`, and
`ξ_F` are neutral. The indexed final predicate means that
`ξ_{E^{P_p}}` is neutral.
-/
structure FullWeylCoreConclusion
    (W Gal Ω : Type*) [Group W] [Group Gal] [Group Ω]
    (neutralAtBase neutralAtEvenField neutralAtCentralField : Prop)
    (neutralAtSylowFixedField : (p : ℕ) → Sylow p W → Prop) : Prop where
  /-- Part (i). -/
  base_iff_evenField : neutralAtBase ↔ neutralAtEvenField
  /-- The neutralization assertion in part (ii). -/
  neutral_centralField : neutralAtCentralField
  /-- The group identification in part (ii). -/
  gal_equiv_omega : Nonempty (Gal ≃* Ω)
  /-- The displayed order in part (ii). -/
  omega_order : Nat.card Ω = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7
  /-- Simplicity in part (ii). -/
  omega_simple : IsSimpleGroup Ω
  /-- Nonabelianness in part (ii), deduced from simplicity and composite order. -/
  omega_nonabelian : ∃ a b : Ω, a * b ≠ b * a
  /-- Part (iii). -/
  neutral_sylowFixedFields :
    ∀ p ∈ fullWeylPrimes, ∀ P : Sylow p W, neutralAtSylowFixedField p P
  /-- Precise form of the prose consequence: solving descent for the one class
  across `F / k⁺` is equivalent to solving the original descent problem. -/
  base_iff_coreDescent :
    neutralAtBase ↔ (neutralAtCentralField → neutralAtEvenField)

/-- Conditional formalization of “The quasisimple core of full-Weyl descent”.

The hypotheses are the exact formal boundary created by the currently
unavailable `E₈` and nonabelian-cohomology infrastructure. The arguments
internal to finite group actions and the logical assembly of parts (i)--(iii)
are proved, not assumed.
-/
theorem quasisimpleCoreOfFullWeylDescent
    {W Gal EvenQuotient Ω : Type*}
    [Group W] [Finite W] [Group Gal] [Group EvenQuotient]
    [Group Ω] [Finite Ω]
    {neutralAtBase neutralAtEvenField neutralAtCentralField : Prop}
    (neutralAtSylowFixedField : (p : ℕ) → Sylow p W → Prop)
    (V : (p : ℕ) → Sylow p W → Type*)
    [∀ (p : ℕ) (P : Sylow p W), AddCommGroup (V p P)]
    [∀ (p : ℕ) (P : Sylow p W), Finite (V p P)]
    [∀ (p : ℕ) (P : Sylow p W),
      DistribMulAction (↥(P : Subgroup W)) (V p P)]
    (restriction_preserves_neutrality :
      neutralAtBase → neutralAtEvenField)
    (quadratic_restriction_kernel :
      neutralAtEvenField → neutralAtBase)
    {centralTorusSplitByCyclicQuadratic : Prop}
    (central_torus_splitting : centralTorusSplitByCyclicQuadratic)
    (cyclic_prime_torus_kernel :
      centralTorusSplitByCyclicQuadratic → neutralAtCentralField)
    (gal_equiv_evenQuotient : Gal ≃* EvenQuotient)
    (evenQuotient_equiv_omega : EvenQuotient ≃* Ω)
    (omega_order :
      Nat.card Ω = 2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7)
    (omega_simple : IsSimpleGroup Ω)
    (smallPrime_card :
      ∀ p ∈ modularFixedVectorPrimes, ∀ P : Sylow p W,
        Nat.card (V p P) = p ^ 8)
    (seven_card :
      ∀ P : Sylow 7 W, Nat.card (V 7 P) = 2 ^ 8)
    (diagonalizable_subgroup_criterion :
      ∀ p ∈ fullWeylPrimes, ∀ P : Sylow p W,
        HasNonzeroFixedPoint (↥(P : Subgroup W)) (V p P) →
          neutralAtSylowFixedField p P) :
    FullWeylCoreConclusion W Gal Ω
      neutralAtBase neutralAtEvenField neutralAtCentralField
      neutralAtSylowFixedField := by
  have hcentral : neutralAtCentralField :=
    cyclic_prime_torus_kernel central_torus_splitting
  refine
    { base_iff_evenField :=
        ⟨restriction_preserves_neutrality, quadratic_restriction_kernel⟩
      neutral_centralField := hcentral
      gal_equiv_omega :=
        ⟨gal_equiv_evenQuotient.trans evenQuotient_equiv_omega⟩
      omega_order := omega_order
      omega_simple := omega_simple
      omega_nonabelian :=
        nonabelian_of_isSimpleGroup_of_card_eq_omegaOrder omega_simple omega_order
      neutral_sylowFixedFields := ?_
      base_iff_coreDescent := ?_ }
  · intro p hp P
    apply diagonalizable_subgroup_criterion p hp P
    have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      simpa [fullWeylPrimes] using hp
    rcases hp_cases with rfl | rfl | rfl | rfl
    · let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
      apply
        exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one P.isPGroup'
      rw [smallPrime_card 2 (by simp [modularFixedVectorPrimes]) P]
      norm_num
    · let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      apply
        exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one P.isPGroup'
      rw [smallPrime_card 3 (by simp [modularFixedVectorPrimes]) P]
      norm_num
    · let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      apply
        exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one P.isPGroup'
      rw [smallPrime_card 5 (by simp [modularFixedVectorPrimes]) P]
      norm_num
    · let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      apply
        exists_nonzero_fixedPoint_of_isPGroup_of_not_card_modEq_one P.isPGroup'
      rw [seven_card P]
      norm_num
  · constructor
    · intro hbase _
      exact restriction_preserves_neutrality hbase
    · intro hcoreDescent
      exact quadratic_restriction_kernel (hcoreDescent hcentral)

end RiemannResearch.E8
