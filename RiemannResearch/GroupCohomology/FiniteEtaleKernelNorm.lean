/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite-étale kernel–norm implications

This module isolates the additive restriction–corestriction argument behind
completion target C in the 5 August 2026 E8 Serre II memorandum. A diagonal
kernel–norm value and a positive Bézout congruence force the original class to
map to the neutral point. A finite-étale family form and an abstract `ZMod 2`
countermodel record exactly what the argument does and does not prove.

These results are generic additive algebra. They do not assert the required E8
kernel–norm hypothesis.
-/

namespace RiemannResearch.GroupCohomology

/-- A diagonal restriction–corestriction value equals the original class when
its total degree is congruent to one modulo an annihilator. Therefore neutrality
of that diagonal value implies neutrality of the original class. -/
theorem eq_neutral_of_diagonalKernelNorm
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (neutral : X) (toClass : A → X)
    (s : Finset ι) (degree multiplicity : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    {a : A} {e q : ℕ}
    (he : e • a = 0)
    (hcoefficient :
      ∑ i ∈ s, multiplicity i * degree i = 1 + q * e)
    (hkernelNorm :
      toClass (∑ i ∈ s, multiplicity i • cor i (res i a)) = neutral) :
    toClass a = neutral := by
  have hcorestriction :
      (∑ i ∈ s, multiplicity i • cor i (res i a)) =
        (∑ i ∈ s, multiplicity i * degree i) • a := by
    calc
      (∑ i ∈ s, multiplicity i • cor i (res i a)) =
          ∑ i ∈ s, multiplicity i • (degree i • a) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hindex i a]
      _ = ∑ i ∈ s, (multiplicity i * degree i) • a := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [smul_smul]
      _ = (∑ i ∈ s, multiplicity i * degree i) • a :=
        Finset.sum_smul.symm
  have hmultiple :
      (∑ i ∈ s, multiplicity i * degree i) • a = a := by
    rw [hcoefficient, add_nsmul, one_nsmul, ← smul_smul,
      he, smul_zero, add_zero]
  rw [hcorestriction, hmultiple] at hkernelNorm
  exact hkernelNorm

/-- The finite-étale form: componentwise local neutrality and a finite-étale
kernel–norm principle provide the diagonal hypothesis above. -/
theorem eq_neutral_of_finiteEtaleKernelNorm
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (degree multiplicity : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    {a : A} {e q : ℕ}
    (he : e • a = 0)
    (hcoefficient :
      ∑ i ∈ s, multiplicity i * degree i = 1 + q * e)
    (hrestrictedKernel :
      ∀ i ∈ s, localClass i (res i a) = localNeutral i)
    (finiteEtaleKernelNorm :
      ∀ x : ∀ i, B i,
        (∀ i ∈ s, localClass i (x i) = localNeutral i) →
        toClass (∑ i ∈ s, multiplicity i • cor i (x i)) = neutral) :
    toClass a = neutral := by
  apply eq_neutral_of_diagonalKernelNorm B neutral toClass s degree multiplicity
    res cor hindex he hcoefficient
  apply finiteEtaleKernelNorm (fun i => res i a)
  exact hrestrictedKernel

/-- If the target pointed set is a subsingleton, every finite-étale
kernel–norm statement is automatic. -/
theorem finiteEtaleKernelNorm_of_subsingleton_target
    {ι A X : Type*} [AddCommGroup A] [Subsingleton X]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (multiplicity : ι → ℕ)
    (cor : ∀ i, B i →+ A) :
    ∀ x : ∀ i, B i,
      (∀ i ∈ s, localClass i (x i) = localNeutral i) →
      toClass (∑ i ∈ s, multiplicity i • cor i (x i)) = neutral := by
  intro x hx
  exact Subsingleton.elim _ _

/-- Additive restriction–corestriction and Bézout data alone do not imply the
diagonal kernel–norm principle. This is an abstract obstruction, not an E8
counterexample. -/
theorem zmodTwo_diagonalKernelNorm_counterexample :
    let A := ZMod 2
    let res : A →+ A := AddMonoidHom.id A
    let cor : A →+ A := AddMonoidHom.id A
    let localClass : A → Unit := fun _ => ()
    let toClass : A → A := id
    let a : A := 1
    (∀ x, cor (res x) = 3 • x) ∧
      2 • a = 0 ∧
      3 = 1 + 1 * 2 ∧
      localClass (res a) = () ∧
      toClass (cor (res a)) ≠ 0 := by
  dsimp
  constructor
  · intro x
    rw [show 3 = 1 + 2 by norm_num, add_nsmul, one_nsmul,
      CharTwo.two_nsmul, add_zero]
  constructor
  · exact CharTwo.two_nsmul 1
  constructor
  · norm_num
  constructor
  · rfl
  · norm_num

end RiemannResearch.GroupCohomology
