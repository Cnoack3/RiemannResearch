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

/-- The repeated diagonal restriction–corestriction sum equals the original
class when its total degree is congruent to one modulo an annihilator.

Source: the proof strategy of Proposition 6.34 on page 36 of the
user-provided E8 Serre II memorandum. -/
theorem diagonalCorestriction_eq_of_annihilator_bezout
    {ι A : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (s : Finset ι) (degree multiplicity : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    {a : A} {e q : ℕ}
    (he : e • a = 0)
    (hcoefficient :
      ∑ i ∈ s, multiplicity i * degree i = 1 + q * e) :
    (∑ i ∈ s, multiplicity i • cor i (res i a)) = a := by
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
    _ = a := by
      rw [hcoefficient, add_nsmul, one_nsmul, ← smul_smul,
        he, smul_zero, add_zero]

/-- At the additive restriction–corestriction boundary, neutrality of the
diagonal value selected in PDF Proposition 6.34 is equivalent to neutrality of
the original class. Thus this diagonal kernel-membership assertion is not an
independent consequence of the Bézout data. -/
theorem diagonalKernelNorm_iff_neutral
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (neutral : X) (toClass : A → X)
    (s : Finset ι) (degree multiplicity : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    {a : A} {e q : ℕ}
    (he : e • a = 0)
    (hcoefficient :
      ∑ i ∈ s, multiplicity i * degree i = 1 + q * e) :
    toClass (∑ i ∈ s, multiplicity i • cor i (res i a)) = neutral ↔
      toClass a = neutral := by
  rw [diagonalCorestriction_eq_of_annihilator_bezout
    B s degree multiplicity res cor hindex he hcoefficient]

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
    toClass a = neutral :=
  (diagonalKernelNorm_iff_neutral
    B neutral toClass s degree multiplicity res cor hindex he hcoefficient).mp
    hkernelNorm

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

/-- The universal finite-etale kernel-norm principle: for every tuple of
locally neutral classes and every nonnegative multiplicity function, the
corestricted sum maps to the global neutral point.

This is the abstract logical shape of Conjecture 6.33. It does not construct
the required E8 restriction, corestriction, or pointed cohomology maps. -/
def UniversalFiniteEtaleKernelNormPrinciple
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (cor : ∀ i, B i →+ A) : Prop :=
  ∀ (multiplicity : ι → ℕ) (x : ∀ i, B i),
    (∀ i ∈ s, localClass i (x i) = localNeutral i) →
      toClass (∑ i ∈ s, multiplicity i • cor i (x i)) = neutral

/-- If every global class is neutral, the universal finite-etale kernel-norm
principle is automatic. This is the abstract reverse direction of PDF
Proposition 6.35. -/
theorem universalFiniteEtaleKernelNormPrinciple_of_all_classes_neutral
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (cor : ∀ i, B i →+ A)
    (allNeutral : ∀ a : A, toClass a = neutral) :
    UniversalFiniteEtaleKernelNormPrinciple
      B Y neutral localNeutral toClass localClass s cor := by
  intro multiplicity x hx
  exact allNeutral _

/-- Under explicit restriction-corestriction and local Bezout data for every
global class, the universal finite-etale kernel-norm principle forces every
global class to be neutral. This packages the abstract forward implication of
PDF Propositions 6.34--6.35.

For E8, providing localBezoutData and the universal kernel-norm principle is
the open mathematical content; this theorem only checks the deduction. -/
theorem all_classes_neutral_of_universalFiniteEtaleKernelNormPrinciple
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (degree : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    (kernelNorm :
      UniversalFiniteEtaleKernelNormPrinciple
        B Y neutral localNeutral toClass localClass s cor)
    (localBezoutData :
      ∀ a : A, ∃ e q : ℕ, ∃ multiplicity : ι → ℕ,
        e • a = 0 ∧
        (∑ i ∈ s, multiplicity i * degree i = 1 + q * e) ∧
        ∀ i ∈ s, localClass i (res i a) = localNeutral i) :
    ∀ a : A, toClass a = neutral := by
  intro a
  obtain ⟨e, q, multiplicity, he, hcoefficient, hrestrictedKernel⟩ :=
    localBezoutData a
  exact eq_neutral_of_finiteEtaleKernelNorm
    B Y neutral localNeutral toClass localClass s degree multiplicity
    res cor hindex he hcoefficient hrestrictedKernel (kernelNorm multiplicity)

/-- With exact local restriction-corestriction and Bezout data, the universal
finite-etale kernel-norm principle is equivalent to neutrality of every global
class. This is a formal logical equivalence, not a proof of its E8 instance. -/
theorem universalFiniteEtaleKernelNormPrinciple_iff_all_classes_neutral
    {ι A X : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (neutral : X) (localNeutral : ∀ i, Y i)
    (toClass : A → X) (localClass : ∀ i, B i → Y i)
    (s : Finset ι) (degree : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i x, cor i (res i x) = degree i • x)
    (localBezoutData :
      ∀ a : A, ∃ e q : ℕ, ∃ multiplicity : ι → ℕ,
        e • a = 0 ∧
        (∑ i ∈ s, multiplicity i * degree i = 1 + q * e) ∧
        ∀ i ∈ s, localClass i (res i a) = localNeutral i) :
    UniversalFiniteEtaleKernelNormPrinciple
        B Y neutral localNeutral toClass localClass s cor ↔
      ∀ a : A, toClass a = neutral := by
  constructor
  · intro kernelNorm
    exact all_classes_neutral_of_universalFiniteEtaleKernelNormPrinciple
      B Y neutral localNeutral toClass localClass s degree res cor hindex
      kernelNorm localBezoutData
  · exact universalFiniteEtaleKernelNormPrinciple_of_all_classes_neutral
      B Y neutral localNeutral toClass localClass s cor

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
