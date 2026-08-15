/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornFockGenerators

/-!
# Preservation laws for the split Fock/Zorn chart

This module proves that the vector and two exterior-Fock representations,
transported through the split Zorn Fock chart, preserve the split Zorn norm
and triality tensor. The proof first identifies the two parity-changing
Clifford generators as adjoints for the polar form, extends this identity from
pairs of generators to the even Clifford algebra by even induction, and then
uses the spin norm-one equation. The tensor identity follows from the full
Fock generator intertwining law and cyclicity of the Zorn tensor.

The related-triple proof strategy follows Alsaody--Gille, *Isotopes of
Octonion Algebras, G2-Torsors and Triality*, Proposition 3.10 and
Theorem 3.12: <https://arxiv.org/abs/1704.05229>.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open CliffordAlgebra
open RiemannResearch.LinearAlgebra
open RiemannResearch.LinearAlgebra.CliffordEven

universe u

noncomputable section

variable (K : Type u) [Field K] [Invertible (2 : K)]

namespace Zorn

/-- The polar bilinear form of the split Zorn norm. -/
def normPolarBilinear : LinearMap.BilinForm K (Octonion K) :=
  QuadraticMap.polarBilin (normForm K)

omit [Invertible (2 : K)] in
@[simp] theorem normPolarBilinear_apply (x y : Octonion K) :
    normPolarBilinear K x y = normPolar K x y :=
  rfl

omit [Invertible (2 : K)] in
/-- The diagonal of the polar form is twice the quadratic norm. -/
theorem normPolarBilinear_self (x : Octonion K) :
    normPolarBilinear K x x = (2 : K) * normForm K x := by
  simp [normPolarBilinear, normForm, norm]

end Zorn

/-- The Zorn polar form transported to positive Fock parity. -/
def splitFockEvenNormPolar : LinearMap.BilinForm K (SplitFockEven K) :=
  (Zorn.normPolarBilinear K).comp
    (splitFockEvenZornEquiv K).toLinearMap
    (splitFockEvenZornEquiv K).toLinearMap

/-- The Zorn polar form transported to negative Fock parity. -/
def splitFockOddNormPolar : LinearMap.BilinForm K (SplitFockOdd K) :=
  (Zorn.normPolarBilinear K).comp
    (splitFockOddZornEquiv K).toLinearMap
    (splitFockOddZornEquiv K).toLinearMap

omit [Invertible (2 : K)] in
private theorem splitFockEvenNormPolar_symm
    (p q : SplitFockEven K) :
    splitFockEvenNormPolar K p q =
      splitFockEvenNormPolar K q p := by
  simp only [splitFockEvenNormPolar, LinearMap.BilinForm.comp_apply,
    Zorn.normPolarBilinear]
  exact QuadraticMap.polar_comm _ _ _

omit [Invertible (2 : K)] in
private theorem splitFockOddNormPolar_symm
    (p q : SplitFockOdd K) :
    splitFockOddNormPolar K p q =
      splitFockOddNormPolar K q p := by
  simp only [splitFockOddNormPolar, LinearMap.BilinForm.comp_apply,
    Zorn.normPolarBilinear]
  exact QuadraticMap.polar_comm _ _ _

omit [Invertible (2 : K)] in
/-- The positive-to-negative and negative-to-positive Fock generators are
adjoint for the two Zorn polar forms. -/
theorem splitFockGenerator_isAdjointPair (x : SplitD4Space K) :
    (splitFockEvenNormPolar K).IsAdjointPair
      (splitFockOddNormPolar K)
      (splitFockGeneratorEvenToOdd K x)
      (splitFockGeneratorOddToEven K x) := by
  intro p m
  simp only [splitFockEvenNormPolar, splitFockOddNormPolar,
    LinearMap.BilinForm.comp_apply, Zorn.normPolarBilinear_apply]
  have hEO :
      (↑(splitFockOddZornEquiv K) :
        SplitFockOdd K → Zorn.Octonion K)
          (splitFockGeneratorEvenToOdd K x p) =
        Zorn.paraMul K (splitVectorZornEquiv K x)
          (splitFockEvenZornEquiv K p) :=
    splitFockGeneratorEvenToOdd_chart K x p
  have hOE :
      (↑(splitFockEvenZornEquiv K) :
        SplitFockEven K → Zorn.Octonion K)
          (splitFockGeneratorOddToEven K x m) =
        Zorn.paraMul K (splitFockOddZornEquiv K m)
          (splitVectorZornEquiv K x) :=
    splitFockGeneratorOddToEven_chart K x m
  change
    Zorn.normPolar K
        (splitFockOddZornEquiv K
          (splitFockGeneratorEvenToOdd K x p))
        (splitFockOddZornEquiv K m) =
      Zorn.normPolar K (splitFockEvenZornEquiv K p)
        (splitFockEvenZornEquiv K
          (splitFockGeneratorOddToEven K x m))
  rw [hEO, hOE]
  change
    QuadraticMap.polar (Zorn.normForm K)
        (Zorn.paraMul K (splitVectorZornEquiv K x)
          (splitFockEvenZornEquiv K p))
        (splitFockOddZornEquiv K m) =
      Zorn.normPolar K (splitFockEvenZornEquiv K p)
        (Zorn.paraMul K (splitFockOddZornEquiv K m)
          (splitVectorZornEquiv K x))
  rw [QuadraticMap.polar_comm]
  exact Zorn.trialityTensor_cycle_two K _ _ _

private def evenCliffordElement
    (a : CliffordAlgebra (splitD4Form K))
    (ha : a ∈ CliffordAlgebra.evenOdd (splitD4Form K) 0) :
    CliffordAlgebra.even (splitD4Form K) :=
  ⟨a, by
    change a ∈ (CliffordAlgebra.even (splitD4Form K)).toSubmodule
    rw [CliffordAlgebra.even_toSubmodule]
    exact ha⟩

private def reverseEvenCliffordElement
    (a : CliffordAlgebra (splitD4Form K))
    (ha : a ∈ CliffordAlgebra.evenOdd (splitD4Form K) 0) :
    CliffordAlgebra.even (splitD4Form K) :=
  ⟨CliffordAlgebra.reverse a, by
    change CliffordAlgebra.reverse a ∈
      (CliffordAlgebra.even (splitD4Form K)).toSubmodule
    rw [CliffordAlgebra.even_toSubmodule]
    exact
      (CliffordAlgebra.reverse_mem_evenOdd_iff
        (splitD4Form K)).2 ha⟩

omit [Invertible (2 : K)] in
/-- On positive Fock parity, the action of an even Clifford element is
adjoint to the action of its reversion. -/
theorem splitFockEvenAction_reverse_isAdjointPair
    (a : CliffordAlgebra (splitD4Form K))
    (ha : a ∈ CliffordAlgebra.evenOdd (splitD4Form K) 0) :
    (splitFockEvenNormPolar K).IsAdjointPair
      (splitFockEvenNormPolar K)
      (splitFockEvenAction K (evenCliffordElement K a ha))
      (splitFockEvenAction K (reverseEvenCliffordElement K a ha)) := by
  induction a, ha using
      CliffordAlgebra.even_induction (splitD4Form K) with
  | algebraMap r =>
      intro p q
      simp [evenCliffordElement, reverseEvenCliffordElement,
        CliffordAlgebra.reverse.commutes]
  | add x y hx hy ihx ihy =>
      intro p q
      have hxy : x + y ∈
          CliffordAlgebra.evenOdd (splitD4Form K) 0 :=
        (CliffordAlgebra.evenOdd (splitD4Form K) 0).add_mem hx hy
      have hleft :
          splitFockEvenAction K
              (evenCliffordElement K (x + y) hxy) p =
            splitFockEvenAction K (evenCliffordElement K x hx) p +
              splitFockEvenAction K (evenCliffordElement K y hy) p := by
        apply Subtype.ext
        change
          splitFockCliffordAction K (x + y) p =
            splitFockCliffordAction K x p +
              splitFockCliffordAction K y p
        rw [map_add, LinearMap.add_apply]
      have hright :
          splitFockEvenAction K
              (reverseEvenCliffordElement K (x + y) hxy) q =
            splitFockEvenAction K (reverseEvenCliffordElement K x hx) q +
              splitFockEvenAction K
                (reverseEvenCliffordElement K y hy) q := by
        apply Subtype.ext
        change
          splitFockCliffordAction K (CliffordAlgebra.reverse (x + y)) q =
            splitFockCliffordAction K (CliffordAlgebra.reverse x) q +
              splitFockCliffordAction K (CliffordAlgebra.reverse y) q
        rw [map_add, map_add, LinearMap.add_apply]
      rw [hleft, hright, map_add, map_add]
      exact congrArg₂ (· + ·) (ihx p q) (ihy p q)
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      intro p q
      have hmul :
          CliffordAlgebra.ι (splitD4Form K) m₁ *
              CliffordAlgebra.ι (splitD4Form K) m₂ * x ∈
            CliffordAlgebra.evenOdd (splitD4Form K) 0 := by
        have h₁₂ := splitClifford_mul_mem_evenOdd K
          (CliffordAlgebra.ι_mem_evenOdd_one
            (splitD4Form K) m₁)
          (CliffordAlgebra.ι_mem_evenOdd_one
            (splitD4Form K) m₂)
        have h := splitClifford_mul_mem_evenOdd K h₁₂ hx
        simpa only [show (1 : ZMod 2) + 1 = 0 by decide,
          zero_add] using h
      have hι₁ :
          splitFockCliffordAction K
              (CliffordAlgebra.ι (splitD4Form K) m₁) =
            exteriorFockGenerator m₁ :=
        exteriorCliffordAction_ι m₁
      have hι₂ :
          splitFockCliffordAction K
              (CliffordAlgebra.ι (splitD4Form K) m₂) =
            exteriorFockGenerator m₂ :=
        exteriorCliffordAction_ι m₂
      have hleft :
          splitFockEvenAction K
              (evenCliffordElement K
                (CliffordAlgebra.ι (splitD4Form K) m₁ *
                  CliffordAlgebra.ι (splitD4Form K) m₂ * x) hmul) p =
            splitFockGeneratorOddToEven K m₁
              (splitFockGeneratorEvenToOdd K m₂
                (splitFockEvenAction K
                  (evenCliffordElement K x hx) p)) := by
        apply Subtype.ext
        change
          splitFockCliffordAction K
              (CliffordAlgebra.ι (splitD4Form K) m₁ *
                CliffordAlgebra.ι (splitD4Form K) m₂ * x) p =
            exteriorFockGenerator m₁
              (exteriorFockGenerator m₂
                (splitFockCliffordAction K x p))
        rw [map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply, hι₁, hι₂]
      have hright :
          splitFockEvenAction K
              (reverseEvenCliffordElement K
                (CliffordAlgebra.ι (splitD4Form K) m₁ *
                  CliffordAlgebra.ι (splitD4Form K) m₂ * x) hmul) q =
            splitFockEvenAction K
                (reverseEvenCliffordElement K x hx)
              (splitFockGeneratorOddToEven K m₂
                (splitFockGeneratorEvenToOdd K m₁ q)) := by
        apply Subtype.ext
        change
          splitFockCliffordAction K
              (CliffordAlgebra.reverse
                (CliffordAlgebra.ι (splitD4Form K) m₁ *
                  CliffordAlgebra.ι (splitD4Form K) m₂ * x)) q =
            splitFockCliffordAction K (CliffordAlgebra.reverse x)
              (exteriorFockGenerator m₂
                (exteriorFockGenerator m₁ q))
        simp only [CliffordAlgebra.reverse.map_mul,
          CliffordAlgebra.reverse_ι, map_mul,
          Module.End.mul_apply, hι₁, hι₂]
      rw [hleft, hright]
      calc
        _ = splitFockOddNormPolar K
            (splitFockGeneratorEvenToOdd K m₂
              (splitFockEvenAction K
                (evenCliffordElement K x hx) p))
            (splitFockGeneratorEvenToOdd K m₁ q) := by
              calc
                _ = _ := splitFockEvenNormPolar_symm K _ _
                _ = _ := (splitFockGenerator_isAdjointPair K m₁ _ _).symm
                _ = _ := splitFockOddNormPolar_symm K _ _
        _ = splitFockEvenNormPolar K
            (splitFockEvenAction K
              (evenCliffordElement K x hx) p)
            (splitFockGeneratorOddToEven K m₂
              (splitFockGeneratorEvenToOdd K m₁ q)) :=
          splitFockGenerator_isAdjointPair K m₂ _ _
        _ = _ := ih _ _

omit [Invertible (2 : K)] in
/-- On negative Fock parity, the action of an even Clifford element is
adjoint to the action of its reversion. -/
theorem splitFockOddAction_reverse_isAdjointPair
    (a : CliffordAlgebra (splitD4Form K))
    (ha : a ∈ CliffordAlgebra.evenOdd (splitD4Form K) 0) :
    (splitFockOddNormPolar K).IsAdjointPair
      (splitFockOddNormPolar K)
      (splitFockOddAction K (evenCliffordElement K a ha))
      (splitFockOddAction K (reverseEvenCliffordElement K a ha)) := by
  induction a, ha using
      CliffordAlgebra.even_induction (splitD4Form K) with
  | algebraMap r =>
      intro p q
      simp [evenCliffordElement, reverseEvenCliffordElement,
        CliffordAlgebra.reverse.commutes]
  | add x y hx hy ihx ihy =>
      intro p q
      have hxy : x + y ∈
          CliffordAlgebra.evenOdd (splitD4Form K) 0 :=
        (CliffordAlgebra.evenOdd (splitD4Form K) 0).add_mem hx hy
      have hleft :
          splitFockOddAction K
              (evenCliffordElement K (x + y) hxy) p =
            splitFockOddAction K (evenCliffordElement K x hx) p +
              splitFockOddAction K (evenCliffordElement K y hy) p := by
        apply Subtype.ext
        change
          splitFockCliffordAction K (x + y) p =
            splitFockCliffordAction K x p +
              splitFockCliffordAction K y p
        rw [map_add, LinearMap.add_apply]
      have hright :
          splitFockOddAction K
              (reverseEvenCliffordElement K (x + y) hxy) q =
            splitFockOddAction K (reverseEvenCliffordElement K x hx) q +
              splitFockOddAction K
                (reverseEvenCliffordElement K y hy) q := by
        apply Subtype.ext
        change
          splitFockCliffordAction K (CliffordAlgebra.reverse (x + y)) q =
            splitFockCliffordAction K (CliffordAlgebra.reverse x) q +
              splitFockCliffordAction K (CliffordAlgebra.reverse y) q
        rw [map_add, map_add, LinearMap.add_apply]
      rw [hleft, hright, map_add, map_add]
      exact congrArg₂ (· + ·) (ihx p q) (ihy p q)
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      intro p q
      have hmul :
          CliffordAlgebra.ι (splitD4Form K) m₁ *
              CliffordAlgebra.ι (splitD4Form K) m₂ * x ∈
            CliffordAlgebra.evenOdd (splitD4Form K) 0 := by
        have h₁₂ := splitClifford_mul_mem_evenOdd K
          (CliffordAlgebra.ι_mem_evenOdd_one
            (splitD4Form K) m₁)
          (CliffordAlgebra.ι_mem_evenOdd_one
            (splitD4Form K) m₂)
        have h := splitClifford_mul_mem_evenOdd K h₁₂ hx
        simpa only [show (1 : ZMod 2) + 1 = 0 by decide,
          zero_add] using h
      have hι₁ :
          splitFockCliffordAction K
              (CliffordAlgebra.ι (splitD4Form K) m₁) =
            exteriorFockGenerator m₁ :=
        exteriorCliffordAction_ι m₁
      have hι₂ :
          splitFockCliffordAction K
              (CliffordAlgebra.ι (splitD4Form K) m₂) =
            exteriorFockGenerator m₂ :=
        exteriorCliffordAction_ι m₂
      have hleft :
          splitFockOddAction K
              (evenCliffordElement K
                (CliffordAlgebra.ι (splitD4Form K) m₁ *
                  CliffordAlgebra.ι (splitD4Form K) m₂ * x) hmul) p =
            splitFockGeneratorEvenToOdd K m₁
              (splitFockGeneratorOddToEven K m₂
                (splitFockOddAction K
                  (evenCliffordElement K x hx) p)) := by
        apply Subtype.ext
        change
          splitFockCliffordAction K
              (CliffordAlgebra.ι (splitD4Form K) m₁ *
                CliffordAlgebra.ι (splitD4Form K) m₂ * x) p =
            exteriorFockGenerator m₁
              (exteriorFockGenerator m₂
                (splitFockCliffordAction K x p))
        rw [map_mul, map_mul, Module.End.mul_apply,
          Module.End.mul_apply, hι₁, hι₂]
      have hright :
          splitFockOddAction K
              (reverseEvenCliffordElement K
                (CliffordAlgebra.ι (splitD4Form K) m₁ *
                  CliffordAlgebra.ι (splitD4Form K) m₂ * x) hmul) q =
            splitFockOddAction K
                (reverseEvenCliffordElement K x hx)
              (splitFockGeneratorEvenToOdd K m₂
                (splitFockGeneratorOddToEven K m₁ q)) := by
        apply Subtype.ext
        change
          splitFockCliffordAction K
              (CliffordAlgebra.reverse
                (CliffordAlgebra.ι (splitD4Form K) m₁ *
                  CliffordAlgebra.ι (splitD4Form K) m₂ * x)) q =
            splitFockCliffordAction K (CliffordAlgebra.reverse x)
              (exteriorFockGenerator m₂
                (exteriorFockGenerator m₁ q))
        simp only [CliffordAlgebra.reverse.map_mul,
          CliffordAlgebra.reverse_ι, map_mul,
          Module.End.mul_apply, hι₁, hι₂]
      rw [hleft, hright]
      calc
        _ = splitFockEvenNormPolar K
            (splitFockGeneratorOddToEven K m₂
              (splitFockOddAction K
                (evenCliffordElement K x hx) p))
            (splitFockGeneratorOddToEven K m₁ q) :=
          splitFockGenerator_isAdjointPair K m₁ _ _
        _ = splitFockOddNormPolar K
            (splitFockOddAction K
              (evenCliffordElement K x hx) p)
            (splitFockGeneratorEvenToOdd K m₂
              (splitFockGeneratorOddToEven K m₁ q)) := by
              calc
                _ = _ := splitFockEvenNormPolar_symm K _ _
                _ = _ := (splitFockGenerator_isAdjointPair K m₂ _ _).symm
                _ = _ := splitFockOddNormPolar_symm K _ _
        _ = _ := ih _ _

omit [Invertible (2 : K)] in
/-- A spin point satisfies the reversion norm-one equation. -/
theorem reverse_mul_self_spinPoint
    (g : SpinPoint (splitD4Form K)) :
    CliffordAlgebra.reverse
        (g : CliffordAlgebra (splitD4Form K)) * g = 1 := by
  have heven :
      (g : CliffordAlgebra (splitD4Form K)) ∈
        CliffordAlgebra.evenOdd (splitD4Form K) 0 :=
    spinGroup.mem_even g.property
  have hunitary := g.property.1.2.1
  rw [CliffordAlgebra.star_def,
    CliffordAlgebra.involute_eq_of_mem_even heven] at hunitary
  exact hunitary

omit [Invertible (2 : K)] in
private theorem splitFockEven_reverse_action_cancel
    (g : SpinPoint (splitD4Form K)) (p : SplitFockEven K) :
    splitFockEvenAction K
        (reverseEvenCliffordElement K g
          (spinGroup.mem_even g.property))
        (splitFockEvenAction K
          (evenCliffordElement K g
            (spinGroup.mem_even g.property)) p) = p := by
  have hmul :
      reverseEvenCliffordElement K g
          (spinGroup.mem_even g.property) *
        evenCliffordElement K g
          (spinGroup.mem_even g.property) = 1 := by
    apply Subtype.ext
    exact reverse_mul_self_spinPoint K g
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_one,
    Module.End.one_apply]

omit [Invertible (2 : K)] in
private theorem splitFockOdd_reverse_action_cancel
    (g : SpinPoint (splitD4Form K)) (p : SplitFockOdd K) :
    splitFockOddAction K
        (reverseEvenCliffordElement K g
          (spinGroup.mem_even g.property))
        (splitFockOddAction K
          (evenCliffordElement K g
            (spinGroup.mem_even g.property)) p) = p := by
  have hmul :
      reverseEvenCliffordElement K g
          (spinGroup.mem_even g.property) *
        evenCliffordElement K g
          (spinGroup.mem_even g.property) = 1 := by
    apply Subtype.ext
    exact reverse_mul_self_spinPoint K g
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_one,
    Module.End.one_apply]

omit [Invertible (2 : K)] in
/-- The positive half-spin representation preserves its transported Zorn
polar form in both arguments. -/
theorem splitEvenFockSpinRepresentation_preserves_normPolar
    (g : SpinPoint (splitD4Form K)) (p q : SplitFockEven K) :
    splitFockEvenNormPolar K
        (splitEvenFockSpinRepresentation K g p)
        (splitEvenFockSpinRepresentation K g q) =
      splitFockEvenNormPolar K p q := by
  have hadj :=
    splitFockEvenAction_reverse_isAdjointPair K g
      (spinGroup.mem_even g.property)
  change
    splitFockEvenNormPolar K
        (splitFockEvenAction K
          (evenCliffordElement K g
            (spinGroup.mem_even g.property)) p)
        (splitFockEvenAction K
          (evenCliffordElement K g
            (spinGroup.mem_even g.property)) q) =
      splitFockEvenNormPolar K p q
  calc
    _ = splitFockEvenNormPolar K p
        (splitFockEvenAction K
          (reverseEvenCliffordElement K g
            (spinGroup.mem_even g.property))
          (splitFockEvenAction K
            (evenCliffordElement K g
              (spinGroup.mem_even g.property)) q)) :=
      hadj _ _
    _ = _ := by rw [splitFockEven_reverse_action_cancel K]

omit [Invertible (2 : K)] in
/-- The negative half-spin representation preserves its transported Zorn
polar form in both arguments. -/
theorem splitOddFockSpinRepresentation_preserves_normPolar
    (g : SpinPoint (splitD4Form K)) (p q : SplitFockOdd K) :
    splitFockOddNormPolar K
        (splitOddFockSpinRepresentation K g p)
        (splitOddFockSpinRepresentation K g q) =
      splitFockOddNormPolar K p q := by
  have hadj :=
    splitFockOddAction_reverse_isAdjointPair K g
      (spinGroup.mem_even g.property)
  change
    splitFockOddNormPolar K
        (splitFockOddAction K
          (evenCliffordElement K g
            (spinGroup.mem_even g.property)) p)
        (splitFockOddAction K
          (evenCliffordElement K g
            (spinGroup.mem_even g.property)) q) =
      splitFockOddNormPolar K p q
  calc
    _ = splitFockOddNormPolar K p
        (splitFockOddAction K
          (reverseEvenCliffordElement K g
            (spinGroup.mem_even g.property))
          (splitFockOddAction K
            (evenCliffordElement K g
              (spinGroup.mem_even g.property)) q)) :=
      hadj _ _
    _ = _ := by rw [splitFockOdd_reverse_action_cancel K]

/-- The positive half-spin representation preserves the Zorn norm in the
chosen chart. -/
theorem splitEvenFockSpinRepresentation_preserves_zornNorm
    (g : SpinPoint (splitD4Form K)) (p : SplitFockEven K) :
    Zorn.normForm K
        (splitFockEvenZornEquiv K
          (splitEvenFockSpinRepresentation K g p)) =
      Zorn.normForm K (splitFockEvenZornEquiv K p) := by
  have h :=
    splitEvenFockSpinRepresentation_preserves_normPolar K g p p
  simp only [splitFockEvenNormPolar, LinearMap.BilinForm.comp_apply,
    Zorn.normPolarBilinear_self] at h
  exact mul_left_cancel₀
    (isUnit_iff_ne_zero.mp (isUnit_of_invertible (2 : K))) h

/-- The negative half-spin representation preserves the Zorn norm in the
chosen chart. -/
theorem splitOddFockSpinRepresentation_preserves_zornNorm
    (g : SpinPoint (splitD4Form K)) (p : SplitFockOdd K) :
    Zorn.normForm K
        (splitFockOddZornEquiv K
          (splitOddFockSpinRepresentation K g p)) =
      Zorn.normForm K (splitFockOddZornEquiv K p) := by
  have h :=
    splitOddFockSpinRepresentation_preserves_normPolar K g p p
  simp only [splitFockOddNormPolar, LinearMap.BilinForm.comp_apply,
    Zorn.normPolarBilinear_self] at h
  exact mul_left_cancel₀
    (isUnit_iff_ne_zero.mp (isUnit_of_invertible (2 : K))) h

/-- All three components of the explicit split Fock/Zorn chart preserve the
Zorn norm. This discharges the norm input of the concrete related-triples
comparison map. -/
theorem splitZornFockChart_preservesNorm :
    SplitZornTuplePreservesNorm K (splitZornFockChart K) := by
  intro g l x
  cases l with
  | vector =>
      exact splitZornFockChart_vector_preservesNorm K g x
  | halfSpinPlus =>
      simp only [splitTrialityLinearTupleHom, chartedRepresentation,
        representationLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk,
        LinearEquiv.trans_apply]
      change
        Zorn.normForm K
            (splitFockEvenZornEquiv K
              (splitEvenFockSpinRepresentation K g
                ((splitFockEvenZornEquiv K).symm x))) =
          Zorn.normForm K x
      rw [splitEvenFockSpinRepresentation_preserves_zornNorm K]
      simp
  | halfSpinMinus =>
      simp only [splitTrialityLinearTupleHom, chartedRepresentation,
        representationLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk,
        LinearEquiv.trans_apply]
      change
        Zorn.normForm K
            (splitFockOddZornEquiv K
              (splitOddFockSpinRepresentation K g
                ((splitFockOddZornEquiv K).symm x))) =
          Zorn.normForm K x
      rw [splitOddFockSpinRepresentation_preserves_zornNorm K]
      simp

/-- Clifford multiplication by a spin point commutes with the vector
generator after applying the vector representation. -/
theorem spin_mul_iota_commute
    (g : SpinPoint (splitD4Form K)) (x : SplitD4Space K) :
    (g : CliffordAlgebra (splitD4Form K)) *
        CliffordAlgebra.ι (splitD4Form K) x =
      CliffordAlgebra.ι (splitD4Form K)
          (spinVectorRepresentation (splitD4Form K) g x) * g := by
  rw [iota_spinVectorRepresentation_mul]
  simp only [mul_assoc]
  rw [show (spinGroup.toUnits g).inv *
      (g : CliffordAlgebra (splitD4Form K)) = 1 by
    simpa only [spinGroup.val_toUnits_apply] using
      (spinGroup.toUnits g).inv_val, mul_one]

/-- The full Fock action intertwines Clifford generators with the vector
representation of spin points. -/
theorem splitFockCliffordAction_generator_intertwines
    (g : SpinPoint (splitD4Form K)) (x : SplitD4Space K)
    (z : SplitFockSpace K) :
    splitFockCliffordAction K g
        (exteriorFockGenerator (K := K) (U := Fin 4 → K) x z) =
      exteriorFockGenerator (K := K) (U := Fin 4 → K)
        (spinVectorRepresentation (splitD4Form K) g x)
        (splitFockCliffordAction K g z) := by
  let ρ := splitFockCliffordAction K
  have hiota :
      ρ.toRingHom (CliffordAlgebra.ι (splitD4Form K) x) =
        exteriorFockGenerator (K := K) (U := Fin 4 → K) x := by
    exact exteriorCliffordAction_ι x
  have hiota' :
      ρ.toRingHom
          (CliffordAlgebra.ι (splitD4Form K)
            (spinVectorRepresentation (splitD4Form K) g x)) =
        exteriorFockGenerator (K := K) (U := Fin 4 → K)
          (spinVectorRepresentation (splitD4Form K) g x) := by
    exact exteriorCliffordAction_ι _
  have hmulL :=
    congrArg (fun f : Module.End K (SplitFockSpace K) => f z)
      (ρ.map_mul (g : CliffordAlgebra (splitD4Form K))
        (CliffordAlgebra.ι (splitD4Form K) x))
  have hmulR :=
    congrArg (fun f : Module.End K (SplitFockSpace K) => f z)
      (ρ.map_mul
        (CliffordAlgebra.ι (splitD4Form K)
          (spinVectorRepresentation (splitD4Form K) g x))
        (g : CliffordAlgebra (splitD4Form K)))
  have hleft :
      ρ g
          (exteriorFockGenerator (K := K) (U := Fin 4 → K) x z) =
        ρ ((g : CliffordAlgebra (splitD4Form K)) *
          CliffordAlgebra.ι (splitD4Form K) x) z := by
    calc
      _ = (ρ.toRingHom g *
          ρ.toRingHom (CliffordAlgebra.ι (splitD4Form K) x)) z := by
            rw [hiota]
            rfl
      _ = _ := hmulL.symm
  have hright :
      ρ (CliffordAlgebra.ι (splitD4Form K)
            (spinVectorRepresentation (splitD4Form K) g x) * g) z =
        exteriorFockGenerator (K := K) (U := Fin 4 → K)
          (spinVectorRepresentation (splitD4Form K) g x) (ρ g z) := by
    calc
      _ = (ρ.toRingHom
          (CliffordAlgebra.ι (splitD4Form K)
            (spinVectorRepresentation (splitD4Form K) g x)) *
          ρ.toRingHom g) z := hmulR
      _ = _ := by
        rw [hiota']
        rfl
  rw [hleft, spin_mul_iota_commute K, hright]

/-- The generator intertwining law restricted from positive to negative
Fock parity. -/
theorem splitFockGeneratorEvenToOdd_spin_intertwines
    (g : SpinPoint (splitD4Form K)) (x : SplitD4Space K)
    (p : SplitFockEven K) :
    splitOddFockSpinRepresentation K g
        (splitFockGeneratorEvenToOdd K x p) =
      splitFockGeneratorEvenToOdd K
        (spinVectorRepresentation (splitD4Form K) g x)
        (splitEvenFockSpinRepresentation K g p) := by
  apply Subtype.ext
  exact splitFockCliffordAction_generator_intertwines K g x p

/-- In Zorn coordinates, the generator intertwining law is para-product
equivariance. -/
theorem splitZornFockChart_paraMul_intertwines
    (g : SpinPoint (splitD4Form K)) (x : SplitD4Space K)
    (p : SplitFockEven K) :
    Zorn.paraMul K
        (splitVectorZornEquiv K
          (spinVectorRepresentation (splitD4Form K) g x))
        (splitFockEvenZornEquiv K
          (splitEvenFockSpinRepresentation K g p)) =
      splitFockOddZornEquiv K
        (splitOddFockSpinRepresentation K g
          (splitFockGeneratorEvenToOdd K x p)) := by
  rw [← splitFockGeneratorEvenToOdd_chart]
  exact congrArg (splitFockOddZornEquiv K)
    (splitFockGeneratorEvenToOdd_spin_intertwines K g x p).symm

/-- The three concrete vector and half-spin actions preserve the Zorn
triality tensor. -/
theorem splitZornFockChart_trialityTensor_preserved
    (g : SpinPoint (splitD4Form K))
    (w : SplitD4Space K) (p : SplitFockEven K)
    (m : SplitFockOdd K) :
    Zorn.trialityTensor K
        (splitVectorZornEquiv K
          (spinVectorRepresentation (splitD4Form K) g w))
        (splitFockEvenZornEquiv K
          (splitEvenFockSpinRepresentation K g p))
        (splitFockOddZornEquiv K
          (splitOddFockSpinRepresentation K g m)) =
      Zorn.trialityTensor K
        (splitVectorZornEquiv K w)
        (splitFockEvenZornEquiv K p)
        (splitFockOddZornEquiv K m) := by
  conv_lhs => rw [Zorn.trialityTensor_cycle_two K]
  conv_rhs => rw [Zorn.trialityTensor_cycle_two K]
  simp only [Zorn.trialityTensor]
  rw [splitZornFockChart_paraMul_intertwines K,
    ← splitFockGeneratorEvenToOdd_chart]
  simpa [splitFockOddNormPolar,
    LinearMap.BilinForm.comp_apply] using
    splitOddFockSpinRepresentation_preserves_normPolar K g m
      (splitFockGeneratorEvenToOdd K w p)

/-- The explicit split Fock/Zorn chart preserves the complete triality
tensor. This discharges the tensor input of the related-triples comparison. -/
theorem splitZornFockChart_preservesTensor :
    SplitZornTuplePreservesTensor K (splitZornFockChart K) := by
  intro g x
  simp only [Zorn.trialityEval]
  simp only [splitTrialityLinearTupleHom, chartedRepresentation,
    representationLinearEquiv, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearEquiv.trans_apply]
  change
    Zorn.trialityTensor K
        (splitVectorZornEquiv K
          (spinVectorRepresentation (splitD4Form K) g
            ((splitVectorZornEquiv K).symm (x .vector))))
        (splitFockEvenZornEquiv K
          (splitEvenFockSpinRepresentation K g
            ((splitFockEvenZornEquiv K).symm (x .halfSpinPlus))))
        (splitFockOddZornEquiv K
          (splitOddFockSpinRepresentation K g
            ((splitFockOddZornEquiv K).symm (x .halfSpinMinus)))) =
      Zorn.trialityTensor K (x .vector)
        (x .halfSpinPlus) (x .halfSpinMinus)
  rw [splitZornFockChart_trialityTensor_preserved K]
  simp

/-- The representation-defined homomorphism from split Clifford spin points
to Zorn related triples, with all chart compatibility obligations discharged. -/
noncomputable def splitFockSpinToZornRelatedTriples :
    SpinPoint (splitD4Form K) →* Zorn.relatedTripleGroup K :=
  splitSpinToZornRelatedTriples K (splitZornFockChart K)
    (splitZornFockChart_preservesNorm K)
    (splitZornFockChart_preservesTensor K)

/-- The concrete split Fock-to-Zorn homomorphism is faithful. -/
theorem splitFockSpinToZornRelatedTriples_injective :
    Function.Injective (splitFockSpinToZornRelatedTriples K) :=
  splitSpinToZornRelatedTriples_injective K
    (splitZornFockChart K)
    (splitZornFockChart_preservesNorm K)
    (splitZornFockChart_preservesTensor K)

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
