/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.CliffordAlgebra.EvenFunctoriality
import RiemannResearch.LinearAlgebra.RootSystem.D4Triality

/-!
# Pointwise Spin data for D4 triality

This file is the first algebraic layer above the combinatorial D4 diagram. It
records the usual eight-dimensional regularity condition on a quadratic form
and gives a precise interface for a supplied faithful action of the six
diagram symmetries on Mathlib's pointwise spin group.

The action in `SpinPointTrialityData` is data, not a theorem constructed here.
In particular this module does not construct a split Spin(8) group scheme,
the vector or half-spin representations, an outer action compatible with root
data, or Galois/fpqc descent. Its purpose is to name that missing bridge without
conflating it with the concrete Clifford-even results in
`CliffordAlgebra.EvenFunctoriality`.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open RiemannResearch.LinearAlgebra

universe uK uM

/-- A finite-dimensional quadratic form of dimension eight with nondegenerate
associated bilinear form. -/
def IsRegularEightDimensional
    {K : Type uK} [Field K] {M : Type uM}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [Invertible (2 : K)] (Q : QuadraticForm K M) : Prop :=
  Module.finrank K M = 8 ∧
    (QuadraticMap.associated Q).Nondegenerate

/-- Supplied pointwise triality data for one regular eight-dimensional
quadratic form.

`action` is only an action on Mathlib's group of spin points. The `faithful`
field prevents a merely trivial S3 action from being presented as triality,
but no root-datum or representation-theoretic compatibility is claimed. -/
structure SpinPointTrialityData
    {K : Type uK} [Field K] {M : Type uM}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [Invertible (2 : K)] (Q : QuadraticForm K M) where
  regularEightDimensional : IsRegularEightDimensional Q
  action : DiagramSymmetry →* MulAut (CliffordEven.SpinPoint Q)
  faithful : Function.Injective action

namespace SpinPointTrialityData

/-- A supplied faithful pointwise triality action sends the canonical
three-cycle to an automorphism of exact order three. -/
theorem orderOf_trialityCycle_action
    {K : Type uK} [Field K] {M : Type uM}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [Invertible (2 : K)] {Q : QuadraticForm K M}
    (D : SpinPointTrialityData Q) :
    orderOf (D.action trialityCycle) = 3 := by
  rw [orderOf_injective D.action D.faithful]
  exact orderOf_trialityCycle

/-- A supplied faithful pointwise triality action sends the half-spin swap to
an automorphism of exact order two. -/
theorem orderOf_halfSpinSwap_action
    {K : Type uK} [Field K] {M : Type uM}
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [Invertible (2 : K)] {Q : QuadraticForm K M}
    (D : SpinPointTrialityData Q) :
    orderOf (D.action halfSpinSwap) = 2 := by
  rw [orderOf_injective D.action D.faithful]
  exact orderOf_halfSpinSwap

end SpinPointTrialityData

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
