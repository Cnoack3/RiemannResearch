/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Bases adapted to a regular functional

This module records the correct root-system replacement for the sign-only
normalization used in Theorem 3.2 of the 5 August 2026 E8 manuscript. A
regular functional need not become positive on a fixed base after multiplication
by `-1`. Instead, the root system admits a base adapted to the functional.
-/

namespace RiemannResearch.LinearAlgebra

/-- A rational-valued functional which is nonzero on every root determines a
base on whose simple roots it is strictly positive. This is the chamber-change
needed for the attracting-rank argument; merely replacing the functional by its
negative is insufficient in rank greater than one. -/
theorem regularFunctional_exists_adaptedBase
    {ι K M N : Type*}
    [Finite ι] [Field K] [CharZero K]
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    (P : RootPairing ι K M N)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (f : M →+ ℚ) (hf : ∀ i, f (P.root i) ≠ 0) :
    ∃ b : P.Base, ∀ i ∈ b.support, 0 < f (P.root i) := by
  let _ := P.indexNeg
  let s : Set ι := IsAddIndecomposable.baseOf (⇑P.root) f
  have hli : LinearIndepOn K (⇑P.root) s :=
    P.linearIndepOn_root_baseOf f hf
  have hspan :
      ∀ i, P.root i ∈ AddSubmonoid.closure (⇑P.root '' s) ∨
        -P.root i ∈ AddSubmonoid.closure (⇑P.root '' s) := by
    intro i
    apply IsAddIndecomposable.mem_or_neg_mem_closure_baseOf
    · exact hf i
    · exact (P.root_eq_neg_iff).2 (P.indexNeg_neg i)
  let b : P.Base := RootPairing.Base.mk' P s hli hspan
  refine ⟨b, ?_⟩
  intro i hi
  apply IsAddIndecomposable.baseOf_subset_pos (⇑P.root) f
  simpa [b, RootPairing.Base.mk', s] using hi

end RiemannResearch.LinearAlgebra
