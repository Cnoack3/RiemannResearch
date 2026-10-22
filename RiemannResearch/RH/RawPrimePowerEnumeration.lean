import RiemannResearch.RH.RawPrimePowerContinuationTargets
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# A complete actual prime-power enumeration

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

API source is pinned to Mathlib commit
51e6992efd06126df61a496bebf8f49482a4e129.

This constructs the increasing enumeration of all natural prime powers
using Nat.nth. Infinitude follows from the already formalized infinitude
of primes. Its support completeness is for the actual von Mangoldt
function, and it closes the exact raw cell assembly including [1,2].
No RH, prime-gap, or arithmetic energy estimate is assumed or asserted.
-/

set_option autoImplicit false
noncomputable section

namespace RiemannResearch.RH.RawPrimePowerEnumeration

open RawPrimePowerContinuation

theorem primePowerSet_infinite :
    (Set.ofPred (IsPrimePow : ℕ → Prop)).Infinite :=
  Nat.infinite_setOfPred_prime.mono (fun _ hn => hn.isPrimePow)

def actualPrimePowerSequence : ℕ → ℕ := Nat.nth (IsPrimePow : ℕ → Prop)

theorem actualPrimePowerSequence_strictMono : StrictMono actualPrimePowerSequence :=
  Nat.nth_strictMono primePowerSet_infinite

theorem actualPrimePowerSequence_mem (i : ℕ) : IsPrimePow (actualPrimePowerSequence i) :=
  Nat.nth_mem_of_infinite primePowerSet_infinite i

theorem actualPrimePowerSequence_first : actualPrimePowerSequence 0 = 2 := by
  have hle : actualPrimePowerSequence 0 ≤ 2 := by
    unfold actualPrimePowerSequence
    rw [Nat.nth_zero]
    exact Nat.sInf_le Nat.prime_two.isPrimePow
  exact le_antisymm hle (actualPrimePowerSequence_mem 0).two_le

/-- Every actual nonzero von Mangoldt coefficient through the N-th cutoff
occurs in the enumeration prefix, with its actual natural-number value. -/
theorem actualPrimePowerSequence_complete (N : ℕ) :
    PrimePowerCriticalEnergy.CompleteThrough actualPrimePowerSequence N := by
  intro k hk hne
  have hp : IsPrimePow k := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne
  have hrange : k ∈ Set.range actualPrimePowerSequence := by
    change k ∈ Set.range (Nat.nth (IsPrimePow : ℕ → Prop))
    rw [Nat.range_nth_of_infinite primePowerSet_infinite]
    exact hp
  obtain ⟨j, he⟩ := hrange
  have hkn : k ≤ actualPrimePowerSequence N :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hjN : j ≤ N := by
    apply actualPrimePowerSequence_strictMono.le_iff_le.mp
    rw [he]
    exact hkn
  exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjN), he⟩

/-- Explicit complete enumeration data, with no remaining construction provider. -/
def actualEnumeration : ActualPrimePowerEnumeration where
  q := actualPrimePowerSequence
  strictMono := actualPrimePowerSequence_strictMono
  first := actualPrimePowerSequence_first
  positive i := (actualPrimePowerSequence_mem i).pos
  primePower := actualPrimePowerSequence_mem
  complete := actualPrimePowerSequence_complete

theorem actualPrimePowerEnumeration_exists : Nonempty ActualPrimePowerEnumeration :=
  ⟨actualEnumeration⟩

/-- The exact actual raw cell assembly is specialized to the constructed
complete enumeration. Only the genuine quantitative energy targets remain. -/
theorem actualRawCellAssembly_actualEnumeration : ActualRawCellAssembly actualEnumeration :=
  actualRawCellAssembly_proved actualEnumeration

end RiemannResearch.RH.RawPrimePowerEnumeration
