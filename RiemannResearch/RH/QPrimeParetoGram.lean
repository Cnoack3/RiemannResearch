/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFinitePrimeBasis
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.Linarith

/-!
# Actual Pareto Gram bounds from independent prime coordinates

Source: user-directed prime-factor independence argument, 21 October 2026.
The existing actual Q product law supplies orthonormal prime modes. The
complete change-of-measure correction is retained before taking bounds.
The auxiliary Gram forms lie between zetaTwo/2 and zetaTwo times the identity.
No such bound for the Ramanujan packet Gram, no completeness of Boolean
prime modes, and no squarefree capacity saturation is asserted.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace RiemannResearch.RH.QPrimeParetoGram
open QFinitePrimeBasis ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer Pareto
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeVector (p : ι → ℕ) (A : Finset ι) : ThresholdHilbert :=
  toPareto (primeUnitVector p A)

theorem prime_synthesis_norm_sq_exact (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset ι)) (c : Finset ι → ℝ) :
    ‖∑ A ∈ S, c A • primeVector p A‖ ^ 2 =
      zetaTwo * (∑ A ∈ S, c A ^ 2) -
        zetaTwo * normCorrection (∑ A ∈ S, c A • primeUnitVector p A) := by
  have hn : ‖∑ A ∈ S, c A • primeUnitVector p A‖ ^ 2 = ∑ A ∈ S, c A ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      (primeUnitVector_orthonormal p hp hinj).inner_sum c c S]
    simp [pow_two]
  have ht : toPareto (∑ A ∈ S, c A • primeUnitVector p A) =
      ∑ A ∈ S, c A • primeVector p A := by
    change toParetoLinear (∑ A ∈ S, c A • primeUnitVector p A) = _
    simp only [map_sum, map_smul]
    rfl
  rw [← ht, toPareto_norm_sq_exact, hn]

theorem prime_synthesis_norm_sq_bounds (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset ι)) (c : Finset ι → ℝ) :
    (zetaTwo / 2) * (∑ A ∈ S, c A ^ 2) ≤
      ‖∑ A ∈ S, c A • primeVector p A‖ ^ 2 ∧
    ‖∑ A ∈ S, c A • primeVector p A‖ ^ 2 ≤
      zetaTwo * (∑ A ∈ S, c A ^ 2) := by
  let f : QHilbert := ∑ A ∈ S, c A • primeUnitVector p A
  have hn : ‖f‖ ^ 2 = ∑ A ∈ S, c A ^ 2 := by
    dsimp only [f]
    rw [← real_inner_self_eq_norm_sq,
      (primeUnitVector_orthonormal p hp hinj).inner_sum c c S]
    simp [pow_two]
  have ht : toPareto f = ∑ A ∈ S, c A • primeVector p A := by
    change toParetoLinear (∑ A ∈ S, c A • primeUnitVector p A) = _
    simp only [map_sum, map_smul]
    rfl
  have hl := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq f
  have hu := toPareto_norm_sq_le f
  rw [hn, ht] at hl hu
  constructor
  · linarith
  · exact hu

theorem prime_projection_full_energy_exact (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (f : QHilbert) (S : Finset (Finset ι)) :
    ‖toPareto f‖ ^ 2 =
      zetaTwo * ((∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) ^ 2) +
        ‖f - ∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) • primeUnitVector p A‖ ^ 2) -
          zetaTwo * normCorrection f := by
  rw [toPareto_norm_sq_exact, primeUnitVector_energy_exact p hp hinj f S]

theorem prime_projection_full_energy_bounds (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (f : QHilbert) (S : Finset (Finset ι)) :
    (zetaTwo / 2) * ((∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) ^ 2) +
      ‖f - ∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) • primeUnitVector p A‖ ^ 2)
        ≤ ‖toPareto f‖ ^ 2 ∧
    ‖toPareto f‖ ^ 2 ≤ zetaTwo *
      ((∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) ^ 2) +
      ‖f - ∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) • primeUnitVector p A‖ ^ 2) := by
  rw [← primeUnitVector_energy_exact p hp hinj f S]
  constructor
  · have h := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq f
    linarith
  · exact toPareto_norm_sq_le f
end RiemannResearch.RH.QPrimeParetoGram
