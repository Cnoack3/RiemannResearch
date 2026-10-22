/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimePowerTargetMellin
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QPrimePowerPrimorial
import RiemannResearch.RH.QSquarefreePeriodicJump

/-!
# The actual logarithmic target obeys the squarefree jump constraints

Source: `PrimePowerTargetsResearch20261020.md`, Section 1. The proof uses
the already established pointwise limit of the legal gcd-two sieve.
It uses only finite-coordinate limits, without inferring norm convergence
or squarefree closure from those limits.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QPrimePowerSieve SquarefreeRadicalDifference
open QSquarefreePeriodicJump

theorem primePowerTwoVector_difference_tendsto (m : ℕ) :
    Tendsto (fun H => qDifference (primePowerTwoVector H) m) atTop
      (𝓝 (qDifference (qTarget 2 (by norm_num)) m)) := by
  simpa only [qDifference, qTarget_sequence] using
    (primePowerTwoVector_pointwise m).sub (primePowerTwoVector_pointwise (m - 1))

/-- The actual complete-Q logarithmic target satisfies all the finite
squarefree-divisor jump relations. This is not a closure-membership theorem. -/
theorem qTarget_two_difference_eq_of_same_divisors
    (m a : ℕ) (hm : 1 ≤ m) (ha : 1 ≤ a)
    (hdiv : ∀ d : ℕ, Squarefree d → 2 ≤ d → (d ∣ m ↔ d ∣ a)) :
    qDifference (qTarget 2 (by norm_num)) m =
      qDifference (qTarget 2 (by norm_num)) a := by
  apply tendsto_nhds_unique (primePowerTwoVector_difference_tendsto m)
  have ht := primePowerTwoVector_difference_tendsto a
  apply ht.congr
  intro H
  exact (squarefree_span_difference_eq_of_same_divisors m a hm ha hdiv
    (primePowerTwoVector H) (primePowerTwoVector_mem_squarefreeSpan H)).symm

theorem qTarget_two_difference_pow (a k : ℕ) (ha : 1 ≤ a) (hk : k ≠ 0) :
    qDifference (qTarget 2 (by norm_num)) (a ^ k) =
      qDifference (qTarget 2 (by norm_num)) a := by
  apply qTarget_two_difference_eq_of_same_divisors (a ^ k) a
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega))) ha
  intro d hd _
  exact hd.dvd_pow_iff_dvd hk

end RiemannResearch.RH.PrimePowerTarget
