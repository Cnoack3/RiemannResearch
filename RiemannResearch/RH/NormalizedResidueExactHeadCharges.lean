/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Coefficients forced by exact heads of normalized residue sums

Source: user-provided squarefree CRT formulation, 13 October 2026.
The coefficient extraction uses the existing finite Mobius inversion theorem.
The results hold for arbitrary finite supports, hence also squarefree divisors.
They prove necessary coefficient and charge identities; they assert no uniform
energy estimate and no new RH converse.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem mobiusDifference_residueFraction (m d : ℕ) (hm : 1 < m) :
    mobiusDifference m (residueFraction d) = if m = d then -1 else 0 := by
  have hscale : mobiusDifference m (residueFraction d) =
      (d : ℝ)⁻¹ * mobiusDifference m (residue d) := by
    unfold mobiusDifference residueFraction residue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hscale, mobiusDifference_residue m d hm]
  by_cases hmd : m = d
  · subst d
    have hmR : (m : ℝ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by omega)
    simp [hmR]
  · simp [hmd]

theorem residueFraction_sum_mobiusDifference (s : Finset ℕ) (c : ℕ → ℝ)
    (m : ℕ) (hm : 1 < m) :
    mobiusDifference m (fun k => ∑ d ∈ s, c d * residueFraction d k) =
      -(if m ∈ s then c m else 0) := by
  rw [mobiusDifference_sum]
  simp_rw [mobiusDifference_residueFraction m _ hm]
  have hterm (d : ℕ) : c d * (if m = d then (-1 : ℝ) else 0) =
      (if d = m then -c m else 0) := by
    by_cases hd : d = m
    · subst d
      simp
    · simp [hd, Ne.symm hd]
  simp_rw [hterm]
  by_cases hmS : m ∈ s <;> simp [hmS]

theorem residueFraction_exact_head_coefficients (s : Finset ℕ) (c : ℕ → ℝ)
    (N : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ N →
      (∑ d ∈ s, c d * residueFraction d k) = 1)
    (m : ℕ) (hm : 1 < m) (hmN : m ≤ N) :
    (if m ∈ s then c m else 0) = -(ArithmeticFunction.moebius m : ℝ) := by
  have hz : (∑ d ∈ s, c d * residueFraction d 0) = 0 := by
    simp [residueFraction]
  have he := exact_head_mobiusDifference hz hhead (by omega : 0 < m) hmN
  rw [residueFraction_sum_mobiusDifference s c m hm] at he
  linarith

theorem residueFraction_exact_head_charge (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 1 < d) (N : ℕ) (hN : 0 < N)
    (hhead : ∀ k, 0 < k → k ≤ N →
      (∑ d ∈ s, c d * residueFraction d k) = 1) :
    (∑ d ∈ s, c d / (d : ℝ)) = 1 := by
  calc
    (∑ d ∈ s, c d / (d : ℝ)) =
        ∑ d ∈ s, c d * residueFraction d 1 := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [residueFraction, Nat.mod_eq_of_lt (hs d hd), div_eq_mul_inv]
    _ = 1 := hhead 1 (by omega) hN

end RiemannResearch.RH.Pareto
