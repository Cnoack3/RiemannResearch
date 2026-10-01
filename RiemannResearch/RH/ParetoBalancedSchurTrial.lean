/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoFirstSitePrimeBudget

/-!
# Actual Schur gains tested against a balanced old row

Source: full finite inverse-Gram norm completion and reciprocal observations.
This is an exact signed finite lower certificate, preserving its projection
remainder. The doubling bucket is a concrete paper application of this test;
nonsummability of its actual pairings remains open.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram

theorem schurBalancedTrial_norm_sq_completion (n : ℕ) (i : Fin n) (a : ℝ) :
    ‖tailAtom n - a • tailAtom i.val‖ ^ 2 = schurSigma n +
      ‖Fintype.linearCombination ℝ (fun j : Fin n => tailAtom j.val)
        (fun j => (if j = i then a else 0) -
          inverseCoeff (finiteTailAtom_independent n) (tailAtom n) j)‖ ^ 2 := by
  classical
  let c : Fin n → ℝ := fun j => if j = i then a else 0
  have hs : Fintype.linearCombination ℝ (fun j : Fin n => tailAtom j.val) c =
      a • tailAtom i.val := by
    change (∑ j : Fin n, c j • tailAtom j.val) = _
    rw [Finset.sum_eq_single i]
    · simp [c]
    · intro j _ hji
      simp [c, hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have he := residual_completion (finiteTailAtom_independent n) (tailAtom n) c
  rw [hs] at he
  exact he

theorem schurSigma_le_balancedTrial_norm_sq (n : ℕ) (i : Fin n) (a : ℝ) :
    schurSigma n ≤ ‖tailAtom n - a • tailAtom i.val‖ ^ 2 := by
  rw [schurBalancedTrial_norm_sq_completion]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The reciprocal target cancels as an exact signed identity. -/
theorem schurEta_eq_neg_balancedTrial (n : ℕ) (i : Fin n) (a : ℝ)
    (ha : a * (1 / ((i.val + 2 : ℕ) : ℝ)) = 1 / ((n + 2 : ℕ) : ℝ)) :
    schurEta n = -inner ℝ (tailAtom n - a • tailAtom i.val) (tailMinimum n) := by
  have ho := tailMinimum_observation n i
  simp only [reciprocalSource] at ho
  rw [inner_sub_left, real_inner_smul_left, ho, ha]
  unfold schurEta
  ring

theorem schurGain_ge_balancedTrial (n : ℕ) (i : Fin n) (a K : ℝ)
    (hK : 0 < K)
    (ha : a * (1 / ((i.val + 2 : ℕ) : ℝ)) = 1 / ((n + 2 : ℕ) : ℝ))
    (htrial : ‖tailAtom n - a • tailAtom i.val‖ ^ 2 ≤ K) :
    (inner ℝ (tailAtom n - a • tailAtom i.val) (tailMinimum n)) ^ 2 / K ≤
      (schurEta n) ^ 2 / schurSigma n := by
  have hs := (schurSigma_le_balancedTrial_norm_sq n i a).trans htrial
  rw [schurEta_eq_neg_balancedTrial n i a ha, neg_sq]
  apply (div_le_div_iff₀ hK (schurSigma_pos n)).mpr
  exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)

theorem factorialCompositeGain_ge_balancedTrial
    (n : ℕ) (hp : ¬ Nat.Prime (n + 3)) (i : Fin (n + 1)) (a K : ℝ)
    (hK : 0 < K)
    (ha : a * (1 / ((i.val + 2 : ℕ) : ℝ)) = 1 / ((n + 3 : ℕ) : ℝ))
    (htrial : ‖tailAtom (n + 1) - a • tailAtom i.val‖ ^ 2 ≤ K) :
    (inner ℝ (tailAtom (n + 1) - a • tailAtom i.val) (tailMinimum (n + 1))) ^ 2 / K ≤
      factorialCompositeGain n := by
  rw [factorialCompositeGain, if_neg hp]
  apply schurGain_ge_balancedTrial (n + 1) i a K hK
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using ha
  · exact htrial

end RiemannResearch.RH.Pareto.IntegerDPP
