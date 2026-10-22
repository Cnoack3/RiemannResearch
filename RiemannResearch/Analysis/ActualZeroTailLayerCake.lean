/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteStrictTail
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Actual-zero strict tails and exact finite layer cake

Every finite sum uses actual zeta zeros and their analytic multiplicities.
The bad mask is the strict complement of the good mask `|β - 1/2| ≤ δ`.
Actual strip geometry supplies the finite upper endpoint `1/2`.
Normalization always uses the original `Ncount 0 T`, including empty cutoffs.
No zero-density estimate or decay with height is asserted here.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23

def copyDisplacement (T : ℝ) (c : Copies T) : ℝ := |c.1.1.re - 1 / 2|

def strictTail (T t : ℝ) : ℝ :=
  FiniteStrictTail.tail (Finset.univ : Finset (Copies T)) (copyDisplacement T) t

def badWeightedSum (T δ : ℝ) (φ : ℝ → ℝ) : ℝ :=
  FiniteStrictTail.badSum (Finset.univ : Finset (Copies T))
    (copyDisplacement T) φ δ

theorem strictTail_eq_realSum (T t : ℝ) :
    strictTail T t = realSum T (fun ρ => if t < |ρ.re - 1 / 2| then 1 else 0) := by
  rw [realSum_eq_copies]
  rfl

theorem badWeightedSum_eq_realSum (T δ : ℝ) (φ : ℝ → ℝ) :
    badWeightedSum T δ φ = realSum T
      (fun ρ => if δ < |ρ.re - 1 / 2| then φ |ρ.re - 1 / 2| else 0) := by
  rw [realSum_eq_copies]
  rfl

theorem strictTail_nonneg (T t : ℝ) : 0 ≤ strictTail T t :=
  FiniteStrictTail.tail_nonneg _ _ _

theorem strictTail_le_count (T t : ℝ) : strictTail T t ≤ (Ncount 0 T : ℝ) := by
  simpa only [strictTail, Finset.card_univ, card_copies] using
    FiniteStrictTail.tail_le_card (Finset.univ : Finset (Copies T))
      (copyDisplacement T) t

theorem strictTail_half (T : ℝ) : strictTail T (1 / 2) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c hc
  have h := displacement_lt_half c.1.2
  exact if_neg (not_lt.mpr h.le)

theorem badWeightedSum_eq_zero_of_half_le (T δ : ℝ) (φ : ℝ → ℝ)
    (hδ : 1 / 2 ≤ δ) : badWeightedSum T δ φ = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c hc
  have h := displacement_lt_half c.1.2
  exact if_neg (not_lt.mpr (h.le.trans hδ))

/-- Actual finite-strip geometry discharges the entire finite support premise.
No assumption about how many copies lie away from the critical line is used. -/
theorem badWeightedSum_layerCake (T δ : ℝ) (φ f : ℝ → ℝ)
    (hδ : δ ≤ 1 / 2) (hf : Continuous f)
    (hderiv : ∀ t, HasDerivAt φ (f t) t) :
    badWeightedSum T δ φ = φ δ * strictTail T δ +
      ∫ t in δ..(1 / 2), strictTail T t * f t := by
  apply FiniteStrictTail.layerCake _ _ _ _ hf hderiv δ (1 / 2) hδ
  intro c hc
  exact (displacement_lt_half c.1.2).le

theorem badExp_layerCake (T δ ell : ℝ) (hδ : δ ≤ 1 / 2) :
    badWeightedSum T δ (fun t => Real.exp (ell * t)) =
      Real.exp (ell * δ) * strictTail T δ +
        ∫ t in δ..(1 / 2), strictTail T t * (ell * Real.exp (ell * t)) := by
  apply badWeightedSum_layerCake T δ _ _ hδ
  · fun_prop
  · intro t
    simpa only [Function.comp_def, mul_one, mul_comm] using
      (Real.hasDerivAt_exp (ell * t)).comp t
        ((hasDerivAt_id t).const_mul ell)

theorem badCosh_layerCake (T δ ell : ℝ) (hδ : δ ≤ 1 / 2) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) =
      (Real.cosh (ell * δ) - 1) * strictTail T δ +
        ∫ t in δ..(1 / 2), strictTail T t * (ell * Real.sinh (ell * t)) := by
  apply badWeightedSum_layerCake T δ _ _ hδ
  · fun_prop
  · intro t
    simpa only [Function.comp_def, mul_one, mul_comm] using
      ((Real.hasDerivAt_cosh (ell * t)).comp t
        ((hasDerivAt_id t).const_mul ell)).sub_const 1

/-- The unconditional finite-strip estimate. It supplies no decay with T. -/
theorem badCoshSum_le_count (T δ ell : ℝ) (hell : 0 ≤ ell) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) ≤
      (Ncount 0 T : ℝ) * (Real.cosh (ell / 2) - 1) := by
  classical
  unfold badWeightedSum FiniteStrictTail.badSum
  calc
    _ ≤ ∑ _c : Copies T, (Real.cosh (ell / 2) - 1) := by
      apply Finset.sum_le_sum
      intro c hc
      split_ifs with hbad
      · apply sub_le_sub_right
        apply Real.cosh_le_cosh.mpr
        have hx0 : 0 ≤ copyDisplacement T c := abs_nonneg _
        have hx : copyDisplacement T c ≤ 1 / 2 :=
          (displacement_lt_half c.1.2).le
        rw [abs_of_nonneg (mul_nonneg hell hx0),
          abs_of_nonneg (div_nonneg hell (by norm_num))]
        nlinarith [mul_le_mul_of_nonneg_left hx hell]
      · exact sub_nonneg.mpr (Real.one_le_cosh _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_copies]

/-- Original-count normalization remains valid even at an empty cutoff. -/
theorem normalized_badCoshSum_le (T δ ell : ℝ) (hell : 0 ≤ ell) :
    badWeightedSum T δ (fun t => Real.cosh (ell * t) - 1) / (Ncount 0 T : ℝ) ≤
      Real.cosh (ell / 2) - 1 := by
  by_cases hN : (Ncount 0 T : ℝ) = 0
  · rw [hN, div_zero]
    exact sub_nonneg.mpr (Real.one_le_cosh _)
  · have hN0 : 0 < (Ncount 0 T : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hN)
    apply (div_le_iff₀ hN0).mpr
    simpa only [mul_comm] using badCoshSum_le_count T δ ell hell

end RiemannResearch.Analysis.ActualZeroOrdinate
