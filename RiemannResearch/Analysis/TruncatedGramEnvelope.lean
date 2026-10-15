/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteGramAffineMinimum
import RiemannResearch.Analysis.FiniteGramRange
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite Gram energies with an explicit diagonal tail allowance

Source: user-requested inverse-Gram research, with an independently derived
finite truncation argument. The RH consumer is CanonicalMobiusTruncatedCeiling.
The augmented finite Hilbert family constructs an actual normal solution and
positive affine ceiling. Exact radius changes retain every signed mixed term.
No uniform estimate over moving families is assumed or established.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.TruncatedGramEnvelope
open RiemannResearch.Analysis.FiniteHilbertGram
variable {ι : Type*} [Fintype ι]

def energy (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (a : ι → ℝ) : ℝ :=
  (∑ n ∈ Finset.range R, w n * (∑ i, a i * v i n) ^ 2) + κ * ∑ i, a i ^ 2

theorem energy_succ_sub (w : ℕ → ℝ) (v : ι → ℕ → ℝ)
    (κ κ' : ℝ) (R : ℕ) (a : ι → ℝ) :
    energy w v κ' (R+1) a - energy w v κ R a =
      w R * (∑ i, a i * v i R) ^ 2 + (κ' - κ) * ∑ i, a i ^ 2 := by
  simp only [energy, Finset.sum_range_succ]
  ring

theorem combination_sq_le (v : ι → ℕ → ℝ) (B a : ι → ℝ) (n : ℕ)
    (hB : ∀ i, |v i n| ≤ B i) :
    (∑ i, a i * v i n) ^ 2 ≤ (∑ i, B i ^ 2) * ∑ i, a i ^ 2 := by
  calc
    _ ≤ (∑ i, a i ^ 2) * ∑ i, v i n^2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, a i ^ 2) * ∑ i, B i ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      simpa only [← pow_two, sq_abs] using mul_self_le_mul_self (abs_nonneg _) (hB i)
    _ = _ := mul_comm _ _

def feature (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (i : ι) : EuclideanSpace ℝ (Fin R ⊕ ι) := by
  classical
  exact WithLp.toLp 2 (fun j => match j with
    | Sum.inl n => Real.sqrt (w n) * v i n
    | Sum.inr k => if i = k then Real.sqrt κ else 0)

theorem feature_synthesis_left (w : ℕ → ℝ) (v : ι → ℕ → ℝ)
    (κ : ℝ) (R : ℕ) (a : ι → ℝ) (n : Fin R) :
    (Fintype.linearCombination ℝ (feature w v κ R) a) (Sum.inl n) =
      Real.sqrt (w n) * ∑ i, a i * v i n := by
  simp only [Fintype.linearCombination_apply]
  simp [feature, Finset.mul_sum, mul_left_comm]

theorem feature_synthesis_right (w : ℕ → ℝ) (v : ι → ℕ → ℝ)
    (κ : ℝ) (R : ℕ) (a : ι → ℝ) (j : ι) :
    (Fintype.linearCombination ℝ (feature w v κ R) a) (Sum.inr j) =
      Real.sqrt κ * a j := by
  classical
  simp [Fintype.linearCombination_apply, feature, mul_comm]

theorem feature_synthesis_energy (w : ℕ → ℝ) (v : ι → ℕ → ℝ)
    (κ : ℝ) (R : ℕ) (a : ι → ℝ) (hw : ∀ n, 0 ≤ w n) (hκ : 0 ≤ κ) :
    ‖Fintype.linearCombination ℝ (feature w v κ R) a‖ ^ 2 = energy w v κ R a := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, Fintype.sum_sum_type]
  simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial]
  simp_rw [feature_synthesis_left, feature_synthesis_right]
  simp_rw [← pow_two, mul_pow, Real.sq_sqrt (hw _), Real.sq_sqrt hκ]
  rw [← Finset.mul_sum]
  simp only [energy]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => w n * (∑ i, a i * v i n) ^ 2) R

theorem normal_exists (w : ℕ → ℝ) (v : ι → ℕ → ℝ)
    (κ : ℝ) (R : ℕ) (hκ : 0 < κ) :
    ∃ z : ι → ℝ, gram (feature w v κ R) z = fun _ => 1 := by
  apply exists_gram_eq_one_of_synthesis_null_sum_zero
  intro a ha
  have hz : ∀ i, a i = 0 := by
    intro i
    have he := congrArg (fun f : EuclideanSpace ℝ (Fin R ⊕ ι) => f (Sum.inr i)) ha
    rw [feature_synthesis_right] at he
    have hs : Real.sqrt κ ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hκ)
    simpa [hs] using he
  simp [hz]

theorem energy_succ_le (w : ℕ → ℝ) (v : ι → ℕ → ℝ)
    (B : ι → ℝ) (κ κ' : ℝ) (R : ℕ) (a : ι → ℝ)
    (hw : 0 ≤ w R) (hB : ∀ i, |v i R| ≤ B i)
    (hκ : κ' - κ ≤ -w R * ∑ i, B i ^ 2) :
    energy w v κ' (R+1) a ≤ energy w v κ R a := by
  have hc := combination_sq_le v B a R hB
  have hs : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hc hw
  have h2 := mul_le_mul_of_nonneg_right hκ hs
  have he := energy_succ_sub w v κ κ' R a
  nlinarith

def normal (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) : ι → ℝ := Classical.choose (normal_exists w v κ R hκ)

theorem normal_equation (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) :
    gram (feature w v κ R) (normal w v κ R hκ) = fun _ => 1 :=
  Classical.choose_spec (normal_exists w v κ R hκ)

variable [Nonempty ι]

def coefficients (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) : ι → ℝ := affineCoefficients (normal w v κ R hκ)

def ceiling (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) : ℝ := (∑ i, normal w v κ R hκ i)⁻¹

theorem coefficients_sum (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) : ∑ i, coefficients w v κ R hκ i = 1 :=
  affineCoefficients_sum _ _ (normal_equation w v κ R hκ)

theorem ceiling_pos (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) : 0 < ceiling w v κ R hκ :=
  inv_pos.mpr (normal_mass_pos _ _ (normal_equation w v κ R hκ))

theorem coefficients_energy (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) (hw : ∀ n, 0 ≤ w n) :
    energy w v κ R (coefficients w v κ R hκ) = ceiling w v κ R hκ := by
  rw [← feature_synthesis_energy w v κ R _ hw hκ.le]
  exact affineCoefficients_energy _ _ (normal_equation w v κ R hκ)

theorem energy_completion (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) (hw : ∀ n, 0 ≤ w n) (a : ι → ℝ) (ha : ∑ i, a i = 1) :
    energy w v κ R a = ceiling w v κ R hκ +
      energy w v κ R (a - coefficients w v κ R hκ) := by
  simp_rw [← feature_synthesis_energy w v κ R _ hw hκ.le]
  exact affineCoefficients_completion _ _ a (normal_equation w v κ R hκ) ha

theorem ceiling_le_energy (w : ℕ → ℝ) (v : ι → ℕ → ℝ) (κ : ℝ) (R : ℕ)
    (hκ : 0 < κ) (hw : ∀ n, 0 ≤ w n) (a : ι → ℝ) (ha : ∑ i, a i = 1) :
    ceiling w v κ R hκ ≤ energy w v κ R a := by
  rw [← feature_synthesis_energy w v κ R _ hw hκ.le]
  exact (affineCoefficients_isLeast _ _ (normal_equation w v κ R hκ)).2 ⟨a, ha, rfl⟩

theorem ceiling_le_of_energy_le (w : ℕ → ℝ) (v : ι → ℕ → ℝ)
    (κ κ' : ℝ) (R S : ℕ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (hw : ∀ n, 0 ≤ w n)
    (he : ∀ a : ι → ℝ, energy w v κ' S a ≤ energy w v κ R a) :
    ceiling w v κ' S hκ' ≤ ceiling w v κ R hκ := by
  calc
    _ ≤ energy w v κ' S (coefficients w v κ R hκ) :=
      ceiling_le_energy w v κ' S hκ' hw _ (coefficients_sum w v κ R hκ)
    _ ≤ energy w v κ R (coefficients w v κ R hκ) := he _
    _ = _ := coefficients_energy w v κ R hκ hw

end RiemannResearch.Analysis.TruncatedGramEnvelope
