/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCovarianceScreening
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Trial vectors for actual screened Q covariance

Source: user-requested Möbius prime-packet investigation, 16 October 2026.
These identities retain the full signed source, every Schur covariance entry,
and the exact nonnegative capacity remainder. They do not assert growth.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCovarianceTrial

open ZetaTwoHilbert QCovarianceInverse QCovarianceInvertibility QCovarianceScreening
open RiemannResearch.Analysis FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def trialVector (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (t : κ → ℝ) : QHilbert :=
  ∑ j, t j • screenedResidue a b ha hia j

def trialSource (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (t : κ → ℝ) : ℝ :=
  dotProduct t (screenedMean a b ha hia)

def trialEnergy (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (t : κ → ℝ) : ℝ :=
  ‖trialVector a b ha hia t‖ ^ 2

omit [DecidableEq κ] in
theorem trialSource_eq_signed (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (t : κ → ℝ) :
    trialSource a b ha hia t =
      ∑ j, t j * (qMean b j -
        ∑ i, covarianceInverseSource a i * crossCovariance a b i j) := by
  unfold trialSource dotProduct
  simp_rw [screenedMean_entry a b ha hia]

omit [DecidableEq κ] in
theorem trialSource_eq_residual_pairing (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (t : κ → ℝ) :
    trialSource a b ha hia t =
      (1 + covarianceInformation a) * inner ℝ
        (qOne - qSynthesis a (fun i =>
          covarianceInverseSource a i / (1 + covarianceInformation a)))
        (qSynthesis b t) := by
  unfold trialSource dotProduct
  simp only [qSynthesis, inner_sum, real_inner_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [screenedMean_eq_residual_correlation a b ha hia j]
  simp only [qSynthesis, div_eq_mul_inv, mul_comm]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem trialEnergy_eq_covariance (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (t : κ → ℝ) :
    trialEnergy a b ha hia t =
      ∑ i, t i * (∑ j, screenedCovariance a b ha hia i j * t j) := by
  unfold trialEnergy
  rw [← real_inner_self_eq_norm_sq]
  unfold trialVector screenedCovariance gramMatrix
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (screenedResidue a b ha hia j) (screenedResidue a b ha hia i)]
  ring

omit [DecidableEq κ] in
theorem trialEnergy_eq_full_schur (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a) (t : κ → ℝ) :
    trialEnergy a b ha hia t =
      ∑ i, t i * (∑ j, (qCov b i j -
        ∑ k, crossCovariance a b k i * projectionCoefficients a b j k) * t j) := by
  rw [trialEnergy_eq_covariance]
  simp_rw [screenedCovariance_entry a b ha hia]

omit [DecidableEq ι] [DecidableEq κ] in
theorem trialEnergy_pos (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b))
    (t : κ → ℝ) (ht : t ≠ 0) :
    0 < trialEnergy a b ha hia t := by
  unfold trialEnergy
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply ht
  apply (screened_independent a b ha hia hb hab).fintypeLinearCombination_injective
  change trialVector a b ha hia t =
    Fintype.linearCombination ℝ (screenedResidue a b ha hia) 0
  simpa only [map_zero] using hz

theorem trialSource_sq_le_gain_mul_energy (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b))
    (t : κ → ℝ) :
    trialSource a b ha hia t ^ 2 ≤
      (covarianceInformation (Sum.elim a b) - covarianceInformation a) *
        trialEnergy a b ha hia t := by
  let hs := screened_independent a b ha hia hb hab
  have h := source_sq_le_capacity_mul_energy hs (screenedMean a b ha hia) t
  rw [covarianceInformation_gain a b ha hia hb hab,
    screenedInverseSource_eq_inverseSource a b ha hia hb hab]
  have hc : dotProduct (screenedMean a b ha hia)
      (inverseSource hs (screenedMean a b ha hia)) =
      capacity hs (screenedMean a b ha hia) := by
    unfold dotProduct capacity
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hc]
  exact h

theorem trial_lower_bound (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b))
    (t : κ → ℝ) (ht : t ≠ 0) :
    trialSource a b ha hia t ^ 2 / trialEnergy a b ha hia t ≤
      covarianceInformation (Sum.elim a b) - covarianceInformation a := by
  exact (div_le_iff₀ (trialEnergy_pos a b ha hia hb hab t ht)).mpr
    (trialSource_sq_le_gain_mul_energy a b ha hia hb hab t)

theorem trial_gain_complete (a : ι → ℕ) (b : κ → ℕ)
    (ha : ∀ i, 1 < a i) (hia : Function.Injective a)
    (hb : ∀ j, 1 < b j) (hab : Function.Injective (Sum.elim a b))
    (t : κ → ℝ) (ht : t ≠ 0) :
    covarianceInformation (Sum.elim a b) - covarianceInformation a =
      trialSource a b ha hia t ^ 2 / trialEnergy a b ha hia t +
        ‖minimumVector (screened_independent a b ha hia hb hab)
          (screenedMean a b ha hia) -
          (trialSource a b ha hia t / trialEnergy a b ha hia t) •
            trialVector a b ha hia t‖ ^ 2 := by
  let hs := screened_independent a b ha hia hb hab
  let α := trialSource a b ha hia t
  let E := trialEnergy a b ha hia t
  have hE : E ≠ 0 := ne_of_gt (trialEnergy_pos a b ha hia hb hab t ht)
  have hi : inner ℝ (minimumVector hs (screenedMean a b ha hia))
      (trialVector a b ha hia t) = α := by
    rw [real_inner_comm]
    exact inner_synthesis_minimumVector hs (screenedMean a b ha hia) t
  have hc : covarianceInformation (Sum.elim a b) - covarianceInformation a =
      ‖minimumVector hs (screenedMean a b ha hia)‖ ^ 2 := by
    rw [covarianceInformation_gain a b ha hia hb hab,
      screenedInverseSource_eq_inverseSource a b ha hia hb hab]
    rw [← capacity_eq_norm_sq]
    unfold dotProduct capacity
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  change _ = α^2/E +
    ‖minimumVector hs (screenedMean a b ha hia) -
      (α/E) • trialVector a b ha hia t‖^2
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hi]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  have hw : ‖trialVector a b ha hia t‖ ^ 2 = E := rfl
  rw [hw, hc]
  field_simp [hE]
  ring

end RiemannResearch.RH.QCovarianceTrial
