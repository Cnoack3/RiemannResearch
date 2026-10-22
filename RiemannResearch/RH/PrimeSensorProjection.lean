/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeCoefficientStability
import RiemannResearch.RH.CombinedPrimeSensors
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact projection onto finite families of actual prime sensors

Source: user-provided consolidated zero-ordinate/Pareto handoff (2026-10-11),
Sections 12 and 15: retain the prime coefficient sums and their full Gram cost.
The rank-one inverse and completed-square refinements are derived here from
the existing exact Gram of the actual Pareto Riesz vectors. No mathematical
novelty claim is made. All observation sets are finite; no RH premise is used.

The debiased synthesis is the minimum-norm vector realizing the observations.
It is a physical sensor projection, not a claimed legal two-seed correction.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.ContrastObstruction
open AdjacentPacket FiniteTwoSeedCompletion RamanujanLaguerre

def primeDebiasedSynthesis (P : Finset ℕ) (c : ℕ → ℝ) : ThresholdHilbert :=
  (1 / 2 : ℝ) • (primeNormalizedSynthesis P c -
    (primeSynthesisCharge P c / (1 + primeSensorMass P)) • primeSensorAggregate P)

def primeObservedEnergy (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  (primeCoefficientEnergy P c - (primeSynthesisCharge P c)^2 /
    (1 + primeSensorMass P)) / 2

theorem primeNormalizedSynthesis_inner_aggregate (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    inner ℝ (primeNormalizedSynthesis P c) (primeSensorAggregate P) =
      2 * (1 + primeSensorMass P) * primeSynthesisCharge P c := by
  rw [primeNormalizedSynthesis, sum_inner]
  simp only [real_inner_smul_left]
  unfold primeSynthesisCharge
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hqP
  rw [primeRiesz_inner_aggregate P hP q hqP]
  ring

theorem primeDebiasedSynthesis_inner (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) (q : ℕ) (hqP : q ∈ P) :
    inner ℝ (mobiusRieszHilbert q) (primeDebiasedSynthesis P c) =
      (q : ℝ) * c q := by
  rw [primeDebiasedSynthesis, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, primeNormalizedSynthesis_inner P c hP q hqP,
    primeRiesz_inner_aggregate P hP q hqP]
  have hH : 1 + primeSensorMass P ≠ 0 :=
    ne_of_gt (by linarith [primeSensorMass_nonneg P])
  field_simp [hH]
  ring

theorem primeDebiasedSynthesis_interpolates (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) (q : ℕ) (hqP : q ∈ P) :
    primeSensorValues (primeDebiasedSynthesis P c) q = c q := by
  rw [primeSensorValues, ← mobiusRieszHilbert_inner,
    primeDebiasedSynthesis_inner P c hP q hqP]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hqP).1.ne_zero
  exact mul_div_cancel_left₀ _ hqR

theorem primeDebiasedSynthesis_norm_sq (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    ‖primeDebiasedSynthesis P c‖^2 = primeObservedEnergy P c := by
  rw [primeDebiasedSynthesis, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, primeNormalizedSynthesis_norm_sq P c hP,
    primeNormalizedSynthesis_inner_aggregate P c hP, primeSensorAggregate_norm_sq P hP]
  unfold primeObservedEnergy
  have hH : 1 + primeSensorMass P ≠ 0 :=
    ne_of_gt (by linarith [primeSensorMass_nonneg P])
  field_simp [hH]
  ring

theorem primeSensorValues_inner_aggregate (P : Finset ℕ) (r : ThresholdHilbert) :
    inner ℝ r (primeSensorAggregate P) =
      primeSynthesisCharge P (primeSensorValues r) := by
  rw [primeSensorAggregate, inner_sum]
  unfold primeSynthesisCharge
  apply Finset.sum_congr rfl
  intro q hqP
  rw [real_inner_smul_right, real_inner_comm, mobiusRieszHilbert_inner]
  unfold primeSensorValues
  ring

theorem primeSensorValues_inner_debiased (P : Finset ℕ) (r : ThresholdHilbert)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    inner ℝ r (primeDebiasedSynthesis P (primeSensorValues r)) =
      primeObservedEnergy P (primeSensorValues r) := by
  rw [primeDebiasedSynthesis, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, primeSensorValues_inner P r hP,
    primeSensorValues_inner_aggregate]
  unfold primeObservedEnergy
  ring

theorem primeObservedEnergy_error_identity (P : Finset ℕ) (r : ThresholdHilbert)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    ‖r‖^2 = primeObservedEnergy P (primeSensorValues r) +
      ‖r - primeDebiasedSynthesis P (primeSensorValues r)‖^2 := by
  rw [norm_sub_sq_real, primeDebiasedSynthesis_norm_sq P _ hP,
    primeSensorValues_inner_debiased P r hP]
  ring

theorem primeObservedEnergy_le_norm_sq (P : Finset ℕ) (r : ThresholdHilbert)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    primeObservedEnergy P (primeSensorValues r) ≤ ‖r‖^2 := by
  rw [primeObservedEnergy_error_identity P r hP]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem primeObservedEnergy_lower_bound (P : Finset ℕ) (c : ℕ → ℝ) :
    primeCoefficientEnergy P c / (2 * (1 + primeSensorMass P)) ≤
      primeObservedEnergy P c := by
  have hH : 0 < 1 + primeSensorMass P := by linarith [primeSensorMass_nonneg P]
  have hCS := primeSynthesisCharge_sq_le P c
  have hc := div_le_div_of_nonneg_right hCS hH.le
  have hid : primeCoefficientEnergy P c * primeSensorMass P / (1 + primeSensorMass P) +
      primeCoefficientEnergy P c / (1 + primeSensorMass P) = primeCoefficientEnergy P c := by
    field_simp [ne_of_gt hH]
    ring
  unfold primeObservedEnergy
  calc
    primeCoefficientEnergy P c / (2 * (1 + primeSensorMass P)) =
        (primeCoefficientEnergy P c / (1 + primeSensorMass P)) / 2 := by
      rw [div_div]
      congr 1
      ring
    _ ≤ (primeCoefficientEnergy P c - (primeSynthesisCharge P c)^2 /
        (1 + primeSensorMass P)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith

theorem primeObservedEnergy_congr (P : Finset ℕ) (c d : ℕ → ℝ)
    (h : ∀ q ∈ P, c q = d q) : primeObservedEnergy P c = primeObservedEnergy P d := by
  have hE : primeCoefficientEnergy P c = primeCoefficientEnergy P d := by
    unfold primeCoefficientEnergy
    apply Finset.sum_congr rfl
    intro q hqP
    rw [h q hqP]
  have hT : primeSynthesisCharge P c = primeSynthesisCharge P d := by
    unfold primeSynthesisCharge
    apply Finset.sum_congr rfl
    intro q hqP
    rw [h q hqP]
  simp only [primeObservedEnergy, hE, hT]

theorem primeDebiasedSynthesis_congr (P : Finset ℕ) (c d : ℕ → ℝ)
    (h : ∀ q ∈ P, c q = d q) : primeDebiasedSynthesis P c = primeDebiasedSynthesis P d := by
  have hV : primeNormalizedSynthesis P c = primeNormalizedSynthesis P d := by
    unfold primeNormalizedSynthesis
    apply Finset.sum_congr rfl
    intro q hqP
    rw [h q hqP]
  have hT : primeSynthesisCharge P c = primeSynthesisCharge P d := by
    unfold primeSynthesisCharge
    apply Finset.sum_congr rfl
    intro q hqP
    rw [h q hqP]
  simp only [primeDebiasedSynthesis, hV, hT]

theorem primeObservedEnergy_interpolation_identity (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) (r : ThresholdHilbert)
    (hobs : ∀ q ∈ P, primeSensorValues r q = c q) :
    ‖r‖^2 = primeObservedEnergy P c + ‖r - primeDebiasedSynthesis P c‖^2 := by
  have h := primeObservedEnergy_error_identity P r hP
  rwa [primeObservedEnergy_congr P _ c hobs, primeDebiasedSynthesis_congr P _ c hobs] at h

theorem primeDebiasedSynthesis_minimum (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) (r : ThresholdHilbert)
    (hobs : ∀ q ∈ P, primeSensorValues r q = c q) :
    ‖primeDebiasedSynthesis P c‖^2 ≤ ‖r‖^2 := by
  rw [primeDebiasedSynthesis_norm_sq P c hP,
    primeObservedEnergy_interpolation_identity P c hP r hobs]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem primeObservedEnergy_nonneg (P : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ primeObservedEnergy P c := by
  apply le_trans _ (primeObservedEnergy_lower_bound P c)
  apply div_nonneg
  · exact Finset.sum_nonneg fun q _ => sq_nonneg _
  · linarith [primeSensorMass_nonneg P]

theorem primeObservedEnergy_upper_bound (P : Finset ℕ) (c : ℕ → ℝ) :
    primeObservedEnergy P c ≤ primeCoefficientEnergy P c / 2 := by
  unfold primeObservedEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by linarith [primeSensorMass_nonneg P]))

def primePairwiseDefect (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ q ∈ P, ∑ r ∈ P, (c q / (r : ℝ) - c r / (q : ℝ))^2

theorem primePairwiseDefect_eq (P : Finset ℕ) (c : ℕ → ℝ) :
    primePairwiseDefect P c =
      2 * (primeCoefficientEnergy P c * primeSensorMass P - (primeSynthesisCharge P c)^2) := by
  unfold primePairwiseDefect
  calc
    (∑ q ∈ P, ∑ r ∈ P, (c q / (r : ℝ) - c r / (q : ℝ))^2) =
        ∑ q ∈ P, ((c q)^2 * primeSensorMass P -
          2 * (c q / (q : ℝ)) * primeSynthesisCharge P c +
          (1 / (q : ℝ)^2) * primeCoefficientEnergy P c) := by
      apply Finset.sum_congr rfl
      intro q hqP
      unfold primeSensorMass primeSynthesisCharge primeCoefficientEnergy
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hrP
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
      have hT : (∑ q ∈ P, 2 * (c q / (q : ℝ)) * primeSynthesisCharge P c) =
          2 * (primeSynthesisCharge P c)^2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        change (2 * primeSynthesisCharge P c) * primeSynthesisCharge P c = _
        ring
      have hE : (∑ q ∈ P, (1 / (q : ℝ)^2) * primeCoefficientEnergy P c) =
          primeSensorMass P * primeCoefficientEnergy P c := by
        rw [← Finset.sum_mul]
        rfl
      rw [hT, hE]
      change primeCoefficientEnergy P c * primeSensorMass P -
        2 * (primeSynthesisCharge P c)^2 + primeSensorMass P * primeCoefficientEnergy P c = _
      ring

theorem primeObservedEnergy_improvement_identity (P : Finset ℕ) (c : ℕ → ℝ) :
    primeObservedEnergy P c =
      primeCoefficientEnergy P c / (2 * (1 + primeSensorMass P)) +
      primePairwiseDefect P c / (4 * (1 + primeSensorMass P)) := by
  rw [primePairwiseDefect_eq]
  unfold primeObservedEnergy
  have hH : 1 + primeSensorMass P ≠ 0 :=
    ne_of_gt (by linarith [primeSensorMass_nonneg P])
  field_simp [hH]
  ring

theorem primePairwiseDefect_harmonic (P : Finset ℕ) (a : ℝ) :
    primePairwiseDefect P (fun q => a / (q : ℝ)) = 0 := by
  unfold primePairwiseDefect
  apply Finset.sum_eq_zero
  intro q hqP
  apply Finset.sum_eq_zero
  intro r hrP
  have h : a / (q : ℝ) / (r : ℝ) - a / (r : ℝ) / (q : ℝ) = 0 := by ring
  rw [h]
  norm_num

theorem primeObservedEnergy_harmonic (P : Finset ℕ) (a : ℝ) :
    primeObservedEnergy P (fun q => a / (q : ℝ)) =
      a^2 * primeSensorMass P / (2 * (1 + primeSensorMass P)) := by
  rw [primeObservedEnergy_improvement_identity, primePairwiseDefect_harmonic]
  have hE : primeCoefficientEnergy P (fun q => a / (q : ℝ)) =
      a^2 * primeSensorMass P := by
    unfold primeCoefficientEnergy primeSensorMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hqP
    rw [div_pow]
    ring
  rw [hE]
  simp

end RiemannResearch.RH.Pareto.ContrastObstruction
