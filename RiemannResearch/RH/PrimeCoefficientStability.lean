/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CombinedPrimeSensors
import RiemannResearch.RH.TwoSeedPrimeCoefficients
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Simultaneous prime coordinate stability in the actual Pareto space

Source: user-provided consolidated zero-ordinate/Pareto handoff, Section 12.2
(prime coefficient sums). The finite-family refinement is derived here from
the exact actual prime Gram. The synthesis square retains its rank-one
cross term before using finite Cauchy-Schwarz. All observation sets are finite.
No RH or actual-gain estimate is assumed.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.ContrastObstruction
open AdjacentPacket FiniteTwoSeedCompletion RamanujanLaguerre

def primeNormalizedSynthesis (P : Finset ℕ) (c : ℕ → ℝ) : ThresholdHilbert :=
  ∑ q ∈ P, (c q / (q : ℝ)) • mobiusRieszHilbert q

def primeCoefficientEnergy (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ q ∈ P, (c q)^2

def primeSynthesisCharge (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ q ∈ P, c q / (q : ℝ)

theorem primeNormalizedSynthesis_inner (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) (q : ℕ) (hqP : q ∈ P) :
    inner ℝ (mobiusRieszHilbert q) (primeNormalizedSynthesis P c) =
      2 * primeSynthesisCharge P c + 2 * (q : ℝ) * c q := by
  classical
  rw [primeNormalizedSynthesis, inner_sum]
  have hq := hP q hqP
  calc
    (∑ r ∈ P, inner ℝ (mobiusRieszHilbert q)
        ((c r / (r : ℝ)) • mobiusRieszHilbert r)) =
        ∑ r ∈ P, (2 * (c r / (r : ℝ)) +
          if r = q then 2 * (q : ℝ) * c q else 0) := by
      apply Finset.sum_congr rfl
      intro r hrP
      have hr := hP r hrP
      rw [real_inner_smul_right, primeRiesz_inner q r hq.1 hr.1 hq.2 hr.2]
      by_cases he : r = q
      · subst r
        rw [if_pos rfl, if_pos rfl]
        have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.1.ne_zero
        field_simp [hqR]
      · simp only [if_neg he, if_neg (Ne.symm he), add_zero]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', hqP, ite_true]
      rfl

/-- Exact normalized synthesis energy. The rank-one cross term is retained. -/
theorem primeNormalizedSynthesis_norm_sq (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    ‖primeNormalizedSynthesis P c‖^2 =
      2 * primeCoefficientEnergy P c + 2 * (primeSynthesisCharge P c)^2 := by
  calc
    ‖primeNormalizedSynthesis P c‖^2 =
        inner ℝ (primeNormalizedSynthesis P c) (primeNormalizedSynthesis P c) := by
      rw [real_inner_self_eq_norm_sq]
    _ = ∑ q ∈ P, (c q / (q : ℝ)) *
        inner ℝ (mobiusRieszHilbert q) (primeNormalizedSynthesis P c) := by
      change inner ℝ
        (∑ q ∈ P, (c q / (q : ℝ)) • mobiusRieszHilbert q)
        (primeNormalizedSynthesis P c) = _
      rw [sum_inner]
      simp only [real_inner_smul_left]
    _ = ∑ q ∈ P, (2 * (c q)^2 +
        (2 * primeSynthesisCharge P c) * (c q / (q : ℝ))) := by
      apply Finset.sum_congr rfl
      intro q hqP
      rw [primeNormalizedSynthesis_inner P c hP q hqP]
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hqP).1.ne_zero
      field_simp [hqR]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change 2 * primeCoefficientEnergy P c +
        (2 * primeSynthesisCharge P c) * primeSynthesisCharge P c = _
      ring

theorem primeSynthesisCharge_sq_le (P : Finset ℕ) (c : ℕ → ℝ) :
    (primeSynthesisCharge P c)^2 ≤ primeCoefficientEnergy P c * primeSensorMass P := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq P c (fun q => 1 / (q : ℝ))
  simp only [mul_one_div, div_pow, one_pow] at h
  exact h

theorem primeNormalizedSynthesis_norm_sq_le (P : Finset ℕ) (c : ℕ → ℝ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    ‖primeNormalizedSynthesis P c‖^2 ≤
      2 * (1 + primeSensorMass P) * primeCoefficientEnergy P c := by
  rw [primeNormalizedSynthesis_norm_sq P c hP]
  nlinarith [primeSynthesisCharge_sq_le P c]

def primeSensorValues (r : ThresholdHilbert) (q : ℕ) : ℝ :=
  mobiusDifferenceCLM q r / (q : ℝ)

theorem primeSensorValues_inner (P : Finset ℕ) (r : ThresholdHilbert)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    inner ℝ r (primeNormalizedSynthesis P (primeSensorValues r)) =
      primeCoefficientEnergy P (primeSensorValues r) := by
  rw [primeNormalizedSynthesis, inner_sum]
  unfold primeCoefficientEnergy
  apply Finset.sum_congr rfl
  intro q hqP
  rw [real_inner_smul_right, real_inner_comm, mobiusRieszHilbert_inner]
  unfold primeSensorValues
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hqP).1.ne_zero
  field_simp [hqR]

/-- Simultaneous bounded observation over every finite set of primes >3. -/
theorem primeSensorValues_energy_le (P : Finset ℕ) (r : ThresholdHilbert)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    primeCoefficientEnergy P (primeSensorValues r) ≤
      2 * (1 + primeSensorMass P) * ‖r‖^2 := by
  let E := primeCoefficientEnergy P (primeSensorValues r)
  let v := primeNormalizedSynthesis P (primeSensorValues r)
  have hE : 0 ≤ E := by
    unfold E primeCoefficientEnergy
    exact Finset.sum_nonneg fun q _ => sq_nonneg _
  have hi : inner ℝ r v = E := primeSensorValues_inner P r hP
  have hcs : E ≤ ‖r‖ * ‖v‖ := by
    have h : ‖inner ℝ r v‖ ≤ ‖r‖ * ‖v‖ := norm_inner_le_norm r v
    rw [hi, Real.norm_eq_abs, abs_of_nonneg hE] at h
    exact h
  have hsq : E^2 ≤ ‖r‖^2 * ‖v‖^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hcs)
      (add_nonneg hE (mul_nonneg (norm_nonneg r) (norm_nonneg v)))
    nlinarith
  have hv : ‖v‖^2 ≤ 2 * (1 + primeSensorMass P) * E :=
    primeNormalizedSynthesis_norm_sq_le P (primeSensorValues r) hP
  have hm := mul_le_mul_of_nonneg_left hv (sq_nonneg ‖r‖)
  by_cases hzero : E = 0
  · rw [show primeCoefficientEnergy P (primeSensorValues r) = 0 from hzero]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (by linarith [primeSensorMass_nonneg P])) (sq_nonneg _)
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    have hprod : E * E ≤ (2 * (1 + primeSensorMass P) * ‖r‖^2) * E := by
      nlinarith [hsq.trans hm]
    by_contra hfail
    have hlt : 2 * (1 + primeSensorMass P) * ‖r‖^2 < E := lt_of_not_ge hfail
    have hpos := mul_pos (sub_pos.mpr hlt) hp
    nlinarith [hprod]

/-- Totalized coefficient sum lets the finite observation set use natural primes. -/
def legalCoefficientSum (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) (q : ℕ) : ℝ :=
  if hq : 0 < q then TwoSeedPrimeCoefficients.coefficientSum S a b q hq else 0

theorem legal_primeSensorValues (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) (q : ℕ)
    (hq : q.Prime) (hq3 : 3 < q) :
    primeSensorValues (hilbertOne - TwoSeedPrimeCoefficients.combination S a b) q =
      -(legalCoefficientSum S a b q + 1 / (q : ℝ)) := by
  rw [primeSensorValues, map_sub, prime_coordinate_one q hq,
    TwoSeedPrimeCoefficients.prime_coordinate_combination S a b q hq hq3]
  simp only [legalCoefficientSum, dif_pos hq.pos]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  field_simp [hqR]
  ring

/-- Simultaneous prime coefficient stability with a support-independent constant. -/
theorem legal_primeCoefficient_l2_bound (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q)
    (S : Finset {m : ℕ // 0 < m})
    (a b : {m : ℕ // 0 < m} → ℝ) :
    (∑ q ∈ P, (legalCoefficientSum S a b q + 1 / (q : ℝ))^2) ≤
      2 * (1 + primeSensorMass P) *
        ‖hilbertOne - TwoSeedPrimeCoefficients.combination S a b‖^2 := by
  have h := primeSensorValues_energy_le P
    (hilbertOne - TwoSeedPrimeCoefficients.combination S a b) hP
  have he : primeCoefficientEnergy P
      (primeSensorValues (hilbertOne - TwoSeedPrimeCoefficients.combination S a b)) =
      ∑ q ∈ P, (legalCoefficientSum S a b q + 1 / (q : ℝ))^2 := by
    unfold primeCoefficientEnergy
    apply Finset.sum_congr rfl
    intro q hqP
    rw [legal_primeSensorValues S a b q (hP q hqP).1 (hP q hqP).2]
    ring
  rwa [he] at h

end RiemannResearch.RH.Pareto.ContrastObstruction
