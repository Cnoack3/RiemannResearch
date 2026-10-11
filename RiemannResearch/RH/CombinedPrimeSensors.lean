/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.TwoSeedContrastObstruction

/-!
# Exact aggregate obstruction from actual prime coordinates

Source: user-provided
RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11.md,
Section 12.1 (one-prime obstruction). The finite-family extension is derived
here by retaining the shared physical coordinate in the exact sensor Gram.
This proves a finite-stage energy floor, not a positive limiting residual
or a lower bound on the actual residual gain. No RH premise is used.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.RH.Pareto.ContrastObstruction
open AdjacentPacket FiniteTwoSeedCompletion RamanujanLaguerre

/-- Prime Möbius coordinates are three physical coordinates. -/
theorem prime_mobiusDifferenceCLM_apply (q : ℕ) (hq : q.Prime)
    (f : ThresholdHilbert) :
    mobiusDifferenceCLM q f =
      hilbertSequence f q - hilbertSequence f (q - 1) - hilbertSequence f 1 := by
  classical
  have hd : q.divisors = ({1, q} : Finset ℕ) := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_prime hq, hq.ne_zero]
  rw [mobiusDifferenceCLM_apply]
  unfold mobiusDifference
  rw [hd, Finset.sum_insert (by simp [hq.ne_one.symm]), Finset.sum_singleton]
  simp [Nat.div_self hq.pos, ArithmeticFunction.moebius_apply_prime hq]
  ring

/-- Distinct odd-prime sensors share exactly the physical coordinate 1. -/
theorem primeRiesz_inner_ne (q r : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hq3 : 3 < q) (hr3 : 3 < r) (hqr : q ≠ r) :
    inner ℝ (mobiusRieszHilbert q) (mobiusRieszHilbert r) = 2 := by
  have hnd2q : ¬ 2 ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).mp h with h | h <;> omega
  have hnd2r : ¬ 2 ∣ r := by
    intro h
    rcases (Nat.dvd_prime hr).mp h with h | h <;> omega
  have hqmod : q % 2 = 1 := by
    have hzero : q % 2 ≠ 0 := by
      intro h
      exact hnd2q (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have hrmod : r % 2 = 1 := by
    have hzero : r % 2 ≠ 0 := by
      intro h
      exact hnd2r (Nat.dvd_iff_mod_eq_zero.mpr h)
    omega
  have hndq : ¬ q ∣ r := by
    intro h
    rcases (Nat.dvd_prime hr).mp h with h | h
    · omega
    · exact hqr h
  have hndsucc : ¬ q + 1 ∣ r := by
    intro h
    rcases (Nat.dvd_prime hr).mp h with h | h <;> omega
  have hndprev : ¬ q - 1 ∣ r := by
    intro h
    rcases (Nat.dvd_prime hr).mp h with h | h <;> omega
  have hd1 : dualCoeff r 1 = -1 := by
    simp [dualCoeff, hnd2r, ArithmeticFunction.moebius_apply_prime hr]
  have hdq : dualCoeff r q = 0 := by
    simp [dualCoeff, hndq, hndsucc]
  have hdp : dualCoeff r (q - 1) = 0 := by
    simp [dualCoeff, hndprev,
      Nat.sub_add_cancel (show 1 ≤ q by omega), hndq]
  rw [mobiusRieszHilbert_inner, prime_mobiusDifferenceCLM_apply q hq]
  rw [mobiusRieszHilbert_sequence r q hr.pos,
    mobiusRieszHilbert_sequence r (q - 1) hr.pos,
    mobiusRieszHilbert_sequence r 1 hr.pos, hdq, hdp, hd1]
  norm_num

/-- The correlated prime-sensor Gram matrix is diagonal plus a rank-one term. -/
theorem primeRiesz_inner (q r : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hq3 : 3 < q) (hr3 : 3 < r) :
    inner ℝ (mobiusRieszHilbert q) (mobiusRieszHilbert r) =
      2 + if q = r then 2 * (q : ℝ) ^ 2 else 0 := by
  by_cases hqr : q = r
  · subst r
    rw [real_inner_self_eq_norm_sq, mobiusRieszHilbert_norm,
      mobiusDifferenceCLM_prime_norm_sq q hq (by omega), if_pos rfl]
    ring
  · rw [primeRiesz_inner_ne q r hq hr hq3 hr3 hqr, if_neg hqr]
    ring

end RiemannResearch.RH.Pareto.ContrastObstruction

namespace RiemannResearch.Analysis.CorrelatedSensor

/-- Algebraic completion for a correlated aggregate sensor. -/
theorem aggregate_error_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r u : E) (s : ℝ) (hs : 0 ≤ s)
    (hi : inner ℝ r u = -s)
    (hn : ‖u‖ ^ 2 = 2 * s * (1 + s)) :
    ‖r‖ ^ 2 = s / (2 * (1 + s)) +
      ‖r + (1 / (2 * (1 + s))) • u‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, hn]
  have hp : (1 + s : ℝ) ≠ 0 := ne_of_gt (by linarith)
  field_simp [hp]
  ring

/-- The exact completion immediately gives the aggregate obstruction floor. -/
theorem aggregate_error_floor
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r u : E) (s : ℝ) (hs : 0 ≤ s)
    (hi : inner ℝ r u = -s)
    (hn : ‖u‖ ^ 2 = 2 * s * (1 + s)) :
    s / (2 * (1 + s)) ≤ ‖r‖ ^ 2 := by
  rw [aggregate_error_identity r u s hs hi hn]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.Analysis.CorrelatedSensor

namespace RiemannResearch.RH.Pareto.ContrastObstruction
open AdjacentPacket FiniteTwoSeedCompletion RamanujanLaguerre
open RiemannResearch.Analysis.CorrelatedSensor

def primeSensorMass (P : Finset ℕ) : ℝ :=
  ∑ q ∈ P, 1 / (q : ℝ) ^ 2

def primeSensorAggregate (P : Finset ℕ) : ThresholdHilbert :=
  ∑ q ∈ P, (1 / (q : ℝ) ^ 2) • mobiusRieszHilbert q

theorem primeSensorMass_nonneg (P : Finset ℕ) : 0 ≤ primeSensorMass P := by
  unfold primeSensorMass
  exact Finset.sum_nonneg fun q _ => div_nonneg (by norm_num) (sq_nonneg _)

theorem primeRiesz_inner_aggregate (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) (q : ℕ) (hqP : q ∈ P) :
    inner ℝ (mobiusRieszHilbert q) (primeSensorAggregate P) =
      2 * (1 + primeSensorMass P) := by
  classical
  rw [primeSensorAggregate, inner_sum]
  have hq := hP q hqP
  calc
    (∑ r ∈ P, inner ℝ (mobiusRieszHilbert q)
        ((1 / (r : ℝ)^2) • mobiusRieszHilbert r)) =
        ∑ r ∈ P, (2 / (r : ℝ)^2 + if r = q then 2 else 0) := by
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
    _ = 2 * (1 + primeSensorMass P) := by
      have hbase : (∑ r ∈ P, 2 / (r : ℝ)^2) = 2 * primeSensorMass P := by
        unfold primeSensorMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hrP
        ring
      rw [Finset.sum_add_distrib, hbase]
      simp only [Finset.sum_ite_eq', hqP, ite_true]
      ring

theorem primeSensorAggregate_norm_sq (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q) :
    ‖primeSensorAggregate P‖^2 =
      2 * primeSensorMass P * (1 + primeSensorMass P) := by
  calc
    ‖primeSensorAggregate P‖^2 =
        inner ℝ (primeSensorAggregate P) (primeSensorAggregate P) := by
      rw [real_inner_self_eq_norm_sq]
    _ = ∑ q ∈ P, (1 / (q : ℝ)^2) *
        inner ℝ (mobiusRieszHilbert q) (primeSensorAggregate P) := by
      change inner ℝ
        (∑ q ∈ P, (1 / (q : ℝ)^2) • mobiusRieszHilbert q)
        (primeSensorAggregate P) = _
      rw [sum_inner]
      simp only [real_inner_smul_left]
    _ = primeSensorMass P * (2 * (1 + primeSensorMass P)) := by
      change (∑ q ∈ P, (1 / (q : ℝ)^2) *
        inner ℝ (mobiusRieszHilbert q) (primeSensorAggregate P)) =
        (∑ q ∈ P, 1 / (q : ℝ)^2) * (2 * (1 + primeSensorMass P))
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hqP
      rw [primeRiesz_inner_aggregate P hP q hqP]
    _ = _ := by ring

theorem completedBudget_aggregate_inner (M : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ M < q)
    (F : ThresholdHilbert) (hF : F ∈ completedBudget M) :
    inner ℝ (hilbertOne-F) (primeSensorAggregate P) = -primeSensorMass P := by
  rw [primeSensorAggregate, inner_sum]
  unfold primeSensorMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q hqP
  obtain ⟨hq, hq3, hMq⟩ := hP q hqP
  have hz : mobiusDifferenceCLM q F = 0 :=
    completedBudget_le_coordinate_kernel M q hq hq3 hMq hF
  rw [real_inner_smul_right, real_inner_comm, mobiusRieszHilbert_inner,
    map_sub, prime_coordinate_one q hq, hz]
  ring

/-- All tested prime directions are combined before squaring. -/
theorem completedBudget_prime_family_error_identity (M : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ M < q)
    (F : ThresholdHilbert) (hF : F ∈ completedBudget M) :
    ‖hilbertOne-F‖^2 =
      primeSensorMass P / (2 * (1 + primeSensorMass P)) +
      ‖hilbertOne-F + (1 / (2 * (1 + primeSensorMass P))) •
        primeSensorAggregate P‖^2 := by
  apply aggregate_error_identity _ _ _ (primeSensorMass_nonneg P)
    (completedBudget_aggregate_inner M P hP F hF)
  exact primeSensorAggregate_norm_sq P (fun q hq => ⟨(hP q hq).1, (hP q hq).2.1⟩)

theorem completedBudget_prime_family_error_floor (M : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ M < q)
    (F : ThresholdHilbert) (hF : F ∈ completedBudget M) :
    primeSensorMass P / (2 * (1 + primeSensorMass P)) ≤ ‖hilbertOne-F‖^2 := by
  rw [completedBudget_prime_family_error_identity M P hP F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem actual_distance_prime_family_lower_bound (M : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ M < q) :
    primeSensorMass P / (2 * (1 + primeSensorMass P)) ≤
      CoupledResidual.distance M := by
  apply completedBudget_prime_family_error_floor M P hP (CoupledResidual.fit M)
  apply (budgetHilbert M ⊔ contrastSpan).le_topologicalClosure
  exact (show budgetHilbert M ≤ budgetHilbert M ⊔ contrastSpan from le_sup_left)
    ((budgetHilbert M).starProjection_apply_mem _)


end RiemannResearch.RH.Pareto.ContrastObstruction
