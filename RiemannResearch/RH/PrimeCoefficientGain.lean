/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeCoefficientStability
import RiemannResearch.RH.ResidualCutoffSchedule

/-!
# Actual new-prime coefficient energy as a residual-gain sensor

Source: user-provided consolidated zero-ordinate/Pareto handoff, Section 15,
Priority 2 (retain coefficient-sum directions together with their full cost).
The exact finite prime Gram and actual full-budget projections are used.
A nonsummable lower bound on the actual prime-fit energy is an explicit open
provider. The implication to RH uses no RH assumption.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoupledResidual
open ContrastObstruction FiniteTwoSeedCompletion RamanujanLaguerre

/-- At a prime, this is the square sum of the actual two-seed coefficients.
The full Pareto optimizer is computed before restricting to the prime set. -/
def primeFitEnergy (P : Finset ℕ) (B : ℕ) : ℝ :=
  primeCoefficientEnergy P (primeSensorValues (fit B))

theorem primeFitEnergy_le_distance_drop (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ A < q) :
    primeFitEnergy P B ≤
      2 * (1 + primeSensorMass P) * (distance A - distance B) := by
  have h := primeSensorValues_energy_le P (fit B - fit A)
    (fun q hq => ⟨(hP q hq).1, (hP q hq).2.1⟩)
  have he : primeCoefficientEnergy P (primeSensorValues (fit B - fit A)) =
      primeFitEnergy P B := by
    unfold primeCoefficientEnergy primeFitEnergy
    apply Finset.sum_congr rfl
    intro q hqP
    obtain ⟨hq, hq3, hAq⟩ := hP q hqP
    have hz : mobiusDifferenceCLM q (fit A) = 0 :=
      budget_le_coordinate_kernel A q hq hq3 hAq
        ((budgetHilbert A).starProjection_apply_mem _)
    simp only [primeSensorValues, map_sub, hz, sub_zero]
  rw [he, ← distance_sub A B hAB] at h
  exact h

theorem normalized_primeFitEnergy_le_cutoffGain
    (M : ℕ → ℕ) (hM : Monotone M) (n : ℕ)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ M n < q) :
    primeFitEnergy P (M (n + 1)) /
      (2 * (1 + primeSensorMass P) * distance (M n)) ≤ cutoffRelativeGain M n := by
  have hC : 0 < 2 * (1 + primeSensorMass P) := by
    linarith [primeSensorMass_nonneg P]
  have hlow : primeFitEnergy P (M (n + 1)) /
      (2 * (1 + primeSensorMass P)) ≤ distance (M n) - distance (M (n + 1)) := by
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm] using
      primeFitEnergy_le_distance_drop (M n) (M (n + 1)) (hM (Nat.le_succ n)) P hP
  have hd := div_le_div_of_nonneg_right hlow (distance_pos (M n)).le
  simpa only [div_div, cutoffRelativeGain] using hd

/-- Conditional arithmetic reduction: a nonsummable lower schedule for
the actual newly visible prime coefficient mass implies RH. -/
theorem riemannHypothesis_of_primeFitEnergy_minorant
    (M : ℕ → ℕ) (hM : Monotone M) (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ q ∈ P n, q.Prime ∧ 3 < q ∧ M n < q)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hdiv : ¬ Summable a)
    (hobs : ∀ n, a n ≤ primeFitEnergy (P n) (M (n + 1)) /
      (2 * (1 + primeSensorMass (P n)) * distance (M n))) : RiemannHypothesis := by
  apply riemannHypothesis_of_cutoff_gain_minorant M hM a ha hdiv
  intro n
  exact (hobs n).trans (normalized_primeFitEnergy_le_cutoffGain M hM n (P n) (hP n))

end RiemannResearch.RH.Pareto.CoupledResidual
