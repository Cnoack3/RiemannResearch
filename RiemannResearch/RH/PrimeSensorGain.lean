/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeCoefficientGain
import RiemannResearch.RH.PrimeSensorProjection
import RiemannResearch.RH.ResidualCutoffSchedule
import RiemannResearch.RH.DyadicGainZeroBudget
import RiemannResearch.RH.CoupledResidualCorrections
import RiemannResearch.RH.TwoSeedContrastObstruction
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact prime observation energy in the actual legal projection gain

Source: user-provided consolidated zero-ordinate/Pareto handoff (2026-10-11),
Sections 5, 6, 12 and 15. The exact finite sensor projection is applied to the
actual full-budget fit increment, not to an independently optimized prime fit.
The remainder squares and cumulative signed identity are retained.

The RH consumer is a conditional research reduction: a nonsummable lower
schedule for the normalized actual observation energies remains Open.
The finite zero-exclusion implications also require their stated numerical
gain inequalities. None of these theorems proves such an arithmetic provider.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.CoupledResidual
open ContrastObstruction FiniteTwoSeedCompletion RamanujanLaguerre

def primeObservedFitEnergy (P : Finset ℕ) (B : ℕ) : ℝ :=
  primeObservedEnergy P (primeSensorValues (fit B))

theorem primeSensorValues_fit_increment (A B : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ A < q) :
    ∀ q ∈ P, primeSensorValues (fit B - fit A) q = primeSensorValues (fit B) q := by
  intro q hqP
  obtain ⟨hq, hq3, hAq⟩ := hP q hqP
  have hz : mobiusDifferenceCLM q (fit A) = 0 :=
    budget_le_coordinate_kernel A q hq hq3 hAq
      ((budgetHilbert A).starProjection_apply_mem _)
  simp only [primeSensorValues, map_sub, hz, sub_zero]

theorem primeObservedFitEnergy_distance_drop_identity (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ A < q) :
    distance A - distance B = primeObservedFitEnergy P B +
      ‖fit B - fit A - primeDebiasedSynthesis P (primeSensorValues (fit B))‖^2 := by
  rw [distance_sub A B hAB]
  exact primeObservedEnergy_interpolation_identity P _
    (fun q hqP => ⟨(hP q hqP).1, (hP q hqP).2.1⟩) _
    (primeSensorValues_fit_increment A B P hP)

theorem primeObservedFitEnergy_le_distance_drop (A B : ℕ) (hAB : A ≤ B)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ A < q) :
    primeObservedFitEnergy P B ≤ distance A - distance B := by
  rw [primeObservedFitEnergy_distance_drop_identity A B hAB P hP]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem primeObservedFitEnergy_improves_coarse_bound (P : Finset ℕ) (B : ℕ) :
    primeFitEnergy P B / (2 * (1 + primeSensorMass P)) ≤ primeObservedFitEnergy P B :=
  primeObservedEnergy_lower_bound P _

theorem normalized_primeObservedFitEnergy_le_cutoffGain
    (M : ℕ → ℕ) (hM : Monotone M) (n : ℕ)
    (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime ∧ 3 < q ∧ M n < q) :
    primeObservedFitEnergy P (M (n + 1)) / distance (M n) ≤ cutoffRelativeGain M n :=
  div_le_div_of_nonneg_right
    (primeObservedFitEnergy_le_distance_drop _ _ (hM (Nat.le_succ n)) P hP)
    (distance_pos _).le

theorem riemannHypothesis_of_primeObservedFitEnergy_minorant
    (M : ℕ → ℕ) (hM : Monotone M) (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ q ∈ P n, q.Prime ∧ 3 < q ∧ M n < q)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hdiv : ¬ Summable a)
    (hobs : ∀ n, a n ≤ primeObservedFitEnergy (P n) (M (n + 1)) / distance (M n)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cutoff_gain_minorant M hM a ha hdiv
  intro n
  exact (hobs n).trans (normalized_primeObservedFitEnergy_le_cutoffGain M hM n (P n) (hP n))

theorem primeObservedFitEnergy_sum_identity
    (M : ℕ → ℕ) (hM : Monotone M) (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ q ∈ P n, q.Prime ∧ 3 < q ∧ M n < q) (N : ℕ) :
    distance (M 0) - distance (M N) =
      (∑ n ∈ Finset.range N, primeObservedFitEnergy (P n) (M (n + 1))) +
      ∑ n ∈ Finset.range N,
        ‖fit (M (n + 1)) - fit (M n) -
          primeDebiasedSynthesis (P n) (primeSensorValues (fit (M (n + 1))))‖^2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hs := primeObservedFitEnergy_distance_drop_identity
      (M N) (M (N + 1)) (hM (Nat.le_succ N)) (P N) (hP N)
    linarith

theorem primeObservedFitEnergy_sum_le_distance_drop
    (M : ℕ → ℕ) (hM : Monotone M) (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ q ∈ P n, q.Prime ∧ 3 < q ∧ M n < q) (N : ℕ) :
    (∑ n ∈ Finset.range N, primeObservedFitEnergy (P n) (M (n + 1))) ≤
      distance (M 0) - distance (M N) := by
  rw [primeObservedFitEnergy_sum_identity M hM P hP N]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem primeObservedFitEnergy_sum_le_of_zeta_zero
    (M : ℕ → ℕ) (hM : Monotone M) (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ q ∈ P n, q.Prime ∧ 3 < q ∧ M n < q) (N : ℕ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (∑ n ∈ Finset.range N, primeObservedFitEnergy (P n) (M (n + 1))) ≤
      distance (M 0) - (2 * s.re - 1) / ‖s‖ ^ 2 :=
  (primeObservedFitEnergy_sum_le_distance_drop M hM P hP N).trans
    (sub_le_sub_left (distance_lower_bound_of_zeta_zero _ s hs hs1 hz) _)

theorem zeta_ne_zero_of_primeObservedFitEnergy
    (M : ℕ → ℕ) (hM : Monotone M) (P : ℕ → Finset ℕ)
    (hP : ∀ n, ∀ q ∈ P n, q.Prime ∧ 3 < q ∧ M n < q) (N : ℕ)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hgain : distance (M 0) - (2 * s.re - 1) / ‖s‖ ^ 2 <
      ∑ n ∈ Finset.range N, primeObservedFitEnergy (P n) (M (n + 1))) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact (not_le_of_gt hgain)
    (primeObservedFitEnergy_sum_le_of_zeta_zero M hM P hP N s hs hs1 hz)

end RiemannResearch.RH.Pareto.CoupledResidual
