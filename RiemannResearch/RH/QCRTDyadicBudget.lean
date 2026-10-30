/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DyadicGronwall
import RiemannResearch.RH.QCRTTrialCertificate
import RiemannResearch.RH.QCRTOptimizerGrowth
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QCRTInnovationBlock
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import Lean.Elab.Tactic.Omega

/-!
# Conditional signed dyadic budgets for the complete squarefree optimizer

Source: user-provided full-squarefree research handoff, priorities 3 and 4.
The exact interval identity retains signed certificates and norm-square loss.
The analytic consumer only requires vanishing multiplicative overhead, improving
the proposed sufficient condition A/(m+1). The arithmetic budget remains Open.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCRTDyadicBudget
open QCRTTrialCertificate QCRTInnovationBlock QCRTPeriodHeadBalance
open QSquarefreeEnergyTransitions QCRTOptimizerGrowth
open RiemannResearch.Analysis.DyadicGronwall

/-- Exact signed accounting on every finite interval, including all stages
without a prime enlargement and retaining every trial-loss square. -/
theorem dense_trial_interval (t : ∀ i, addedConductors i → ℝ)
    (M N : ℕ) (hMN : M ≤ N) :
    stageEnergy denseSchedule N = stageEnergy denseSchedule M +
      (∑ i ∈ Finset.Ico M N, fullCertificate t i) -
      ∑ i ∈ Finset.Ico M N, fullLoss t i := by
  rw [Finset.sum_Ico_eq_sub _ hMN, Finset.sum_Ico_eq_sub _ hMN]
  have hN := dense_trial_telescope t N
  have hM := dense_trial_telescope t M
  linarith

theorem dense_energy_le_interval_certificate (t : ∀ i, addedConductors i → ℝ)
    (M N : ℕ) (hMN : M ≤ N) :
    stageEnergy denseSchedule N ≤ stageEnergy denseSchedule M +
      ∑ i ∈ Finset.Ico M N, fullCertificate t i := by
  rw [dense_trial_interval t M N hMN]
  exact sub_le_self _ (Finset.sum_nonneg (fun i _ => fullLoss_nonneg t i))

/-- Conditional research reduction. The eventual signed budget is the sole
arithmetic provider. Its multiplier may decay arbitrarily slowly to zero;
the harmonic rate in the original agenda is sufficient but unnecessary. -/
theorem riemannHypothesis_of_vanishing_dyadic_trial_budget
    (t : ∀ i, addedConductors i → ℝ) (a : ℕ → ℝ) (B : ℝ) (m0 : ℕ)
    (ha : ∀ m, 0 ≤ a m) (hB : 0 ≤ B)
    (ha0 : Tendsto a atTop (𝓝 0))
    (hbudget : ∀ m, m0 ≤ m →
      (∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), fullCertificate t i) ≤
        a m * stageEnergy denseSchedule (2 ^ m) + B) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_subpolynomial_stageEnergy
    (fun n => 2 ^ (n + m0 + 1)) (dyadic_tendsto_atTop m0)
  apply relativeLog_dyadic_of_eventual_recurrence
    (stageEnergy denseSchedule) a B m0 (fun _ => sq_nonneg _) ha hB ha0
  intro m hm
  have hpow : 2 ^ m ≤ (2 : ℕ) ^ (m + 1) := by
    rw [pow_succ]
    omega
  have he := dense_energy_le_interval_certificate t (2 ^ m) (2 ^ (m + 1)) hpow
  have hb := hbudget m hm
  nlinarith

/-- The dyadic target stated in the handoff, allowing a finite starting index.
No estimate for the budget is supplied by this consumer. -/
theorem riemannHypothesis_of_harmonic_dyadic_trial_budget
    (t : ∀ i, addedConductors i → ℝ) (A B : ℝ) (m0 : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbudget : ∀ m, m0 ≤ m →
      (∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), fullCertificate t i) ≤
        (A / ((m + 1 : ℕ) : ℝ)) * stageEnergy denseSchedule (2 ^ m) + B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_vanishing_dyadic_trial_budget t
    (fun m => A / ((m + 1 : ℕ) : ℝ)) B m0
    (fun _ => div_nonneg hA (by positivity)) hB
  · have hd : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact hd.const_div_atTop A
  · exact hbudget

end RiemannResearch.RH.QCRTDyadicBudget
