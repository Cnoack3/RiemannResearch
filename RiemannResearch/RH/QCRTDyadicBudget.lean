/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DyadicGronwall
import Mathlib.Topology.Order.Basic
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

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCRTDyadicBudget
open QCRTTrialCertificate QCRTInnovationBlock QCRTPeriodHeadBalance
open QSquarefreeEnergyTransitions

/-- Positive excess is taken after summing the entire signed dyadic block. -/
def normalizedDyadicExcess (t : ∀ i, addedConductors i → ℝ) (B : ℝ) (m : ℕ) : ℝ :=
  max ((∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), fullCertificate t i) - B) 0 /
    (1 + stageEnergy denseSchedule (2 ^ m))

theorem normalizedDyadicExcess_nonneg (t : ∀ i, addedConductors i → ℝ)
    (B : ℝ) (m : ℕ) : 0 ≤ normalizedDyadicExcess t B m := by
  apply div_nonneg (le_max_right _ _)
  have he : 0 ≤ stageEnergy denseSchedule (2 ^ m) := sq_nonneg _
  linarith

/-- Conditional research reduction: only this normalized signed excess
must vanish. No arithmetic provider for that limit is asserted. -/
theorem riemannHypothesis_of_normalized_dyadic_excess
    (t : ∀ i, addedConductors i → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hlim : Tendsto (normalizedDyadicExcess t B) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hlt : ∀ᶠ m in atTop, normalizedDyadicExcess t B m < 1 :=
    (tendsto_order.1 hlim).2 1 (by norm_num)
  obtain ⟨m0, hm0⟩ := eventually_atTop.1 hlt
  apply riemannHypothesis_of_vanishing_dyadic_trial_budget
    t (normalizedDyadicExcess t B) (B + 1) m0
    (normalizedDyadicExcess_nonneg t B) (by linarith) hlim
  intro m hm
  have he : 0 ≤ stageEnergy denseSchedule (2 ^ m) := sq_nonneg _
  have hd : 1 + stageEnergy denseSchedule (2 ^ m) ≠ 0 := by linarith
  have hs : (∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), fullCertificate t i) - B ≤
      normalizedDyadicExcess t B m * (1 + stageEnergy denseSchedule (2 ^ m)) := by
    rw [normalizedDyadicExcess, div_mul_cancel₀ _ hd]
    exact le_max_left _ _
  have ha := hm0 m hm
  nlinarith

/-- Energy of the complete dense squarefree optimizer on a dyadic head. -/
def dyadicEnergy (m : ℕ) : ℝ := stageEnergy denseSchedule (2 ^ m)

/-- Positive excess after subtracting all certified loss squares on a block.
The interval identity identifies the numerator with the net stage increment. -/
def netDyadicExcess (B : ℝ) (m : ℕ) : ℝ :=
  max (dyadicEnergy (m + 1) - dyadicEnergy m - B) 0 / (1 + dyadicEnergy m)

theorem netDyadicExcess_le_trial (B : ℝ) (t : ∀ i, addedConductors i → ℝ) (m : ℕ) :
    netDyadicExcess B m ≤ normalizedDyadicExcess t B m := by
  have hp : 2 ^ m ≤ (2 : ℕ) ^ (m + 1) := by rw [pow_succ]; omega
  have h := dense_energy_le_interval_certificate t _ _ hp
  have hn : dyadicEnergy (m + 1) - dyadicEnergy m - B ≤
      (∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), fullCertificate t i) - B := by
    unfold dyadicEnergy
    linarith only [h]
  have he : 0 ≤ dyadicEnergy m := sq_nonneg _
  exact div_le_div_of_nonneg_right (max_le_max hn le_rfl) (by linarith : 0 ≤ 1 + dyadicEnergy m)

/-- Sparse large excesses enter through the product of their actual
multipliers. The additive baseline is charged once per dyadic block. -/
theorem dyadic_energy_le_net_product (B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    1 + dyadicEnergy n ≤ (1 + dyadicEnergy 0 + (n : ℝ) * B) *
      ∏ i ∈ Finset.range n, (1 + netDyadicExcess B i) := by
  have hE (i : ℕ) : 0 ≤ dyadicEnergy i := sq_nonneg _
  have hpos (i : ℕ) : 0 < 1 + dyadicEnergy i := by linarith [hE i]
  have hx (i : ℕ) : 0 ≤ netDyadicExcess B i :=
    div_nonneg (le_max_right _ _) (hpos i).le
  have hp (i : ℕ) : 1 ≤ ∏ j ∈ Finset.range i, (1 + netDyadicExcess B j) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Finset.prod_range_succ]
      nlinarith only [ih, hx i, mul_nonneg (sub_nonneg.mpr ih) (hx i)]
  induction n with
  | zero => simp
  | succ n ih =>
    have he : dyadicEnergy (n + 1) - dyadicEnergy n - B ≤
        netDyadicExcess B n * (1 + dyadicEnergy n) := by
      rw [netDyadicExcess, div_mul_cancel₀ _ (hpos n).ne']
      exact le_max_left _ _
    have hstep : 1 + dyadicEnergy (n + 1) ≤
        (1 + dyadicEnergy n) * (1 + netDyadicExcess B n) + B := by
      nlinarith only [he]
    have hmul := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 + netDyadicExcess B n by linarith [hx n])
    have hbase := mul_nonneg hB (sub_nonneg.mpr (hp (n + 1)))
    rw [Finset.prod_range_succ] at hbase ⊢
    push_cast
    nlinarith only [hstep, hmul, hbase]

/-- Subpolynomial cumulative multiplicative excess on one cofinal
subsequence of dyadic blocks suffices for RH. -/
theorem riemannHypothesis_of_cofinal_net_product
    (B : ℝ) (hB : 0 ≤ B) (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (hsmall : Tendsto (fun j =>
      Real.log ((1 + dyadicEnergy 0 + (s j : ℝ) * B) *
        ∏ i ∈ Finset.range (s j), (1 + netDyadicExcess B i)) /
        Real.log ((2 ^ (s j) + 2 : ℕ) : ℝ)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hpow : Tendsto (fun j : ℕ => (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  apply QCRTOptimizerGrowth.riemannHypothesis_of_cofinal_subpolynomial_stageEnergy
    (fun j => 2 ^ (s j)) (hpow.comp hs)
  have hE (j : ℕ) : 0 ≤ dyadicEnergy (s j) := sq_nonneg _
  have hD (j : ℕ) : 0 ≤ Real.log ((2 ^ (s j) + 2 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ (2 : ℕ) ^ (s j) + 2 from Nat.succ_le_succ (Nat.zero_le _))
  exact squeeze_zero (fun j => div_nonneg (Real.log_nonneg (by linarith [hE j] :
      1 ≤ 1 + dyadicEnergy (s j))) (hD j))
    (fun j => div_le_div_of_nonneg_right (Real.log_le_log
      (by linarith [hE j] : 0 < 1 + dyadicEnergy (s j))
      (dyadic_energy_le_net_product B hB (s j))) (hD j)) hsmall

end RiemannResearch.RH.QCRTDyadicBudget
