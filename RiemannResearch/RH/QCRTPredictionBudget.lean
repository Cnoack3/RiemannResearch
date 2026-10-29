/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QExactHeadSubpolynomial
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual next-site prediction budgets as conditional RH criteria

Source: the user's minimum-energy optimizer agenda, 29 October 2026,
Sections 3--7. All dictionary, feasibility, and complete-energy estimates are
provided by QSquarefreeEnergyTransitions. The supplied arithmetic premise
is subpolynomial growth of its literal predictionBudget, or the stronger
uniform bound on its actual nextMismatch. Neither premise is proved here.
The Mellin-zero consumer is the existing QExactHeadSubpolynomial theorem.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTPredictionBudget
open ZetaTwoHilbert ZetaTwoProbability
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions
open QExactHeadSubpolynomial
open RiemannResearch.Analysis.SubpolynomialWindow

def trial (N : ℕ) : QHilbert := minimumAt (denseSchedule N) (N + 1)

theorem trial_legal (N : ℕ) : trial N ∈ qSquarefreeCRTSpan :=
  minimumAt_legal _ _

theorem trial_head (N k : ℕ) (hk : 0 < k) (hkN : k < N + 2) :
    qSequence (trial N) k = 1 :=
  minimumAt_head _ _ (Nat.add_le_add_right (denseSchedule_head N) 1)
    k hk (by omega)

theorem trial_error_le (N : ℕ) :
    ‖qOne - trial N‖ ^ 2 ≤
      2 + 2 * stageEnergy denseSchedule 0 + (8 / zetaTwo) * predictionBudget N := by
  have hnorm := norm_sub_le qOne (trial N)
  rw [qOne_norm] at hnorm
  have he := dense_energy_le_predictionBudget N
  change ‖trial N‖ ^ 2 ≤ stageEnergy denseSchedule 0 +
    (4 / zetaTwo) * predictionBudget N at he
  have hs : ‖qOne - trial N‖ ^ 2 ≤ (1 + ‖trial N‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have htwo : ‖qOne - trial N‖ ^ 2 ≤ 2 + 2 * ‖trial N‖ ^ 2 := by
    nlinarith [sq_nonneg (‖trial N‖ - 1)]
  calc
    _ ≤ 2 + 2 * ‖trial N‖ ^ 2 := htwo
    _ ≤ 2 + 2 * (stageEnergy denseSchedule 0 +
        (4 / zetaTwo) * predictionBudget N) := by linarith only [he]
    _ = _ := by ring

/-- Conditional research reduction. The displayed arithmetic budget limit is Open. -/
theorem riemannHypothesis_of_subpolynomial_predictionBudget
    (hsub : Tendsto (fun N => Real.log (1 + predictionBudget N) /
      Real.log ((N + 2 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  let E : ℕ → ℝ := fun N =>
    1 + 2 * stageEnergy denseSchedule 0 + (8 / zetaTwo) * predictionBudget N
  let A : ℝ := 2 + 2 * stageEnergy denseSchedule 0 + 8 / zetaTwo
  have he0 : 0 ≤ stageEnergy denseSchedule 0 := sq_nonneg _
  have hc : 0 ≤ 8 / zetaTwo := div_nonneg (by norm_num) zetaTwo_pos.le
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hE : ∀ N, 0 ≤ E N := by
    intro N
    dsimp [E]
    positivity [predictionBudget_nonneg N]
  have hn : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hscaled := relativeLog_tendsto_zero_of_scaled_budget E predictionBudget
    (fun N => ((N + 2 : ℕ) : ℝ)) A hA hE predictionBudget_nonneg hn
    (Eventually.of_forall (fun N => by
      dsimp [A, E]
      nlinarith [predictionBudget_nonneg N,
        mul_nonneg he0 (predictionBudget_nonneg N)])) hsub
  apply riemannHypothesis_of_cofinal_exact_head_subpolynomial
    trial (fun N => N + 2) E hn trial_legal trial_head hE
  · intro N
    have h := trial_error_le N
    dsimp [E]
    linarith
  · exact hscaled

theorem trial_error_le_log (B : ℝ) (hB : 0 ≤ B)
    (hprediction : ∀ i, |nextMismatch i| ≤ B) (N : ℕ) (hN : 1 ≤ N) :
    ‖qOne - trial N‖ ^ 2 ≤
      (2 + 2 * stageEnergy denseSchedule 0 + (8 / zetaTwo) * B ^ 2) +
        ((8 / zetaTwo) * B ^ 2) * Real.log ((N + 2 : ℕ) : ℝ) := by
  have hb := predictionBudget_le_log B hB hprediction N
  have hl : Real.log (N : ℝ) ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
      (by exact_mod_cast (show N ≤ N + 2 by omega))
  have hb' := hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hl) (sq_nonneg B))
  have hm := mul_le_mul_of_nonneg_left hb'
    (show 0 ≤ 8 / zetaTwo from div_nonneg (by norm_num) zetaTwo_pos.le)
  have he := trial_error_le N
  nlinarith

/-- Conditional research reduction: a uniform bound on the actual moving
prediction errors is enough for logarithmic complete energy and hence RH.
The hypothesis is not a fixed-conductor coefficient limit. -/
theorem riemannHypothesis_of_bounded_nextMismatch
    (B : ℝ) (hB : 0 ≤ B) (hprediction : ∀ i, |nextMismatch i| ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_arbitrarily_small_power_cost
  intro a ha c hc cutoff
  let K : ℝ := 2 + 2 * stageEnergy denseSchedule 0 + (8 / zetaTwo) * B ^ 2
  let D : ℝ := (8 / zetaTwo) * B ^ 2
  have hn : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hp : Tendsto (fun N : ℕ => ((N + 2 : ℕ) : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp hn
  have hlog : Tendsto (fun N : ℕ =>
      Real.log ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ) ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp hn
  have hlim : Tendsto (fun N : ℕ =>
      (K + D * Real.log ((N + 2 : ℕ) : ℝ)) / ((N + 2 : ℕ) : ℝ) ^ a)
      atTop (𝓝 0) := by
    have ht := (hp.const_div_atTop K).add (hlog.const_mul D)
    convert ht using 1
    · ext N
      ring
    · simp
  obtain ⟨N, hN, hsmall⟩ := ((eventually_ge_atTop (max cutoff 1)).and
    (hlim.eventually (Iio_mem_nhds hc))).exists
  refine ⟨N + 2, trial N, by omega, by omega, trial_legal N, trial_head N, ?_⟩
  have hpow : 0 < ((N + 2 : ℕ) : ℝ) ^ a :=
    Real.rpow_pos_of_pos (by positivity) _
  have hs := (div_lt_iff₀ hpow).mp hsmall
  exact (trial_error_le_log B hB hprediction N (by omega)).trans_lt hs

end RiemannResearch.RH.QCRTPredictionBudget
