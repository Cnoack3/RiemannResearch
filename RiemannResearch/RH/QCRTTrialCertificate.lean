/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTHeadFirstSource
import RiemannResearch.RH.QCRTOptimizerGrowth
import RiemannResearch.Analysis.FiniteGramTrialCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Actual adjusted conductor trials. Source: the user-provided RH research
handoff of 30 October 2026, Sections 3 and 4. These use the moving optimizer
and complete Q norm, including empty innovation blocks. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCRTTrialCertificate
open ZetaTwoHilbert QCRTInnovationGain QCRTInnovationBlock QCRTMovingPredictionGain
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions QSquarefreeAffineHead
open QCRTHeadFirstSource QCRTPrimeInnovation
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open RiemannResearch.Analysis.OrthogonalObservationHeadFirst

def oldNormal (i : ℕ) : QHilbert :=
  (oldTangent i).starProjection (denseNormal i)

def observation (i : ℕ) (d : addedConductors i) : ℝ :=
  qSequence (blockFamily i d) (i + 2)

def jointFamily (i : ℕ) (d : addedConductors i) : QHilbert :=
  adjustedColumn (blockFamily i d) (oldNormal i) (observation i d) (oldCapacity i)

def jointSource (i : ℕ) (d : addedConductors i) : ℝ :=
  cross (blockFamily i) (minimumAt (denseSchedule i) (i + 1)) d -
    oldMismatch i * observation i d / oldCapacity i

def jointGram (i : ℕ) : Matrix (addedConductors i) (addedConductors i) ℝ :=
  fun d e => gramMatrix (blockFamily i) d e +
    observation i d * observation i e / oldCapacity i

def trialCertificate (i : ℕ) (t : addedConductors i → ℝ) : ℝ :=
  oldMismatch i ^ 2 / oldCapacity i -
    2 * dotProduct t (jointSource i) + dotProduct t ((jointGram i).mulVec t)

theorem innovation_pairing (i : ℕ) (d : addedConductors i) :
    inner ℝ (innovationNormal i) (blockFamily i d) = observation i d := by
  have hx : blockFamily i d ∈ innovationSpace i := by
    rw [← block_span]
    exact Submodule.subset_span ⟨d, rfl⟩
  have ho (u : QHilbert) (hu : u ∈ oldTangent i) :
      inner ℝ (blockFamily i d) u = 0 := by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).mp hx.2 u hu
  rw [real_inner_comm]
  change inner ℝ (blockFamily i d) (innovation (oldTangent i) (denseNormal i)) = _
  rw [innovation_inner _ _ _ ho]
  exact block_observation i d

theorem block_oldNormal_orthogonal (i : ℕ) (d : addedConductors i) :
    inner ℝ (blockFamily i d) (oldNormal i) = 0 := by
  have hx : blockFamily i d ∈ innovationSpace i := by
    rw [← block_span]
    exact Submodule.subset_span ⟨d, rfl⟩
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal _ _).mp hx.2 (oldNormal i)
    ((oldTangent i).starProjection_apply_mem _)

theorem jointFamily_independent (i : ℕ) : LinearIndependent ℝ (jointFamily i) := by
  have he : jointFamily i =
      fun d => headShear (oldNormal i) (innovationNormal i) (oldCapacity i)
        (blockFamily i d) := by
    funext d
    change blockFamily i d - (observation i d / oldCapacity i) • oldNormal i =
      blockFamily i d -
        (inner ℝ (innovationNormal i) (blockFamily i d) / oldCapacity i) • oldNormal i
    rw [innovation_pairing]
  rw [he]
  apply headShear_independent _ (block_independent i)
  exact Submodule.starProjection_inner_eq_zero (denseNormal i) (oldNormal i)
    ((oldTangent i).starProjection_apply_mem _)

theorem jointFamily_gram (i : ℕ) (hK : oldCapacity i ≠ 0) :
    gramMatrix (jointFamily i) = jointGram i := by
  funext d e
  exact adjusted_inner (blockFamily i d) (blockFamily i e) (oldNormal i)
    (observation i d) (observation i e) (oldCapacity i) hK rfl
    (block_oldNormal_orthogonal i d)
    (by simpa only [real_inner_comm] using block_oldNormal_orthogonal i e)

/-- The actual certificate is the actual signed increment plus its exact loss. -/
theorem dense_trial_completion (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (t : addedConductors i → ℝ) :
    trialCertificate i t -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) =
      ‖minimumVector (jointFamily_independent i) (jointSource i) -
        Fintype.linearCombination ℝ (jointFamily i) t‖ ^ 2 := by
  have hc := inverseGram_trial_completion (jointFamily_independent i) (jointSource i) t
  rw [jointFamily_gram i (ne_of_gt (oldCapacity_pos i hi hsf))] at hc
  have ht := dense_headFirst_inverseGram i hi hsf
  change stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
    oldMismatch i ^ 2 / oldCapacity i -
      dotProduct (jointSource i) ((jointGram i)⁻¹.mulVec (jointSource i)) at ht
  unfold trialCertificate
  linarith

theorem dense_step_le_trialCertificate (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (t : addedConductors i → ℝ) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i ≤
      trialCertificate i t := by
  have h := dense_trial_completion i hi hsf t
  nlinarith [sq_nonneg ‖minimumVector (jointFamily_independent i) (jointSource i) -
    Fintype.linearCombination ℝ (jointFamily i) t‖]

/-- A one-direction actual-source gain bound, with all signed cross terms. -/
theorem dense_direction_gain_lower (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (w : addedConductors i → ℝ)
    (hw : 0 < dotProduct w ((jointGram i).mulVec w)) :
    (dotProduct w (jointSource i)) ^ 2 / dotProduct w ((jointGram i).mulVec w) ≤
      oldMismatch i ^ 2 / oldCapacity i -
        (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) := by
  have hg := jointFamily_gram i (ne_of_gt (oldCapacity_pos i hi hsf))
  have hb := inverseGram_direction_lower (jointFamily_independent i) (jointSource i) w
    (by rwa [hg])
  rw [hg] at hb
  have ht := dense_headFirst_inverseGram i hi hsf
  change stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
    oldMismatch i ^ 2 / oldCapacity i -
      dotProduct (jointSource i) ((jointGram i)⁻¹.mulVec (jointSource i)) at ht
  linarith
end RiemannResearch.RH.QCRTTrialCertificate


namespace RiemannResearch.RH.QCRTTrialCertificate
open ZetaTwoHilbert QCRTInnovationBlock QCRTPeriodHeadBalance
open QSquarefreeEnergyTransitions QCRTOptimizerGrowth
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.SubpolynomialWindow

/-- The initial step is exact; dependent sites keep their full negative gain. -/
def fullCertificate (t : ∀ i, addedConductors i → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then stageEnergy denseSchedule 1 - stageEnergy denseSchedule 0
  else if Squarefree (i + 2) then trialCertificate i (t i)
  else -periodGain denseSchedule i

def fullLoss (t : ∀ i, addedConductors i → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0
  else if Squarefree (i + 2) then
    ‖minimumVector (jointFamily_independent i) (jointSource i) -
      Fintype.linearCombination ℝ (jointFamily i) (t i)‖ ^ 2
  else 0

theorem fullLoss_nonneg (t : ∀ i, addedConductors i → ℝ) (i : ℕ) :
    0 ≤ fullLoss t i := by
  unfold fullLoss
  split_ifs <;> positivity

theorem dense_full_completion (t : ∀ i, addedConductors i → ℝ) (i : ℕ) :
    fullCertificate t i -
      (stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i) =
      fullLoss t i := by
  by_cases hi : i = 0
  · simp [fullCertificate, fullLoss, hi]
  · by_cases hsf : Squarefree (i + 2)
    · simpa only [fullCertificate, fullLoss, if_neg hi, if_pos hsf] using
        dense_trial_completion i (Nat.pos_of_ne_zero hi) hsf (t i)
    · have ht := stageEnergy_step denseSchedule denseSchedule_monotone denseSchedule_head i
      rw [headCost_eq_zero_of_nonsquarefree denseSchedule i (denseSchedule_head (i + 1)) hsf]
        at ht
      simp only [fullCertificate, fullLoss, if_neg hi, if_neg hsf]
      linarith

/-- Exact cumulative accounting preserves both signed certificates and all losses. -/
theorem dense_trial_telescope (t : ∀ i, addedConductors i → ℝ) (N : ℕ) :
    stageEnergy denseSchedule N =
      stageEnergy denseSchedule 0 +
        (∑ i ∈ Finset.range N, fullCertificate t i) -
        ∑ i ∈ Finset.range N, fullLoss t i := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h := dense_full_completion t N
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

theorem dense_energy_le_trial_sum (t : ∀ i, addedConductors i → ℝ) (N : ℕ) :
    stageEnergy denseSchedule N ≤
      stageEnergy denseSchedule 0 + ∑ i ∈ Finset.range N, fullCertificate t i := by
  rw [dense_trial_telescope t N]
  exact sub_le_self _ (Finset.sum_nonneg (fun i _ => fullLoss_nonneg t i))

/-- Conditional RH reduction allowing cancellation across stages and only cofinal heads.
The signed arithmetic budget and its physical-head growth remain Open providers. -/
theorem riemannHypothesis_of_cofinal_trial_budget
    (t : ∀ i, addedConductors i → ℝ) (S : ℕ → ℕ)
    (hS : Tendsto S atTop atTop) (B : ℕ → ℝ) (hB : ∀ N, 0 ≤ B N)
    (hbudget : ∀ N, stageEnergy denseSchedule 0 +
      (∑ i ∈ Finset.range (S N), fullCertificate t i) ≤ B N)
    (hlog : Tendsto (fun N => Real.log (1 + B N) /
      Real.log ((S N + 2 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_subpolynomial_stageEnergy S hS
  apply relativeLog_tendsto_zero_of_scaled_budget
    (fun N => stageEnergy denseSchedule (S N)) B
    (fun N => ((S N + 2 : ℕ) : ℝ)) 1 (by norm_num)
    (fun _ => sq_nonneg _) hB
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 2).comp hS))
  · exact Eventually.of_forall (fun N => by
      have he := (dense_energy_le_trial_sum t (S N)).trans (hbudget N)
      linarith)
  · exact hlog
end RiemannResearch.RH.QCRTTrialCertificate
