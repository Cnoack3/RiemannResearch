import RiemannResearch.RH.DyadicBoundaryParseval
import RiemannResearch.RH.ThresholdRiemannHypothesis
import Mathlib.Topology.Sequences

/-!
# Exact boundary-energy criterion for legal recovery

Source: user-provided DyadicGramPrefixVerification20260910(1).md,
September 10, 2026, continuation toward actual legal approximation.
The complete Parseval identity is specialized to converging witness sequences.
The three scalar energy limits are proved equivalent to physical convergence.
Existence of legal witnesses satisfying them remains an open arithmetic input.
-/

namespace RiemannResearch.RH.Pareto
open Filter
open scoped BigOperators Topology
noncomputable section

/-- The full convergent sum of squared physical boundary pairings. -/
def dyadicBoundaryDetailEnergy (f : ThresholdHilbert) : ℝ :=
  ∑' n : ℕ, 4 * (inner ℝ (dyadicQuotientProjection
    (dyadicStepBoundary (n+1) (by positivity))) f)^2

theorem dyadicBoundaryDetailEnergy_nonneg (f : ThresholdHilbert) :
    0 ≤ dyadicBoundaryDetailEnergy f := by
  apply tsum_nonneg
  intro n
  positivity

/-- Exact scalar criterion; no finite prefix replaces the infinite boundary sum. -/
theorem dyadicBoundary_tendsto_one_iff (F : ℕ → ThresholdHilbert) :
    Tendsto F atTop (𝓝 hilbertOne) ↔
      Tendsto (fun n => (1 - inner ℝ hilbertOne (F n))^2) atTop (𝓝 0) ∧
      Tendsto (fun n => dyadicBoundaryDetailEnergy (F n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖F n - dyadicQuotientProjection (F n)‖^2) atTop (𝓝 0) := by
  have he (n : ℕ) : ‖hilbertOne - F n‖^2 =
      (1 - inner ℝ hilbertOne (F n))^2 + dyadicBoundaryDetailEnergy (F n) +
      ‖F n - dyadicQuotientProjection (F n)‖^2 :=
    dyadicBoundary_full_error_sq (F n)
  constructor
  · intro hF
    have herror : Tendsto (fun n => ‖hilbertOne - F n‖^2) atTop (𝓝 0) := by
      simpa only [norm_sub_rev, zero_pow (by norm_num : 2 ≠ 0)] using
        (tendsto_iff_norm_sub_tendsto_zero.mp hF).pow 2
    refine ⟨?_, ?_, ?_⟩
    · apply squeeze_zero (fun n => sq_nonneg _) _ herror
      intro n
      have hb := dyadicBoundaryDetailEnergy_nonneg (F n)
      have hc := sq_nonneg ‖F n - dyadicQuotientProjection (F n)‖
      linarith [he n]
    · apply squeeze_zero (fun n => dyadicBoundaryDetailEnergy_nonneg (F n)) _ herror
      intro n
      have hm := sq_nonneg (1 - inner ℝ hilbertOne (F n))
      have hc := sq_nonneg ‖F n - dyadicQuotientProjection (F n)‖
      linarith [he n]
    · apply squeeze_zero (fun n => sq_nonneg _) _ herror
      intro n
      have hm := sq_nonneg (1 - inner ℝ hilbertOne (F n))
      have hb := dyadicBoundaryDetailEnergy_nonneg (F n)
      linarith [he n]
  · rintro ⟨hm, hb, hc⟩
    have herror : Tendsto (fun n => ‖hilbertOne - F n‖^2) atTop (𝓝 0) := by
      simpa only [he, add_zero] using (hm.add hb).add hc
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hs := herror.eventually (gt_mem_nhds (sq_pos_of_pos hε))
    filter_upwards [hs] with n hn
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [norm_nonneg (hilbertOne - F n)]

/-- This is a witness-existence target with every energy explicit. -/
def HasDyadicBoundaryLegalRecovery (A : Set ℕ) : Prop :=
  ∃ F : ℕ → ThresholdHilbert, (∀ n, F n ∈ hilbertLegalSubspace A) ∧
    Tendsto (fun n => (1 - inner ℝ hilbertOne (F n))^2) atTop (𝓝 0) ∧
    Tendsto (fun n => dyadicBoundaryDetailEnergy (F n)) atTop (𝓝 0) ∧
    Tendsto (fun n => ‖F n - dyadicQuotientProjection (F n)‖^2) atTop (𝓝 0)

/-- The scalar witness criterion is exactly the original legal closure target. -/
theorem dyadicBoundaryLegalRecovery_iff_legalClosure (A : Set ℕ) :
    HasDyadicBoundaryLegalRecovery A ↔ hilbertOne ∈ hilbertLegalClosure A := by
  constructor
  · rintro ⟨F, hlegal, hm, hb, hc⟩
    change hilbertOne ∈ closure (hilbertLegalSubspace A : Set ThresholdHilbert)
    exact mem_closure_iff_seq_limit.mpr
      ⟨F, hlegal, (dyadicBoundary_tendsto_one_iff F).mpr ⟨hm, hb, hc⟩⟩
  · intro hmem
    change hilbertOne ∈ closure (hilbertLegalSubspace A : Set ThresholdHilbert) at hmem
    obtain ⟨F, hlegal, hF⟩ := mem_closure_iff_seq_limit.mp hmem
    exact ⟨F, hlegal, (dyadicBoundary_tendsto_one_iff F).mp hF⟩

/-- The actual RH implication; a provider of the legal scalar limits is required. -/
theorem riemannHypothesis_of_dyadicBoundaryLegalRecovery
    (h : HasDyadicBoundaryLegalRecovery {2, 3}) : RiemannHypothesis :=
  riemannHypothesis_of_twoSeed_closure
    ((dyadicBoundaryLegalRecovery_iff_legalClosure {2, 3}).mp h)

/-- For exactly mean-one finite legal witnesses only the two full energies remain. -/
theorem riemannHypothesis_of_dyadicBoundary_meanOne_recovery
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace {2, 3})
    (hmean : ∀ n, inner ℝ hilbertOne (F n) = 1)
    (hboundary : Tendsto (fun n => dyadicBoundaryDetailEnergy (F n)) atTop (𝓝 0))
    (hcomplement : Tendsto (fun n => ‖F n - dyadicQuotientProjection (F n)‖^2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicBoundaryLegalRecovery
  refine ⟨F, hlegal, ?_, hboundary, hcomplement⟩
  simpa only [hmean, sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end
end RiemannResearch.RH.Pareto
