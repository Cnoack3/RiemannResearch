/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanRHBridge
import RiemannResearch.Probability.ConditionalIIDSampleMean

/-!
# The actual conditional-iid sampling criterion for RH

All sample coordinates live on the already constructed common probability
space and share one latent endpoint. Each witness is one deterministic legal
arithmetic function. The theorem does not construct approximating witnesses:
it proves an implication from the explicitly stated approximation hypothesis.
-/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Probability.ConditionalIID

/-- The square error of a genuine sample mean in the shared-environment model. -/
def conditionalIIDError (g : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∫ ω : Omega, (1 - pathAverage g r ω.2) ^ 2 ∂probability

/-- Expected within-environment variance. -/
def withinVariance (g : ℕ → ℝ) : ℝ :=
  ∫ ω : Omega, variance g (uniformLaw (latentIndex ω)) ∂probability

theorem withinVariance_nonneg (g : ℕ → ℝ) : 0 ≤ withinVariance g :=
  integral_nonneg (fun _ => variance_nonneg _ _)

theorem conditionalIIDError_nonneg (g : ℕ → ℝ) (r : ℕ) :
    0 ≤ conditionalIIDError g r := integral_nonneg (fun _ => sq_nonneg _)

/-- Boundedness of actual legal witnesses supplies all observation integrability. -/
theorem legal_observation_memLp (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) (i : ℕ) :
    MemLp (fun ω => g (coordinate i ω)) 2 probability := by
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  apply MemLp.of_bound
    ((measurable_of_countable g).comp (coordinate_measurable i)).aestronglyMeasurable B
  exact Filter.Eventually.of_forall (fun ω => by simpa [Real.norm_eq_abs] using hB (coordinate i ω))

/-- The entire conditional-mean contribution survives row averaging. -/
theorem conditionalIIDError_eq (g : ℕ → ℝ) (r : ℕ) (hr : 0 < r)
    (hg : MemLp (fun ω => g (coordinate 0 ω)) 2 probability) :
    conditionalIIDError g r = conditionalMeanError g + withinVariance g / (r : ℝ) := by
  have hm := latent_integral
    (fun k => (1 - cesaro g (k + 1)) ^ 2)
    (conditionalMean_error_integrable g 1 hg)
  have he := average_error g r hr 1 (coordinate_memLp_of_zero g hg)
  change conditionalIIDError g r = _ at he
  change (∫ ω : Omega, (1 - cesaro g (endpoint ω)) ^ 2 ∂probability) =
    conditionalMeanError g at hm
  rw [hm] at he
  exact he

theorem conditionalMeanError_le_conditionalIIDError (g : ℕ → ℝ) (r : ℕ)
    (hr : 0 < r) (hg : MemLp (fun ω => g (coordinate 0 ω)) 2 probability) :
    conditionalMeanError g ≤ conditionalIIDError g r := by
  rw [conditionalIIDError_eq g r hr hg]
  exact le_add_of_nonneg_right (div_nonneg (withinVariance_nonneg g) (Nat.cast_nonneg _))

/-- Increasing a positive sample size cannot increase the expected square error. -/
theorem conditionalIIDError_antitone (g : ℕ → ℝ)
    (hg : MemLp (fun ω => g (coordinate 0 ω)) 2 probability)
    {r t : ℕ} (hr : 0 < r) (hrt : r ≤ t) :
    conditionalIIDError g t ≤ conditionalIIDError g r := by
  rw [conditionalIIDError_eq g t (hr.trans_le hrt) hg,
    conditionalIIDError_eq g r hr hg]
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (withinVariance_nonneg g)
    (by exact_mod_cast hr) (by exact_mod_cast hrt)

/-- The limiting sample error is the conditional-mean error, not automatically zero. -/
theorem conditionalIIDError_tendsto (g : ℕ → ℝ)
    (hg : MemLp (fun ω => g (coordinate 0 ω)) 2 probability) :
    Tendsto (fun r => conditionalIIDError g (r + 1)) atTop (𝓝 (conditionalMeanError g)) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hv : Tendsto (fun r : ℕ => withinVariance g / ((r + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, div_eq_mul_inv] using h.const_mul (withinVariance g)
  simpa only [conditionalIIDError_eq g _ (Nat.succ_pos _) hg, add_zero] using
    tendsto_const_nhds.add hv

/-- One finite deterministic sample size suffices once the conditional mean is accurate. -/
theorem exists_sampleSize_error_lt (g : ℕ → ℝ)
    (hg : MemLp (fun ω => g (coordinate 0 ω)) 2 probability)
    (ε : ℝ) (hε : conditionalMeanError g < ε) :
    ∃ r : ℕ, 0 < r ∧ conditionalIIDError g r < ε := by
  obtain ⟨r, hr⟩ := ((conditionalIIDError_tendsto g hg).eventually (gt_mem_nhds hε)).exists
  exact ⟨r + 1, Nat.succ_pos r, hr⟩

/-- Equivalence of the two approximation predicates, without assuming RH. -/
theorem conditionalMeanApproximation_iff_conditionalIIDApproximation
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    (∀ ε : ℝ, 0 < ε → ∃ g ∈ legalSeedSpan A, conditionalMeanError g < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ g ∈ legalSeedSpan A,
      ∃ r : ℕ, 0 < r ∧ conditionalIIDError g r < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨g, hg, he⟩ := h ε hε
    obtain ⟨r, hr, her⟩ := exists_sampleSize_error_lt g (legal_observation_memLp A hA hg 0) ε he
    exact ⟨g, hg, r, hr, her⟩
  · intro h ε hε
    obtain ⟨g, hg, r, hr, he⟩ := h ε hε
    exact ⟨g, hg, (conditionalMeanError_le_conditionalIIDError g r hr
      (legal_observation_memLp A hA hg 0)).trans_lt he⟩

/-- Sampling approximation implies the actual mathlib Riemann hypothesis. -/
theorem riemannHypothesis_of_conditionalIIDApproximation
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g ∈ legalSeedSpan A,
      ∃ r : ℕ, 0 < r ∧ conditionalIIDError g r < ε) : RiemannHypothesis := by
  apply riemannHypothesis_of_conditionalMeanApproximation A hA
  exact (conditionalMeanApproximation_iff_conditionalIIDApproximation A hA).2 happrox

/-- Sequence form: functions are deterministic legal witnesses and sample sizes may vary. -/
theorem riemannHypothesis_of_conditionalIIDError_tendsto
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ) (r : ℕ → ℕ)
    (hg : ∀ j, g j ∈ legalSeedSpan A) (hr : ∀ j, 0 < r j)
    (hlim : Tendsto (fun j => conditionalIIDError (g j) (r j)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_conditionalIIDApproximation A hA
  intro ε hε
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨g j, hg j, r j, hr j, hj⟩

end RiemannResearch.RH.Pareto
