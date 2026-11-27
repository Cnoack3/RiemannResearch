import RiemannResearch.Probability.ConditionalVarianceError
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Local deletion bounds for the variance conditional on a window centre

A real observation in `[0,1]` of a thinned configuration agrees with a fixed
full-configuration value whenever the local deletion count is zero. Its variance,
together with its squared bias, is bounded by the expected count of deletions.
Averaging over the centres gives a necessary condition on a proposed common
limiting law. The source of randomness in these variances is the thinning at a
fixed centre. The variance due to the choice of centre is a different quantity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RiemannResearch.Probability.DPP.DeletionVariance

variable {Ω A ι : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

/-- A bounded observation which agrees off the deletion event has total
mean-square error at most the expected number of deleted points. -/
theorem variance_add_bias_sq_le_deletions (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (c : ℝ) (D : Ω → ℕ) (hm : AEMeasurable X μ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1)
    (heq : ∀ᵐ ω ∂μ, D ω = 0 → X ω = c)
    (hd : Integrable (fun ω => (D ω : ℝ)) μ) :
    (c - ∫ ω, X ω ∂μ) ^ 2 + variance X μ ≤ ∫ ω, (D ω : ℝ) ∂μ := by
  have hLp : MemLp X 2 μ := memLp_of_bounded hb hm.aestronglyMeasurable 2
  rw [← integral_const_sub_sq_eq_bias_sq_add_variance hLp c]
  apply integral_mono_of_nonneg (ae_of_all μ fun ω => sq_nonneg _) hd
  filter_upwards [hb, heq] with ω hx he
  change (c - X ω) ^ 2 ≤ (D ω : ℝ)
  by_cases hz : D ω = 0
  · simp [hz, he hz]
  · have hD : 1 ≤ D ω := Nat.one_le_iff_ne_zero.mpr hz
    have hD' : (1 : ℝ) ≤ (D ω : ℝ) := by exact_mod_cast hD
    have h₁ : 0 ≤ 1 - (c - X ω) := by linarith [hc.2, hx.1]
    have h₂ : 0 ≤ 1 + (c - X ω) := by linarith [hc.1, hx.2]
    nlinarith [mul_nonneg h₁ h₂]

/-- Any point process whose expected count on a window is strictly between
zero and one has a bounded local observable of strictly positive variance:
whether the window is occupied. Only its first count moment is required. -/
theorem occupancy_variance_pos_of_mean_count (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hm : Measurable N) (hint : Integrable (fun ω => (N ω : ℝ)) μ)
    (hpos : 0 < ∫ ω, (N ω : ℝ) ∂μ) (hlt : (∫ ω, (N ω : ℝ) ∂μ) < 1) :
    0 < variance (fun ω => if N ω = 0 then (0 : ℝ) else 1) μ := by
  let F : Ω → ℝ := fun ω => if N ω = 0 then 0 else 1
  have hmeas : Measurable F :=
    Measurable.ite (hm (measurableSet_singleton 0)) measurable_const measurable_const
  have hb (ω : Ω) : F ω ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : N ω = 0 <;> simp [F, h]
  have hLp : MemLp F 2 μ := memLp_of_bounded (ae_of_all μ hb) hmeas.aestronglyMeasurable 2
  have hnonneg : 0 ≤ ∫ ω, F ω ∂μ := integral_nonneg fun ω => (hb ω).1
  have hFpos : 0 < ∫ ω, F ω ∂μ := by
    by_contra! hn
    have hF : F =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all μ fun ω => (hb ω).1) (hLp.integrable one_le_two)).mp (le_antisymm hn hnonneg)
    have hz : (fun ω => (N ω : ℝ)) =ᵐ[μ] 0 := by
      filter_upwards [hF] with ω hω
      change F ω = 0 at hω
      by_cases h : N ω = 0
      · simp [h]
      · simp [F, h] at hω
    have hzero : (∫ ω, (N ω : ℝ) ∂μ) = 0 := (integral_congr_ae hz).trans (integral_zero _ _)
    linarith
  have hFle : (∫ ω, F ω ∂μ) ≤ ∫ ω, (N ω : ℝ) ∂μ := by
    apply integral_mono (hLp.integrable one_le_two) hint
    intro ω
    by_cases h : N ω = 0
    · simp [F, h]
    · simpa [F, h] using (show (1 : ℝ) ≤ (N ω : ℝ) by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h))
  have hsq : F ^ 2 = F := by
    ext ω
    by_cases h : N ω = 0 <;> simp [F, h]
  change 0 < variance F μ
  rw [variance_eq_sub hLp, hsq]
  nlinarith [mul_pos hFpos (sub_pos.mpr (hFle.trans_lt hlt))]

/-- At moving heights and with varying laws for centres and thinnings, vanishing
mean local deletion forces vanishing averaged conditional variance. -/
theorem averaged_variance_tendsto_zero_of_deletions {l : Filter ι}
    (ν : ι → Measure A) (μ : ι → A → Measure Ω) [∀ k a, IsProbabilityMeasure (μ k a)]
    (X : ι → A → Ω → ℝ) (c : ι → A → ℝ) (D : ι → A → Ω → ℕ)
    (hm : ∀ k a, AEMeasurable (X k a) (μ k a))
    (hc : ∀ k a, c k a ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ k a, ∀ᵐ ω ∂μ k a, X k a ω ∈ Set.Icc (0 : ℝ) 1)
    (heq : ∀ k a, ∀ᵐ ω ∂μ k a, D k a ω = 0 → X k a ω = c k a)
    (hd : ∀ k a, Integrable (fun ω => (D k a ω : ℝ)) (μ k a))
    (hvint : ∀ k, Integrable (fun a => variance (X k a) (μ k a)) (ν k))
    (havg : ∀ k, Integrable (fun a => ∫ ω, (D k a ω : ℝ) ∂μ k a) (ν k))
    (hlim : Tendsto (fun k => ∫ a, ∫ ω, (D k a ω : ℝ) ∂μ k a ∂ν k) l (𝓝 0)) :
    Tendsto (fun k => ∫ a, variance (X k a) (μ k a) ∂ν k) l (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg fun a => variance_nonneg _ _) _ hlim
  intro k
  apply integral_mono (hvint k) (havg k)
  intro a
  have h := variance_add_bias_sq_le_deletions (μ k a) (X k a) (c k a) (D k a)
    (hm k a) (hc k a) (hb k a) (heq k a) (hd k a)
  exact (le_add_of_nonneg_left (sq_nonneg _)).trans h

/-- If the mean conditional variance vanishes, a common limiting pair of first
and second moments must have zero variance. Convergence of the squared
conditional means is essential here. -/
theorem second_moment_eq_sq_of_common_limit {l : Filter ι} [NeBot l]
    (ν : ι → Measure A) (μ : ι → A → Measure Ω) [∀ k a, IsProbabilityMeasure (μ k a)]
    (X : ι → A → Ω → ℝ) (m s : ℝ)
    (hX : ∀ k a, MemLp (X k a) 2 (μ k a))
    (hint₂ : ∀ k, Integrable (fun a => ∫ ω, (X k a ω) ^ 2 ∂μ k a) (ν k))
    (hint₁ : ∀ k, Integrable (fun a => (∫ ω, X k a ω ∂μ k a) ^ 2) (ν k))
    (hm₂ : Tendsto (fun k => ∫ a, ∫ ω, (X k a ω) ^ 2 ∂μ k a ∂ν k) l (𝓝 s))
    (hm₁ : Tendsto (fun k => ∫ a, (∫ ω, X k a ω ∂μ k a) ^ 2 ∂ν k) l (𝓝 (m ^ 2)))
    (hv : Tendsto (fun k => ∫ a, variance (X k a) (μ k a) ∂ν k) l (𝓝 0)) :
    s = m ^ 2 := by
  have hiden (k : ι) : (∫ a, variance (X k a) (μ k a) ∂ν k) =
      (∫ a, ∫ ω, (X k a ω) ^ 2 ∂μ k a ∂ν k) -
        ∫ a, (∫ ω, X k a ω ∂μ k a) ^ 2 ∂ν k := by
    simp_rw [variance_eq_sub (hX k _), Pi.pow_apply]
    exact integral_sub (hint₂ k) (hint₁ k)
  have h := hm₂.sub hm₁
  simp only [← hiden] at h
  exact sub_eq_zero.mp (tendsto_nhds_unique h hv)

end RiemannResearch.Probability.DPP.DeletionVariance
