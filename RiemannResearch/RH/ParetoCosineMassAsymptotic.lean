import RiemannResearch.Analysis.NatStepIntegral
import RiemannResearch.Analysis.CosineReciprocalIntegral
import RiemannResearch.RH.ParetoCompressedMellinNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Sharp full-series asymptotic by dominated convergence of its exact
rescaled step realization. Both the complete head and infinite tail are retained. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CompressedMellin

private def scaledCosinePhase (t x : ℝ) : ℝ :=
  t * Real.log (1 + 1 / ((⌊t * x⌋₊ : ℝ) + 1))

private theorem scaledCosinePhase_bounds {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    1 / (x + 2 / t) ≤ scaledCosinePhase t x ∧
      scaledCosinePhase t x ≤ 1 / x := by
  let n : ℝ := (⌊t * x⌋₊ : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hn1 : 0 < n + 1 := by positivity
  have hn2 : 0 < n + 2 := by positivity
  have hfloor : n ≤ t * x := Nat.floor_le (mul_nonneg ht.le hx.le)
  have hceil : t * x < n + 1 := Nat.lt_floor_add_one (t * x)
  have hy : 0 < 1 + 1 / (n + 1) := by positivity
  have hlogU : Real.log (1 + 1 / (n + 1)) ≤ 1 / (n + 1) := by
    have h := Real.log_le_sub_one_of_pos hy
    linarith
  have hlogL : 1 / (n + 2) ≤ Real.log (1 + 1 / (n + 1)) := by
    have h := Real.one_sub_inv_le_log_of_pos hy
    have he : 1 - (1 + 1 / (n + 1))⁻¹ = 1 / (n + 2) := by
      field_simp
      ring
    rwa [he] at h
  change 1 / (x + 2 / t) ≤ t * Real.log (1 + 1 / (n + 1)) ∧
    t * Real.log (1 + 1 / (n + 1)) ≤ 1 / x
  constructor
  · calc
      1 / (x + 2 / t) = t / (t * x + 2) := by field_simp
      _ ≤ t / (n + 2) := div_le_div_of_nonneg_left ht.le hn2 (by linarith)
      _ = t * (1 / (n + 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogL ht.le
  · calc
      _ ≤ t * (1 / (n + 1)) := mul_le_mul_of_nonneg_left hlogU ht.le
      _ = t / (n + 1) := by ring
      _ ≤ 1 / x := by
        rw [div_le_div_iff₀ hn1 hx]
        simpa using hceil.le

private theorem scaledCosinePhase_nonneg {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    0 ≤ scaledCosinePhase t x := by
  apply mul_nonneg ht
  apply Real.log_nonneg
  have h : 0 ≤ 1 / ((⌊t * x⌋₊ : ℝ) + 1) := by positivity
  linarith

private theorem scaledCosinePhase_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t : ℝ => scaledCosinePhase t x) atTop (𝓝 (1 / x)) := by
  have hlow : Tendsto (fun t : ℝ => 1 / (x + 2 / t)) atTop (𝓝 (1 / x)) := by
    have hi : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hm : Tendsto (fun t : ℝ => x + 2 * t⁻¹) atTop (𝓝 (x + 2 * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hi)
    have h := hm.inv₀ (by simpa using (ne_of_gt hx))
    simpa [div_eq_mul_inv] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (scaledCosinePhase_bounds ht hx).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (scaledCosinePhase_bounds ht hx).2

private def scaledCosineStep (t x : ℝ) : ℝ := cosineDeficit t ⌊t * x⌋₊

private theorem scaledCosineStep_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t : ℝ => scaledCosineStep t x) atTop (𝓝 (1 - Real.cos (1 / x))) := by
  exact tendsto_const_nhds.sub
    ((Real.continuous_cos.tendsto _).comp (scaledCosinePhase_tendsto hx))

private theorem scaledCosineStep_bound {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ‖scaledCosineStep t x‖ ≤ 4 * (1 + x ^ 2)⁻¹ := by
  change ‖cosineDeficit t ⌊t * x⌋₊‖ ≤ 4 * (1 + x ^ 2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (cosineDeficit_nonneg t ⌊t * x⌋₊)]
  have htwo : scaledCosineStep t x ≤ 2 := cosineDeficit_le_two t _
  have hp := scaledCosinePhase_bounds ht hx
  have hp0 := scaledCosinePhase_nonneg ht.le x
  have hq := one_sub_cos_le_half_square (scaledCosinePhase t x)
  have hsq : (scaledCosinePhase t x) ^ 2 ≤ (1 / x) ^ 2 :=
    (sq_le_sq₀ hp0 (by positivity)).mpr hp.2
  have hquad : scaledCosineStep t x ≤ 1 / (2 * x ^ 2) := by
    change 1 - Real.cos (scaledCosinePhase t x) ≤ _
    have he : (1 / x) ^ 2 / 2 = 1 / (2 * x ^ 2) := by ring
    rw [← he]
    linarith
  have hd : 0 < 1 + x ^ 2 := by positivity
  by_cases hs : x ^ 2 ≤ 1
  · have hc : (2 : ℝ) ≤ 4 / (1 + x ^ 2) := by
      rw [le_div_iff₀ hd]
      linarith
    simpa only [div_eq_mul_inv, scaledCosineStep] using! htwo.trans hc
  · have hc : 1 / (2 * x ^ 2) ≤ 4 / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) hd]
      linarith
    simpa only [div_eq_mul_inv, scaledCosineStep] using! hquad.trans hc

private theorem integral_scaledCosineStep (t : ℝ) (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), scaledCosineStep t x) = (∑' n, cosineDeficit t n) / t :=
  RiemannResearch.Analysis.integral_scaled_natStep_Ioi
    (cosineDeficit t) (cosineDeficit_summable t) t ht

private theorem integral_scaledCosineStep_tendsto :
    Tendsto (fun t : ℝ => ∫ x in Ioi (0 : ℝ), scaledCosineStep t x)
      atTop (𝓝 (Real.pi / 2)) := by
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable (scaledCosineStep t)
      (volume.restrict (Ioi 0)) := by
    intro t
    exact ((measurable_of_countable (cosineDeficit t)).comp
      (Nat.measurable_floor.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  have hlim : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0),
      Tendsto (fun t : ℝ => scaledCosineStep t x) atTop
        (𝓝 (1 - Real.cos (1 / x))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact scaledCosineStep_tendsto (show 0 < x from hx)
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => 4 * (1 + x ^ 2)⁻¹)
    (Filter.Eventually.of_forall hmeas)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact scaledCosineStep_bound ht (show 0 < x from hx))
    ((integrable_inv_one_add_sq.const_mul 4).restrict) hlim
  simpa only [RiemannResearch.Analysis.integral_one_sub_cos_inv_Ioi] using h

/-- The exact sharp asymptotic of the complete original logarithmic cosine series. -/
theorem cosineMassAsymptotic : CosineMassAsymptotic := by
  have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have h : Tendsto
      (fun t : ℝ => 1 / t + 2 * ∫ x in Ioi (0 : ℝ), scaledCosineStep t x)
      atTop (𝓝 (0 + 2 * (Real.pi / 2))) :=
    hi.add (tendsto_const_nhds.mul integral_scaledCosineStep_tendsto)
  have he : (fun t : ℝ => 1 / t + 2 * ∫ x in Ioi (0 : ℝ), scaledCosineStep t x) =ᶠ[atTop]
      (fun t : ℝ => cosineMass t / t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [integral_scaledCosineStep t ht]
    unfold cosineMass
    ring
  simpa [CosineMassAsymptotic, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] using! h.congr' he

end RiemannResearch.RH.Pareto.CompressedMellin
