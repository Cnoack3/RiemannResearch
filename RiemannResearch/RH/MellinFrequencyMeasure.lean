import RiemannResearch.RH.MellinModeOrthonormality

/-!
# The actual Mellin reference measure and Gram identity

Source: user-requested Mellin DPP construction, September 20, 2026.
Angular frequency `t` uses the measure `dt/(2π)`. The exact change of
variables in `MellinModeOrthonormality` supplies this Gram identity.
Square-integrability is a conclusion, not a provider hypothesis.
-/

noncomputable section
open MeasureTheory

namespace RiemannResearch.RH.Pareto.MellinFrequency

/-- Angular-frequency Lebesgue measure with the Mellin--Plancherel normalization. -/
def frequencyMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume

instance frequencyMeasure_sigmaFinite : SigmaFinite frequencyMeasure := by
  change SigmaFinite (Real.toNNReal (1 / (2 * Real.pi)) • (volume : Measure ℝ))
  infer_instance

theorem frequencyMeasure_gram (i j : ℕ) :
    (∫ t, star (modeFeature i t) * modeFeature j t ∂frequencyMeasure) =
      if i = j then (1 : ℂ) else 0 := by
  rw [frequencyMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 * Real.pi))]
  exact modeFeature_angular_gram i j

/-- The nonzero diagonal integral proves actual integrability; it cannot be
an artifact of Lean's value zero for a divergent Bochner integral. -/
theorem modeFeature_self_product_integrable (j : ℕ) :
    Integrable (fun t => star (modeFeature j t) * modeFeature j t) frequencyMeasure := by
  by_contra hn
  have h := frequencyMeasure_gram j j
  rw [integral_undef hn] at h
  simp at h

theorem modeFeature_memLp (j : ℕ) : MemLp (modeFeature j) 2 frequencyMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (modeFeature_continuous j).measurable.aestronglyMeasurable).mpr
  convert (modeFeature_self_product_integrable j).re using 1
  funext t
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re]

theorem modeFeature_cross_product_integrable (i j : ℕ) :
    Integrable (fun t => star (modeFeature i t) * modeFeature j t) frequencyMeasure := by
  have h := L2.integrable_inner (𝕜 := ℂ)
    ((modeFeature_memLp i).toLp (modeFeature i))
    ((modeFeature_memLp j).toLp (modeFeature j))
  apply h.congr
  filter_upwards [(modeFeature_memLp i).coeFn_toLp,
    (modeFeature_memLp j).coeFn_toLp] with t hi hj
  rw [hi, hj]
  simp [RCLike.inner_apply, mul_comm]

end RiemannResearch.RH.Pareto.MellinFrequency
