/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Probability.DPPContinuousSpectralRigidity

/-! # Lower triangular overlap on a vanishing frequency sequence

The triangle estimate must hold for the covariogram of the actual spectral
multiplier. Even a fixed linear deficit strictly below one suffices.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannResearch.DPPSpectral

/-- A one-sided error less than one times the width forces the exact
right-hand structure-factor slope. -/
theorem structureFactor_rightSlope_of_lower_triangle {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1)
    {h : ℕ → ℝ} (hp : ∀ n, 0 < h n) (hz : Tendsto h atTop (𝓝 0))
    {δ : ℝ} (hδ : δ < 1)
    (htri : ∀ᶠ n in atTop, 1 - (1 + δ) * h n ≤ ∫ t, f t * f (t + h n)) :
    Tendsto (fun u => ENNReal.ofReal (structureFactor f u / u)) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨a, ha⟩ := interval_spectrum_of_small_slope hf hb hm hp hz
    (show 1 + δ < 2 by linarith) (by
      filter_upwards [htri] with n hn
      unfold structureFactor
      linarith only [hn])
  exact structureFactor_rightSlope_of_interval_ae ha

/-- A sequence on which the overlap agrees with the triangle up to little-o
of the width verifies the lower-slope hypothesis of spectral rigidity. -/
theorem structureFactor_liminf_of_triangle_error {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1)
    {h : ℕ → ℝ} (hp : ∀ n, 0 < h n) (hz : Tendsto h atTop (𝓝 0))
    (herr : Tendsto (fun n => ((1 - h n) - ∫ t, f t * f (t + h n)) / h n) atTop (𝓝 0)) :
    liminf (fun u => ENNReal.ofReal (structureFactor f u / u)) (𝓝[>] 0) = 1 := by
  apply (structureFactor_rightSlope_of_lower_triangle hf hb hm hp hz
    (show (1 / 2 : ℝ) < 1 by norm_num) ?_).liminf_eq
  filter_upwards [herr.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
  have hn' := (div_lt_iff₀ (hp n)).mp hn
  linarith only [hn']

/--
info: 'RiemannResearch.DPPSpectral.structureFactor_rightSlope_of_lower_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms structureFactor_rightSlope_of_lower_triangle

/--
info: 'RiemannResearch.DPPSpectral.structureFactor_liminf_of_triangle_error' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms structureFactor_liminf_of_triangle_error

end RiemannResearch.DPPSpectral
