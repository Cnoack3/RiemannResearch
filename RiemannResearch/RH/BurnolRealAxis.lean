import RiemannResearch.RH.BurnolCayleyJensen
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Real-axis normalization at the exceptional Cayley boundary point

Burnol excludes an exponential inner factor using the behavior on the positive
real axis; see https://arxiv.org/abs/math/9910055, Section 2. We prove the
actual limits from Mathlib's Dirichlet-series limit theorem. These limits do
not by themselves supply the Hardy factorization or Jensen boundary theorem.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Burnol

/-- The zeta function tends to one on the positive real axis, unconditionally. -/
theorem riemannZeta_real_tendsto_one :
    Tendsto (fun σ : ℝ => riemannZeta (σ : ℂ)) atTop (𝓝 1) := by
  have h : Tendsto (fun σ : ℝ => LSeries (1 : ℕ → ℂ) (σ : ℂ)) atTop (𝓝 1) := by
    simpa using (LSeries.tendsto_atTop (f := (1 : ℕ → ℂ))
      (by rw [LSeries.abscissaOfAbsConv_one]; exact EReal.coe_lt_top 1))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  exact LSeries_one_eq_riemannZeta (by simpa using hσ)

/-- Real-axis points approach the exceptional disk boundary point `1`. -/
theorem diskCoordinate_real_tendsto_one :
    Tendsto (fun σ : ℝ => diskCoordinate (σ : ℂ)) atTop (𝓝 1) := by
  have hr : Tendsto (fun σ : ℝ => 1 - σ⁻¹) atTop (𝓝 (1 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hconst.sub tendsto_inv_atTop_zero
  have hc : Tendsto (fun σ : ℝ => ((1 - σ⁻¹ : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hr
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  have hn : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  push_cast
  unfold diskCoordinate
  field_simp [hn]

/-- The pole-removed normalized zeta ratio has real-axis limit exactly one. -/
theorem regularZetaRatio_real_tendsto_one :
    Tendsto (fun σ : ℝ => regularZetaRatio (σ : ℂ)) atTop (𝓝 1) := by
  have h := diskCoordinate_real_tendsto_one.mul riemannZeta_real_tendsto_one
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  have hp : 0 < (σ : ℂ).re := by simpa using (show 0 < σ by linarith)
  have h1 : (σ : ℂ) ≠ 1 := by
    intro hh
    have := congrArg Complex.re hh
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  exact (regularZetaRatio_eq hp h1).symm

/-- Radial normalization at the exceptional point, parametrized by the
positive half-line. The disk coordinate equals `1 - 1/σ` for `σ ≠ 0`. -/
theorem diskZeta_real_radial_tendsto_one :
    Tendsto (fun σ : ℝ => diskZeta (diskCoordinate (σ : ℂ))) atTop (𝓝 1) := by
  apply regularZetaRatio_real_tendsto_one.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  have hn : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  rw [diskZeta, cayley_diskCoordinate hn]

/-- The real-axis logarithmic modulus has no nonzero limiting constant. -/
theorem regularZetaRatio_real_log_norm_tendsto_zero :
    Tendsto (fun σ : ℝ => Real.log ‖regularZetaRatio (σ : ℂ)‖) atTop (𝓝 0) := by
  have hn : Tendsto (fun σ : ℝ => ‖regularZetaRatio (σ : ℂ)‖) atTop (𝓝 1) := by
    simpa using regularZetaRatio_real_tendsto_one.norm
  simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hn

end RiemannResearch.RH.Burnol
