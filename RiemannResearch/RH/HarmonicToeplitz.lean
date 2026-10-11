import RiemannResearch.RH.CriticalMellinCellAsymptotics
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Harmonic Toeplitz convergence

Source: user-provided critical Mellin mixture argument, 21 September 2026.
The harmonic normalization follows from Mathlib's Euler--Mascheroni limit;
weighted Toeplitz convergence follows from its little-o summation theorem.
-/

noncomputable section
set_option autoImplicit false
open Filter Asymptotics
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

def realHarmonicSum (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)

theorem realHarmonicSum_eq (N : ℕ) : realHarmonicSum N = (harmonic N : ℝ) := by
  simp [realHarmonicSum, harmonic, one_div]

theorem realHarmonicSum_nonneg (N : ℕ) : 0 ≤ realHarmonicSum N := by
  apply Finset.sum_nonneg
  intro n hn
  positivity

theorem logarithm_succ_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  exact tendsto_atTop.mpr (fun b => by
    have hb : ∀ᶠ N : ℕ in atTop, b ≤ (N : ℝ) :=
      (tendsto_atTop.mp tendsto_natCast_atTop_atTop) b
    filter_upwards [hb] with N hN
    linarith)

theorem logarithm_succ_le_realHarmonicSum (N : ℕ) :
    Real.log ((N : ℝ) + 1) ≤ realHarmonicSum N := by
  rw [realHarmonicSum_eq]
  simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N

theorem realHarmonicSum_tendsto_atTop : Tendsto realHarmonicSum atTop atTop :=
  tendsto_atTop_mono logarithm_succ_le_realHarmonicSum logarithm_succ_tendsto_atTop

theorem realHarmonicSum_div_log_tendsto :
    Tendsto (fun N => realHarmonicSum N / Real.log ((N : ℝ) + 1)) atTop (𝓝 1) := by
  have hd : Tendsto (fun N => realHarmonicSum N - Real.log ((N : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [realHarmonicSum_eq] using Real.tendsto_harmonic_sub_log_add_one
  have hh := (hd.div_atTop logarithm_succ_tendsto_atTop).add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hh' : Tendsto (fun N =>
      (realHarmonicSum N - Real.log ((N : ℝ) + 1)) / Real.log ((N : ℝ) + 1) + 1)
      atTop (𝓝 1) := by simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : 0 < Real.log ((N : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  field_simp [hn.ne']
  ring

theorem harmonic_diagonal_tendsto :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, (1 : ℂ) / ((n : ℂ) + 1)) /
        (Real.log ((N : ℝ) + 1) : ℂ)) atTop (𝓝 1) := by
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
    realHarmonicSum_div_log_tendsto
  simpa [Function.comp_def, realHarmonicSum] using hh

/-- Harmonic weighted Toeplitz lemma for actual complex sequences. -/
theorem harmonic_toeplitz_zero (u : ℕ → ℂ) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, u n / ((n : ℂ) + 1)) /
        (Real.log ((N : ℝ) + 1) : ℂ)) atTop (𝓝 0) := by
  have hsmall : (fun n : ℕ => u n / ((n : ℂ) + 1)) =o[atTop]
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    apply isLittleO_iff.mpr
    intro c hc
    have heu : ∀ᶠ n in atTop, ‖u n‖ < c :=
      hu.norm.eventually (gt_mem_nhds (by simpa using hc))
    filter_upwards [heu] with n hn
    have hx : 0 < (n : ℝ) + 1 := by positivity
    have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      have he : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by simp
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    rw [norm_div, hnorm, Real.norm_eq_abs, abs_of_pos (by positivity)]
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hn.le hx.le
  have hsum := hsmall.sum_range
    (show 0 ≤ (fun n : ℕ => 1 / ((n : ℝ) + 1)) from fun n => by positivity)
    realHarmonicSum_tendsto_atTop
  have hsum' : (fun N => ∑ n ∈ Finset.range N, u n / ((n : ℂ) + 1)) =o[atTop]
      (fun N => (realHarmonicSum N : ℂ)) := by
    apply Asymptotics.IsLittleO.of_norm_right
    exact hsum.congr_right (fun N => by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (realHarmonicSum_nonneg N)]
      rfl)
  have hrat : Tendsto (fun N =>
      (realHarmonicSum N : ℂ) / (Real.log ((N : ℝ) + 1) : ℂ)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      realHarmonicSum_div_log_tendsto
  have hh := hsum'.tendsto_div_nhds_zero.mul hrat
  have hh' : Tendsto (fun N =>
      ((∑ n ∈ Finset.range N, u n / ((n : ℂ) + 1)) / (realHarmonicSum N : ℂ)) *
        ((realHarmonicSum N : ℂ) / (Real.log ((N : ℝ) + 1) : ℂ))) atTop (𝓝 0) := by
    simpa using hh
  apply hh'.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hlog : 0 < Real.log ((N : ℝ) + 1) := by
    apply Real.log_pos
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hH : (realHarmonicSum N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hlog (logarithm_succ_le_realHarmonicSum N)).ne'
  field_simp [hH]

end RiemannResearch.RH.Pareto.SpectralObstruction
