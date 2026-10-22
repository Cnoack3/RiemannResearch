import RiemannResearch.Analysis.WeightedMellinHardy
import Mathlib.Tactic.FunProp

/-!
# Strong L2 boundary traces for finite-energy Mellin transforms

Source: user-requested continuation of
RH_Energy_Holomorphy_Hardy_Implications_2026-09-18.md.
The proof uses dominated convergence for the logarithmic lifts and continuity
of the unitary L2 Fourier transform. It proves convergence along every
sequence of interior real parts tending to the boundary.

The trace is an L2 equivalence class, not the ordinary boundary Mellin
integral (which need not converge), nor arbitrarily assigned boundary values.
These theorems apply to finite-energy Mellin transforms; the representation
of an arbitrary Hardy function is a separate obligation.
-/

set_option autoImplicit false
open MeasureTheory Set Filter FourierTransform
open scoped Topology
noncomputable section
namespace MeasureTheory.WeightedMellin

theorem logLift_continuous_parameter (f : ℝ → ℂ) (t : ℝ) :
    Continuous (fun σ : ℝ => logLift f σ t) := by
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [logLift, indicator_of_mem ht]
    fun_prop
  · simp only [logLift, indicator_of_notMem ht]
    exact continuous_const

theorem logLift_norm_mono (f : ℝ → ℂ) {α σ : ℝ} (hσ : α ≤ σ) (t : ℝ) :
    ‖logLift f σ t‖ ≤ ‖logLift f α t‖ := by
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [logLift, indicator_of_mem ht, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have : 0 < t := ht
    nlinarith
  · simp [logLift, ht]

theorem logLift_sub_norm_sq_le (f : ℝ → ℂ) {α σ : ℝ} (hσ : α ≤ σ) (t : ℝ) :
    ‖logLift f σ t - logLift f α t‖ ^ 2 ≤ 4 * ‖logLift f α t‖ ^ 2 := by
  have hn := norm_sub_le (logLift f σ t) (logLift f α t)
  have hm := logLift_norm_mono f hσ t
  have hb : ‖logLift f σ t - logLift f α t‖ ≤ 2 * ‖logLift f α t‖ := by linarith
  have hh := pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith

theorem logLift_sub_energy_tendsto {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {σ : ℕ → ℝ} (hσ : ∀ n, s / 2 ≤ σ n) (ht : Tendsto σ atTop (𝓝 (s / 2))) :
    Tendsto (fun n => ∫ t : ℝ, ‖logLift f (σ n) t - logLift f (s / 2) t‖ ^ 2)
      atTop (𝓝 0) := by
  have hl := logLift_memLp hf (σ := s / 2) (by linarith)
  have hi := (memLp_two_iff_integrable_sq_norm hl.1).mp hl
  have H := tendsto_integral_of_dominated_convergence
    (fun t : ℝ => 4 * ‖logLift f (s / 2) t‖ ^ 2)
    (F := fun n t => ‖logLift f (σ n) t - logLift f (s / 2) t‖ ^ 2)
    (f := fun _ : ℝ => (0 : ℝ))
    (fun n => (((logLift_measurable hf.1 (σ n)).sub
      (logLift_measurable hf.1 (s / 2))).norm.pow_const 2).aestronglyMeasurable)
    (hi.const_mul 4) ?_ ?_
  · simpa using H
  · intro n
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact logLift_sub_norm_sq_le f (hσ n) t
  · filter_upwards [] with t
    have hp := ((logLift_continuous_parameter f t).continuousAt.tendsto.comp ht).sub_const
      (logLift f (s / 2) t)
    simpa using hp.norm.pow 2

private theorem lp_norm_sq_integral (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖u‖ ^ 2 = ∫ t : ℝ, ‖u t‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h

def liftLp {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    (σ : ℝ) (hσ : s / 2 ≤ σ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (logLift_memLp hf (by linarith)).toLp (logLift f σ)

def boundaryTrace {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s) :
    Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (liftLp hf (s / 2) le_rfl)

theorem liftLp_sub_norm_sq {f : ℝ → ℂ} {s σ : ℝ} (hf : FiniteEnergy f s)
    (hσ : s / 2 ≤ σ) :
    ‖liftLp hf σ hσ - liftLp hf (s / 2) le_rfl‖ ^ 2 =
      ∫ t : ℝ, ‖logLift f σ t - logLift f (s / 2) t‖ ^ 2 := by
  rw [lp_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (liftLp hf σ hσ) (liftLp hf (s / 2) le_rfl),
    (logLift_memLp hf (by linarith : s ≤ 2 * σ)).coeFn_toLp,
    (logLift_memLp hf (by linarith : s ≤ 2 * (s / 2))).coeFn_toLp] with t h1 h2 h3
  simp only [liftLp] at h1 ⊢
  simp only [h1, Pi.sub_apply, h2, h3]

theorem liftLp_tendsto {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {σ : ℕ → ℝ} (hσ : ∀ n, s / 2 ≤ σ n) (ht : Tendsto σ atTop (𝓝 (s / 2))) :
    Tendsto (fun n => liftLp hf (σ n) (hσ n)) atTop (𝓝 (liftLp hf (s / 2) le_rfl)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := logLift_sub_energy_tendsto hf hσ ht
  have he : (fun n => ‖liftLp hf (σ n) (hσ n) - liftLp hf (s / 2) le_rfl‖ ^ 2) =
      (fun n => ∫ t : ℝ, ‖logLift f (σ n) t - logLift f (s / 2) t‖ ^ 2) :=
    funext (fun n => liftLp_sub_norm_sq hf (hσ n))
  rw [← he] at h
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hh

theorem boundaryTrace_tendsto {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {σ : ℕ → ℝ} (hσ : ∀ n, s / 2 ≤ σ n) (ht : Tendsto σ atTop (𝓝 (s / 2))) :
    Tendsto (fun n => 𝓕 (liftLp hf (σ n) (hσ n))) atTop (𝓝 (boundaryTrace hf)) := by
  exact (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ))).continuous.continuousAt.tendsto.comp
    (liftLp_tendsto hf hσ ht)

theorem fourier_liftLp_ae_eq {f : ℝ → ℂ} {s σ : ℝ} (hf : FiniteEnergy f s)
    (hσ : s / 2 < σ) :
    (fun w => (𝓕 (liftLp hf σ hσ.le) : Lp ℂ 2 (volume : Measure ℝ)) w) =ᵐ[volume]
      (fun w => transform f (verticalPoint σ w)) := by
  have h := RiemannResearch.Analysis.fourier_toLp_ae_eq_of_integrable
    (logLift_integrable hf hσ) (logLift_memLp hf (by linarith : s ≤ 2 * σ))
  filter_upwards [h] with w hw
  exact hw.trans (logLift_fourier f σ w)

theorem boundaryTrace_norm_sq {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s) :
    ‖boundaryTrace hf‖ ^ 2 = energy f s := by
  rw [boundaryTrace, Lp.norm_fourier_eq, lp_norm_sq_integral]
  calc
    _ = ∫ t : ℝ, ‖logLift f (s / 2) t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [(logLift_memLp hf (by linarith : s ≤ 2 * (s / 2))).coeFn_toLp]
        with t ht
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) ht
    _ = energy f s := by rw [logLift_energy]; congr 1; ring

theorem transform_boundary_L2 {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {σ : ℕ → ℝ} (hσ : ∀ n, s / 2 < σ n) (ht : Tendsto σ atTop (𝓝 (s / 2))) :
    Tendsto (fun n => (vertical_memLp hf (hσ n)).toLp
      (fun w => transform f (verticalPoint (σ n) w))) atTop (𝓝 (boundaryTrace hf)) := by
  have he (n : ℕ) : (vertical_memLp hf (hσ n)).toLp
      (fun w => transform f (verticalPoint (σ n) w)) =
      𝓕 (liftLp hf (σ n) (hσ n).le) := by
    apply Lp.ext
    exact ((vertical_memLp hf (hσ n)).coeFn_toLp).trans
      (fourier_liftLp_ae_eq hf (hσ n)).symm
  simp_rw [he]
  exact boundaryTrace_tendsto hf (fun n => (hσ n).le) ht

theorem transform_boundary_integral {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s)
    {σ : ℕ → ℝ} (hσ : ∀ n, s / 2 < σ n) (ht : Tendsto σ atTop (𝓝 (s / 2))) :
    Tendsto (fun n => ∫ w : ℝ,
      ‖transform f (verticalPoint (σ n) w) - boundaryTrace hf w‖ ^ 2) atTop (𝓝 0) := by
  have hn := (tendsto_iff_norm_sub_tendsto_zero.mp
    (transform_boundary_L2 hf hσ ht)).pow 2
  have he (n : ℕ) :
      ‖(vertical_memLp hf (hσ n)).toLp
        (fun w => transform f (verticalPoint (σ n) w)) - boundaryTrace hf‖ ^ 2 =
      ∫ w : ℝ, ‖transform f (verticalPoint (σ n) w) - boundaryTrace hf w‖ ^ 2 := by
    rw [lp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((vertical_memLp hf (hσ n)).toLp
        (fun w => transform f (verticalPoint (σ n) w))) (boundaryTrace hf),
      (vertical_memLp hf (hσ n)).coeFn_toLp] with w hw hv
    simp only [hw, Pi.sub_apply, hv]
  simp_rw [he] at hn
  simpa using hn

/-- The squared trace differences are integrable, independently of their limit. -/
theorem transform_boundary_difference_integrable {f : ℝ → ℂ} {s σ : ℝ}
    (hf : FiniteEnergy f s) (hσ : s / 2 < σ) :
    Integrable (fun w : ℝ =>
      ‖transform f (verticalPoint σ w) - boundaryTrace hf w‖ ^ 2) := by
  have hm := (vertical_memLp hf hσ).sub (Lp.memLp (boundaryTrace hf))
  exact (memLp_two_iff_integrable_sq_norm hm.1).mp hm

end MeasureTheory.WeightedMellin
