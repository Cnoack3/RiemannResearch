import RiemannResearch.Analysis.WeightedMellinEnergy
import RiemannResearch.Analysis.FourierL1L2Plancherel
import Mathlib.Tactic.LinearCombination

/-!
# Weighted Mellin energy implies Hardy H2

The logarithmic substitution gives an actual L1 intersection L2 Fourier
integral on every interior vertical line. Ordinary Plancherel proves the
line-energy identity, genuine L2 membership, and the uniform Hardy bound.
Dominated convergence identifies its supremum with the original energy.

Source: user-requested companion
RH_Energy_Holomorphy_Hardy_Implications_2026-09-18.md, Mellin--Hardy argument.
The Hardy definition uses z = sigma + 2*pi*i*w; angular_plancherel spells out
the standard 1/(2*pi) normalization. This is the forward implication;
no general Paley--Wiener converse or boundary L2 trace theorem is asserted.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace MeasureTheory.WeightedMellin
open FourierTransform

def logLift (f : ℝ → ℂ) (σ : ℝ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (fun t => f (Real.exp t) * (Real.exp (-σ*t) : ℂ))

theorem logLift_measurable {f : ℝ → ℂ} (hf : Measurable f) (σ : ℝ) :
    Measurable (logLift f σ) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact (hf.comp Real.measurable_exp).mul
    (Complex.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)))

theorem logLift_norm_sq {f : ℝ → ℂ} {σ t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    ‖logLift f σ t‖^2 =
      Real.exp t * (‖f (Real.exp t)‖^2 * (Real.exp t)^(-(2*σ)-1)) := by
  simp only [logLift, indicator_of_mem ht, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, mul_left_comm (Real.exp t),
    ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem logLift_memLp {f : ℝ → ℂ} {s σ : ℝ}
    (hf : FiniteEnergy f s) (hs : s ≤ 2*σ) : MemLp (logLift f σ) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (logLift_measurable hf.1 σ).aestronglyMeasurable).2
  have hi := (integrableOn_comp_exp_Ioi
    (fun x : ℝ => ‖f x‖^2*x^(-(2*σ)-1)) 0).2
      (by simpa using (finiteEnergy_mono hf hs).2)
  have he : (fun t => ‖logLift f σ t‖^2) =
      (Ioi (0:ℝ)).indicator
        (fun t => Real.exp t • (‖f (Real.exp t)‖^2*(Real.exp t)^(-(2*σ)-1))) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simpa only [indicator_of_mem ht, smul_eq_mul] using logLift_norm_sq (f:=f) (σ:=σ) ht
    · simp [logLift, ht]
  rw [he]
  exact hi.integrable_indicator measurableSet_Ioi

theorem logLift_energy (f : ℝ → ℂ) (σ : ℝ) :
    (∫ t, ‖logLift f σ t‖^2) = energy f (2*σ) := by
  calc
    _ = ∫ t in Ioi (0:ℝ), ‖logLift f σ t‖^2 := by
      symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht; simp [logLift, ht]
    _ = ∫ t in Ioi (0:ℝ),
        Real.exp t • (‖f (Real.exp t)‖^2*(Real.exp t)^(-(2*σ)-1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact logLift_norm_sq ht
    _ = _ := by
      simpa [energy] using integral_comp_exp_Ioi
        (fun x : ℝ => ‖f x‖^2*x^(-(2*σ)-1)) 0

def verticalPoint (σ w : ℝ) : ℂ := (σ : ℂ) + ((2*Real.pi*w:ℝ):ℂ)*Complex.I

theorem exp_factor (σ t w : ℝ) :
    (Real.exp t : ℂ)*(Real.exp t : ℂ)^(-verticalPoint σ w-1) =
      Complex.exp (((-2*Real.pi*t*w:ℝ):ℂ)*Complex.I) * (Real.exp (-σ*t):ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)),
    ← Complex.ofReal_log (Real.exp_nonneg t), Real.log_exp,
    Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold verticalPoint
  push_cast
  ring

theorem logLift_integrable {f : ℝ → ℂ} {s σ : ℝ}
    (hf : FiniteEnergy f s) (hs : s/2 < σ) : Integrable (logLift f σ) := by
  have hi := (integrableOn_comp_exp_Ioi
    (fun x : ℝ => f x*(x:ℂ)^(-(σ:ℂ)-1)) 0).2
      (by simpa using transform_integrable hf (z := (σ:ℂ)) hs)
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioi
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have he := exp_factor σ t 0
  simp only [verticalPoint, mul_zero, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.exp_zero, one_mul] at he
  simp only [Complex.real_smul]
  linear_combination (f (Real.exp t)) * he

theorem logLift_fourier (f : ℝ → ℂ) (σ w : ℝ) :
    𝓕 (logLift f σ) w = transform f (verticalPoint σ w) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t in Ioi (0:ℝ),
        Complex.exp (((-2*Real.pi*t*w:ℝ):ℂ)*Complex.I) • logLift f σ t := by
      symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht; simp [logLift, ht]
    _ = ∫ t in Ioi (0:ℝ), Real.exp t •
        (f (Real.exp t)*(Real.exp t:ℂ)^(-verticalPoint σ w-1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [logLift, indicator_of_mem ht, smul_eq_mul, Complex.real_smul]
      linear_combination -(f (Real.exp t)) * exp_factor σ t w
    _ = _ := by
      simpa [transform] using integral_comp_exp_Ioi
        (fun x : ℝ => f x*(x:ℂ)^(-verticalPoint σ w-1)) 0

theorem vertical_plancherel {f : ℝ → ℂ} {s σ : ℝ}
    (hf : FiniteEnergy f s) (hs : s/2 < σ) :
    (∫ w : ℝ, ‖transform f (verticalPoint σ w)‖^2) = energy f (2*σ) := by
  simp_rw [← logLift_fourier]
  rw [RiemannResearch.Analysis.integral_norm_sq_fourier_of_integrable
    (logLift_integrable hf hs) (logLift_memLp hf (by linarith))]
  exact logLift_energy f σ

theorem vertical_memLp {f : ℝ → ℂ} {s σ : ℝ}
    (hf : FiniteEnergy f s) (hs : s/2 < σ) :
    MemLp (fun w => transform f (verticalPoint σ w)) 2 := by
  have hl := logLift_memLp hf (by linarith : s ≤ 2*σ)
  have he := RiemannResearch.Analysis.fourier_toLp_ae_eq_of_integrable
    (logLift_integrable hf hs) hl
  have hm := (memLp_congr_ae he).mp
    (Lp.memLp (𝓕 (hl.toLp (logLift f σ)) : Lp ℂ 2 (volume : Measure ℝ)))
  have heq : 𝓕 (logLift f σ) = (fun w => transform f (verticalPoint σ w)) :=
    funext (logLift_fourier f σ)
  rwa [heq] at hm

/-- Hardy H2 on a right half-plane, with Fourier-frequency parametrization
z = sigma + 2*pi*i*w; this gives the standard 1/(2*pi) angular normalization. -/
def HardyH2 (F : ℂ → ℂ) (α : ℝ) : Prop :=
  (∀ z, α < z.re → AnalyticAt ℂ F z) ∧
  (∀ σ, α < σ → MemLp (fun w => F (verticalPoint σ w)) 2) ∧
  ∃ C : ℝ, ∀ σ, α < σ → (∫ w : ℝ, ‖F (verticalPoint σ w)‖^2) ≤ C

theorem energy_to_hardy {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s) :
    HardyH2 (transform f) (s/2) := by
  refine ⟨fun z hz => transform_analyticAt hf hz,
    fun σ hσ => vertical_memLp hf hσ, energy f s, ?_⟩
  intro σ hσ
  rw [vertical_plancherel hf hσ]
  exact energy_mono hf (by linarith)

theorem angular_plancherel {f : ℝ → ℂ} {s σ : ℝ}
    (hf : FiniteEnergy f s) (hs : s/2 < σ) :
    (1/(2*Real.pi)) * (∫ t : ℝ, ‖transform f ((σ:ℂ)+(t:ℂ)*Complex.I)‖^2)
      = energy f (2*σ) := by
  have he := Measure.integral_comp_mul_left
    (fun t : ℝ => ‖transform f ((σ:ℂ)+(t:ℂ)*Complex.I)‖^2) (2*Real.pi)
  have hp : 0 < 2*Real.pi := by positivity
  rw [abs_of_pos (inv_pos.mpr hp), smul_eq_mul] at he
  rw [one_div]
  rw [← he]
  exact vertical_plancherel hf hs

theorem hardy_energy_le {f : ℝ → ℂ} {s σ : ℝ}
    (hf : FiniteEnergy f s) (hs : s/2 < σ) :
    (∫ w : ℝ, ‖transform f (verticalPoint σ w)‖^2) ≤ energy f s := by
  rw [vertical_plancherel hf hs]
  exact energy_mono hf (by linarith)


/-- The squared Hardy norm is exactly the original weighted energy. -/
theorem hardy_energy_isLUB {f : ℝ → ℂ} {s : ℝ} (hf : FiniteEnergy f s) :
    IsLUB {v : ℝ | ∃ σ : ℝ, s/2 < σ ∧
      v = ∫ w : ℝ, ‖transform f (verticalPoint σ w)‖^2} (energy f s) := by
  constructor
  · rintro v ⟨σ, hσ, rfl⟩
    exact hardy_energy_le hf hσ
  · intro C hC
    have hu : ∀ n : ℕ, s ≤ s + 1/((n:ℝ)+1) := by
      intro n
      have : 0 < (1:ℝ)/((n:ℝ)+1) := by positivity
      linarith
    have ht : Tendsto (fun n : ℕ => s + 1/((n:ℝ)+1)) atTop (𝓝 s) := by
      simpa using tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    apply le_of_tendsto (energy_tendsto hf hu ht)
    apply Filter.Eventually.of_forall
    intro n
    let σ : ℝ := (s + 1/((n:ℝ)+1))/2
    have hσ : s/2 < σ := by
      have : 0 < (1:ℝ)/((n:ℝ)+1) := by positivity
      dsimp [σ]; linarith
    have he : 2*σ = s + 1/((n:ℝ)+1) := by dsimp [σ]; ring
    have hb := hC ⟨σ, hσ, rfl⟩
    rw [vertical_plancherel hf hσ, he] at hb
    exact hb

end MeasureTheory.WeightedMellin
