import RiemannResearch.RH.CauchyFourierTransform
import RiemannResearch.Analysis.MarkedIntegralCauchy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact original rational-kernel marked spectral representation

Source: user manuscript's marked spectral form, with its original kernel
`w(x)=4/(4+x²)`. All finite occurrences are retained; the ordinate map need not
be injective. Uses the existing proved Laplace transform after three private
support declarations in `CauchyFourierTransform` are promoted to public.
-/

noncomputable section
open MeasureTheory Complex
open scoped BigOperators

namespace RiemannResearch.Analysis.MarkedLaplaceKernel

open RiemannResearch.RH.Pareto.SpectralObstruction

/-- Positive-sign angular phase. -/
def phase (a t : ℝ) : ℂ := Complex.exp ((a * t : ℝ) * I)

@[simp] theorem phase_norm (a t : ℝ) : ‖phase a t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- A literal finite sum, preserving repetitions in the ordinate map. -/
def amplitude {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q t : ℝ) : ℂ :=
  ∑ j ∈ s, phase (γ j) (q + t)

theorem amplitude_norm_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q t : ℝ) :
    ‖amplitude s γ q t‖ ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ j ∈ s, ‖phase (γ j) (q + t)‖ := norm_sum_le _ _
    _ = _ := by simp

/-- The half-density converts the original positive Laplace-weight integral to L2. -/
def dampedAmplitude {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q t : ℝ) : ℂ :=
  (Real.exp (-|t|) : ℂ) * amplitude s γ q t

theorem laplace_half_density_memLp :
    MemLp (fun t : ℝ => (Real.exp (-|t|) : ℂ)) 2 := by
  have hi : Integrable (fun t : ℝ => Real.exp (-2 * |t|)) := by
    simpa [laplaceFourierIntegrand, Complex.norm_exp] using
      (laplaceFourierIntegrand_integrable 2 0 (by norm_num)).norm
  apply (memLp_two_iff_integrable_sq_norm
    (show AEStronglyMeasurable (fun t : ℝ => (Real.exp (-|t|) : ℂ)) volume by
      fun_prop)).2
  have heq : (fun t : ℝ => ‖(Real.exp (-|t|) : ℂ)‖ ^ 2) =
      (fun t : ℝ => Real.exp (-2 * |t|)) := by
    funext t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hi

theorem dampedAmplitude_memLp {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q : ℝ) :
    MemLp (dampedAmplitude s γ q) 2 := by
  apply laplace_half_density_memLp.of_le_mul
    (show AEStronglyMeasurable (dampedAmplitude s γ q) volume by
      unfold dampedAmplitude amplitude phase
      fun_prop)
  apply Filter.Eventually.of_forall
  intro t
  unfold dampedAmplitude
  rw [norm_mul]
  calc
    _ ≤ ‖(Real.exp (-|t|) : ℂ)‖ * (s.card : ℝ) :=
      mul_le_mul_of_nonneg_left (amplitude_norm_le s γ q t) (norm_nonneg _)
    _ = _ := by ring

/-- Exact finite marked expansion before integration. -/
theorem amplitude_mul_star {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u t : ℝ) :
    amplitude s γ (q + u) t * star (amplitude s γ q t) =
      ∑ j ∈ s, ∑ k ∈ s,
        (phase u (γ j) * phase q (γ j - γ k)) * phase (γ j - γ k) t := by
  simp only [amplitude, star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exact original rational form, before normalizing by the zero count. -/
def kernelForm {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q u : ℝ) : ℂ :=
  ∑ j ∈ s, ∑ k ∈ s, (phase u (γ j) * phase q (γ j - γ k)) *
    ((4 / (4 + (γ j - γ k) ^ 2) : ℝ) : ℂ)

/-- The weighted integrand equals the complete finite signed pair expansion. -/
theorem dampedAmplitude_mul_star {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u t : ℝ) :
    dampedAmplitude s γ (q + u) t * star (dampedAmplitude s γ q t) =
      ∑ j ∈ s, ∑ k ∈ s, (phase u (γ j) * phase q (γ j - γ k)) *
        laplaceFourierIntegrand 2 (-(γ j - γ k)) t := by
  have hd : (Real.exp (-|t|) : ℂ) * (Real.exp (-|t|) : ℂ) =
      (Real.exp (-2 * |t|) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  have hk (a : ℝ) : (Real.exp (-2 * |t|) : ℂ) * phase a t =
      laplaceFourierIntegrand 2 (-a) t := by
    unfold phase laplaceFourierIntegrand
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ((Real.exp (-|t|) : ℂ) * (Real.exp (-|t|) : ℂ)) *
        (amplitude s γ (q + u) t * star (amplitude s γ q t)) := by
      simp only [dampedAmplitude, star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = (Real.exp (-2 * |t|) : ℂ) *
        (∑ j ∈ s, ∑ k ∈ s,
          (phase u (γ j) * phase q (γ j - γ k)) * phase (γ j - γ k) t) := by
      rw [hd, amplitude_mul_star]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk'
      rw [← hk (γ j - γ k)]
      ring

/-- The original rational marked pair form is an actual convergent integral. -/
theorem integral_dampedAmplitude_mul_star {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u : ℝ) :
    (∫ t, dampedAmplitude s γ (q + u) t * star (dampedAmplitude s γ q t)) =
      kernelForm s γ q u := by
  have hint (j k : ι) : Integrable
      (fun t => (phase u (γ j) * phase q (γ j - γ k)) *
        laplaceFourierIntegrand 2 (-(γ j - γ k)) t) :=
    (laplaceFourierIntegrand_integrable 2 (-(γ j - γ k)) (by norm_num)).const_mul _
  simp_rw [dampedAmplitude_mul_star]
  rw [integral_finsetSum s (fun j hj => integrable_finsetSum s (fun k hk => hint j k))]
  unfold kernelForm
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum s (fun k hk => hint j k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_laplaceFourierIntegrand _ _ (by norm_num)]
  simp only [neg_sq]
  norm_num

/-- The unmarked energy is a genuine nonnegative weighted square integral. -/
def energy {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q : ℝ) : ℝ :=
  ∫ t, ‖dampedAmplitude s γ q t‖ ^ 2

theorem energy_nonneg {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (q : ℝ) :
    0 ≤ energy s γ q := integral_nonneg (fun t => sq_nonneg _)

/-- The unmarked original rational form is exactly the real nonnegative
weighted square energy, including every repeated ordinate. -/
theorem kernelForm_zero_eq_energy {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q : ℝ) : kernelForm s γ q 0 = (energy s γ q : ℂ) := by
  have hp := dampedAmplitude_memLp s γ q
  rw [← integral_dampedAmplitude_mul_star, add_zero,
    MarkedIntegralCauchy.integral_mul_star_eq_inner hp hp,
    inner_self_eq_norm_sq_to_K]
  have hreal : ‖hp.toLp (dampedAmplitude s γ q)‖ ^ 2 = energy s γ q :=
    (MarkedIntegralCauchy.integral_norm_sq_eq_toLp_norm_sq hp).symm
  simpa using congrArg (fun r : ℝ => (r : ℂ)) hreal

/-- Actual integral Cauchy bounds the exact original rational marked kernel form.
There is no assumed scalar Cauchy-square inequality. -/
theorem kernelForm_norm_sq_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    (q u : ℝ) :
    ‖kernelForm s γ q u‖ ^ 2 ≤ energy s γ (q + u) * energy s γ q := by
  rw [← integral_dampedAmplitude_mul_star]
  exact MarkedIntegralCauchy.integral_mul_star_norm_sq_le
    (dampedAmplitude_memLp s γ (q + u)) (dampedAmplitude_memLp s γ q)

end RiemannResearch.Analysis.MarkedLaplaceKernel
