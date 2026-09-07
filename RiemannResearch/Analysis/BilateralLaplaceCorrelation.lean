import RiemannResearch.Analysis.SuperexponentialLaplace
import RiemannResearch.Analysis.BilateralLaplaceTranslation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual bilateral transform of a cross-correlation

The two-dimensional integrability is established from ordinary integrability
after an exact translation. Fubini's theorem is then applied to the actual
Bochner integrals. No correlation transform identity is assumed.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace MeasureTheory.BilateralLaplace

theorem kernel_conj (z : ℂ) (y : ℝ) :
    conj (kernel z y) = kernel (conj z) y := by
  simp only [kernel, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]

theorem kernel_mul_neg (z : ℂ) (y : ℝ) :
    kernel z y * kernel (-z) y = 1 := by
  rw [kernel, kernel, ← Complex.exp_add]
  rw [show -z * (y : ℂ) + -(-z) * (y : ℂ) = 0 by ring, Complex.exp_zero]

theorem transform_conj (f : ℝ → ℂ) (z : ℂ) :
    transform (fun y => conj (f y)) z = conj (transform f (conj z)) := by
  unfold transform
  rw [← integral_conj]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  simp only [map_mul, kernel_conj]
  simp

/-- Actual joint integrability after a triangular change of variables. -/
theorem integrable_translated_mul {A B : ℝ → ℂ}
    (hAc : Continuous A) (hBc : Continuous B)
    (hA : Integrable A) (hB : Integrable B) :
    Integrable (fun p : ℝ × ℝ => A (p.1 + p.2) * B p.2) (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ => A (p.1 + p.2) * B p.2) := by fun_prop
  have hnorm (y : ℝ) : (∫ t : ℝ, ‖A (t + y) * B y‖) =
      (∫ x : ℝ, ‖A x‖) * ‖B y‖ := by
    simp_rw [norm_mul]
    rw [integral_mul_const]
    have hshift := integral_add_right_eq_self (μ := volume) (fun x : ℝ => ‖A x‖) y
    rw [hshift]
  apply (integrable_prod_iff' hcont.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun y => (hA.comp_add_right y).mul_const (B y))
  · simpa only [hnorm] using hB.norm.const_mul (∫ x : ℝ, ‖A x‖)

/-- Integrability and Fubini for the translated product are proved explicitly. -/
theorem integral_integral_translated_mul {A B : ℝ → ℂ}
    (hAc : Continuous A) (hBc : Continuous B)
    (hA : Integrable A) (hB : Integrable B) :
    (∫ t : ℝ, ∫ y : ℝ, A (t + y) * B y) =
      (∫ x : ℝ, A x) * ∫ y : ℝ, B y := by
  have hprod := integrable_translated_mul hAc hBc hA hB
  calc
    (∫ t : ℝ, ∫ y : ℝ, A (t + y) * B y) =
        ∫ y : ℝ, ∫ t : ℝ, A (t + y) * B y := integral_integral_swap hprod
    _ = ∫ y : ℝ, (∫ x : ℝ, A x) * B y := by
      congr 1
      funext y
      rw [integral_mul_const, integral_add_right_eq_self A y]
    _ = _ := integral_const_mul _ _

/-- The outer correlation is integrable; no derivative bound is required. -/
theorem integrable_crossCorrelation {f g : ℝ → ℂ}
    (hfc : Continuous f) (hgc : Continuous g)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (RiemannResearch.Analysis.crossCorrelation f g) := by
  have hgcj : Continuous (fun y : ℝ => conj (g y)) := by fun_prop
  have hgi : Integrable (fun y : ℝ => conj (g y)) := by
    apply hg.norm.mono' hgcj.aestronglyMeasurable
    exact ae_of_all _ (fun y => by simp)
  have hprod := integrable_translated_mul hfc hgcj hf hgi
  have heq : RiemannResearch.Analysis.crossCorrelation f g =
      (fun x : ℝ => ∫ y : ℝ, f (x + y) * conj (g y)) := by
    funext x
    unfold RiemannResearch.Analysis.crossCorrelation
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by
      change f (y + x) * star (g y) = f (x + y) * conj (g y)
      rw [add_comm y x]
      rfl)
  rw [heq]
  exact hprod.integral_prod_left

theorem transform_crossCorrelation {f g : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hg : HasExponentialMoments g)
    (hfc : Continuous f) (hgc : Continuous g) (z : ℂ) :
    transform (RiemannResearch.Analysis.crossCorrelation f g) z =
      transform f z * conj (transform g (-conj z)) := by
  let A : ℝ → ℂ := fun x => f x * kernel z x
  let B : ℝ → ℂ := fun y => conj (g y) * kernel (-z) y
  have hAc : Continuous A := by unfold A kernel; fun_prop
  have hBc : Continuous B := by unfold B kernel; fun_prop
  have hA : Integrable A := integrable_integrand hf z
  have hBeq (y : ℝ) : B y = conj (g y * kernel (-conj z) y) := by
    simp only [B, map_mul, kernel_conj, map_neg]
    simp
  have hB : Integrable B := by
    apply (integrable_integrand hg (-conj z)).norm.mono' hBc.aestronglyMeasurable
    exact ae_of_all _ (fun y => by rw [hBeq]; simp)
  have hpoint (t y : ℝ) :
      f (y + t) * star (g y) * kernel z t = A (t + y) * B y := by
    have hk := kernel_mul_neg z y
    dsimp only [A, B]
    rw [kernel_add]
    calc
      f (y + t) * star (g y) * kernel z t =
          (f (t + y) * conj (g y) * kernel z t) *
            (kernel z y * kernel (-z) y) := by rw [hk]; simp [add_comm]
      _ = _ := by ring
  have hBint : (∫ y : ℝ, B y) = conj (transform g (-conj z)) := by
    simp_rw [hBeq]
    exact integral_conj
  calc
    transform (RiemannResearch.Analysis.crossCorrelation f g) z =
        ∫ t : ℝ, ∫ y : ℝ, f (y + t) * star (g y) * kernel z t := by
      unfold transform RiemannResearch.Analysis.crossCorrelation
      simp_rw [integral_mul_const]
    _ = ∫ t : ℝ, ∫ y : ℝ, A (t + y) * B y := by simp_rw [hpoint]
    _ = (∫ x : ℝ, A x) * ∫ y : ℝ, B y :=
      integral_integral_translated_mul hAc hBc hA hB
    _ = _ := by rw [hBint]; rfl

theorem integral_crossCorrelation {f g : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hg : HasExponentialMoments g)
    (hfc : Continuous f) (hgc : Continuous g) :
    (∫ t : ℝ, RiemannResearch.Analysis.crossCorrelation f g t) =
      (∫ y : ℝ, f y) * conj (∫ y : ℝ, g y) := by
  simpa [transform, kernel] using transform_crossCorrelation hf hg hfc hgc 0

end MeasureTheory.BilateralLaplace
