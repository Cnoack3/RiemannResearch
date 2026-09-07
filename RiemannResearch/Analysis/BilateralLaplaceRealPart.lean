import RiemannResearch.Analysis.BilateralLaplaceCorrelation

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Taking a real part inside the actual bilateral transform

Real projection mixes the two reflected spectral parameters. Both terms are
retained; their vanishing is proved from actual transform vanishing.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace MeasureTheory.BilateralLaplace

theorem transform_realPart {C : ℝ → ℂ}
    (hC : HasExponentialMoments C) (hCc : Continuous C) (z : ℂ) :
    transform (fun y => ((C y).re : ℂ)) z =
      (transform C z + conj (transform C (conj z))) / 2 := by
  have hci := integrable_integrand hC z
  have hcj : Continuous (fun y : ℝ => conj (C y) * kernel z y) := by
    unfold kernel
    fun_prop
  have hcji : Integrable (fun y : ℝ => conj (C y) * kernel z y) := by
    apply (integrable_integrand hC (conj z)).norm.mono' hcj.aestronglyMeasurable
    apply ae_of_all
    intro y
    have heq : conj (C y) * kernel z y = conj (C y * kernel (conj z) y) := by
      simp only [map_mul, kernel_conj]
      simp
    rw [heq]
    simp
  have hfun : (fun y : ℝ => ((C y).re : ℂ)) =
      (fun y : ℝ => (1 / 2 : ℂ) * (C y + conj (C y))) := by
    funext y
    apply Complex.ext <;> simp <;> ring
  have hadd : transform (fun y => C y + conj (C y)) z =
      transform C z + transform (fun y => conj (C y)) z := by
    unfold transform
    simp_rw [add_mul]
    exact integral_add hci hcji
  rw [hfun, transform_const_mul, hadd, transform_conj]
  ring

theorem transform_realPart_crossCorrelation_zero {f : ℝ → ℂ}
    (hf : HasExponentialMoments f) (hfc : Continuous f)
    (hC : HasExponentialMoments (RiemannResearch.Analysis.crossCorrelation f f))
    (hCc : Continuous (RiemannResearch.Analysis.crossCorrelation f f))
    (z : ℂ) (hz : transform f z = 0) (hneg : transform f (-z) = 0) :
    transform (fun t => ((RiemannResearch.Analysis.crossCorrelation f f t).re : ℂ)) z = 0 := by
  rw [transform_realPart hC hCc z,
    transform_crossCorrelation hf hf hfc hfc z,
    transform_crossCorrelation hf hf hfc hfc (conj z)]
  simp [hz, hneg]

end MeasureTheory.BilateralLaplace
