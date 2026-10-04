import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integral Cauchy bound for marked spectral windows

Source: user manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`, marked spectral
window argument. This closes the analytic Cauchy step for actual Bochner integrals.
The `MemLp` hypotheses express square-integrability, and no scalar Cauchy
inequality or zero-counting theorem is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RiemannResearch.Analysis.MarkedIntegralCauchy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Ordinary integral norm-square agrees with the L2 norm-square. -/
theorem integral_norm_sq_eq_toLp_norm_sq {f : X → ℂ} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) (hf.toLp f) (hf.toLp f)
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  calc
    _ = ∫ x, ‖(hf.toLp f) x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := h.symm

/-- Complex conjugate pairing is the actual L2 inner product. -/
theorem integral_mul_star_eq_inner {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * star (g x) ∂μ) = inner ℂ (hg.toLp g) (hf.toLp f) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply]
  rfl

/-- The marked integral satisfies Cauchy–Schwarz, including zero-energy cases. -/
theorem integral_mul_star_norm_sq_le {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * star (g x) ∂μ‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  rw [integral_mul_star_eq_inner hf hg,
    integral_norm_sq_eq_toLp_norm_sq hf, integral_norm_sq_eq_toLp_norm_sq hg]
  have h := norm_inner_le_norm (𝕜 := ℂ) (hg.toLp g) (hf.toLp f)
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  nlinarith

end RiemannResearch.Analysis.MarkedIntegralCauchy
