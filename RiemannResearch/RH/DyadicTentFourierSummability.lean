import RiemannResearch.RH.DyadicTentMellinCoefficients
import Mathlib.Analysis.PSeries

/-!
# Absolute summability of the actual dyadic tent Fourier rows

Source: `FourierBridgeUniformSignedEnergy20260910.md`, Section 2,
September 10, 2026. The proof uses the explicit inverse-square bound for
the actual tent Mellin integrals and Mathlib's integer p-series theorem.

This establishes absolute convergence of each scalar coefficient row,
including the zero mode. It does not by itself identify the resulting sum
with the continuous tent periodization; Fourier reconstruction remains a
separate analytic assertion.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
noncomputable section

/-- Every actual scalar coefficient row is absolutely summable, including
its separately evaluated zero-frequency term. -/
theorem summable_norm_dyadicTentMellinCoefficient (i : ℕ) :
    Summable (fun h : ℤ => ‖dyadicTentMellinCoefficient i h‖) := by
  let K : ℝ := 4 * (2 * (i + 1) + 1 : ℝ) * Real.log 2 / (2 * Real.pi) ^ 2
  have hp : Summable (fun h : ℤ => 1 / (h : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have hb := (hp.mul_left K).update 0 ‖dyadicTentMellinCoefficient i 0‖
  apply hb.of_norm_bounded
  intro h
  rw [norm_norm]
  by_cases hh : h = 0
  · subst h
    simp
  · rw [Function.update_of_ne hh]
    simpa only [K, div_eq_mul_inv, mul_one, one_mul] using
      norm_dyadicTentMellinCoefficient_le_inv_sq i hh

/-- The actual coefficient row is summable as a complex series. -/
theorem summable_dyadicTentMellinCoefficient (i : ℕ) :
    Summable (dyadicTentMellinCoefficient i) :=
  (summable_norm_dyadicTentMellinCoefficient i).of_norm

/-- Absolute row summability survives multiplication by any uniformly
bounded scalar factor, in particular a modulus-one Fourier character. -/
theorem summable_norm_dyadicTentMellinCoefficient_mul_of_bounded
    (i : ℕ) (u : ℤ → ℂ) (B : ℝ) (hu : ∀ h, ‖u h‖ ≤ B) :
    Summable (fun h : ℤ => ‖dyadicTentMellinCoefficient i h * u h‖) := by
  apply ((summable_norm_dyadicTentMellinCoefficient i).mul_right B).of_norm_bounded
  intro h
  rw [norm_norm, norm_mul]
  exact mul_le_mul_of_nonneg_left (hu h) (norm_nonneg _)

end
end RiemannResearch.RH.Pareto
