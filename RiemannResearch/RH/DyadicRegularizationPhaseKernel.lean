import RiemannResearch.RH.DampedMobiusFourierSymbol
import RiemannResearch.RH.DyadicResidueFourierCocycle
import RiemannResearch.RH.DyadicRegularizedMean
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Exact arithmetic phase kernel for the actual damped family

Source: user-provided FourierResidueBridgeVerification20260911(1).md and
the actual product-index coefficients already defined by the project.
Möbius Dirichlet inversion and a geometric series evaluate the signed
kernel at every positive damping; no zero-damping energy bound is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem dyadicTriadicDampedPhase_hasSum {ε : ℝ} (hε : 0 < ε) (h : ℤ) :
    HasSum (fun j : ℕ =>
      ((triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h)^j)
      (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h)⁻¹ := by
  apply hasSum_geometric_of_norm_lt_one
  rw [norm_mul, norm_dyadicTriadicFourierPhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (triadicDampingRatio_pos ε)]
  exact triadicDampingRatio_lt_one hε

/-- Exact signed arithmetic kernel, with both Möbius and triadic indices present. -/
theorem dyadicRegularizationPhaseKernel_hasSum {ε : ℝ} (hε : 0 < ε) (h : ℤ) :
    HasSum (fun p : ℕ × ℕ =>
      (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ) *
        dyadicIntegerFourierPhase h ((p.1+1)*3^p.2))
      ((riemannZeta (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h : ℂ)))⁻¹ /
        (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h)) := by
  have hm := dampedMobius_phase_hasSum_inv_zeta hε h
  have hj := dyadicTriadicDampedPhase_hasSum hε h
  have hprod := summable_mul_of_summable_norm hm.summable.norm hj.summable.norm
  have hp := hm.mul hj hprod
  convert hp using 1 <;> try rfl
  · funext p
    rw [dyadicIntegerFourierPhase_mul_triadic_pow h (p.1+1) (by omega) p.2]
    simp only [dyadicRegularizationCoefficient, Complex.ofReal_mul,
      Complex.ofReal_pow, mul_pow]
    ring

theorem dyadicRegularizationPhaseKernel_tsum {ε : ℝ} (hε : 0 < ε) (h : ℤ) :
    (∑' p : ℕ × ℕ, (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ) *
      dyadicIntegerFourierPhase h ((p.1+1)*3^p.2)) =
      (riemannZeta (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h : ℂ)))⁻¹ /
        (1 - (triadicDampingRatio ε : ℂ) * dyadicTriadicFourierPhase h) :=
  (dyadicRegularizationPhaseKernel_hasSum hε h).tsum_eq

/-- The complete actual scalar coefficient family is absolutely summable. -/
theorem dyadicRegularizationCoefficient_abs_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun p : ℕ × ℕ => |dyadicRegularizationCoefficient ε p.1 p.2|) := by
  simpa only [norm_mul, norm_dyadicIntegerFourierPhase, mul_one,
    Complex.norm_real, Real.norm_eq_abs] using
    (dyadicRegularizationPhaseKernel_hasSum hε 0).summable.norm

/-- The zero-frequency scalar coefficient sum uses the original real Möbius series. -/
theorem dyadicRegularizationCoefficient_hasSum {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun p : ℕ × ℕ => (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ))
      ((regularizationMobiusSeries ε : ℂ) / (1 - (triadicDampingRatio ε : ℂ))) := by
  have hm : HasSum (fun n : ℕ =>
      (((ArithmeticFunction.moebius (n+1) : ℝ) / (n+1 : ℝ)^(1+ε) : ℝ) : ℂ))
      (regularizationMobiusSeries ε : ℂ) := by
    simpa only [regularizationMobiusSeries, Complex.ofReal_tsum] using
      (dampedMobius_hasSum_inv_zeta hε).summable.hasSum
  have he := hm.unique (dampedMobius_hasSum_inv_zeta hε)
  have hp := dyadicRegularizationPhaseKernel_hasSum hε 0
  simpa only [dyadicIntegerFourierPhase_zero, dyadicTriadicFourierPhase_zero,
    mul_one, dyadicLogFrequency_zero, Complex.ofReal_zero, mul_zero, sub_zero, ← he] using hp

/-- The exact normalized zero mode is one for the actual arithmetic coefficients. -/
theorem dyadicRegularizationPhaseKernel_zero_normalization {ε : ℝ} (hε : 0 < ε) :
    (dyadicRegularizationNormalization ε : ℂ) *
      ((∑' p : ℕ × ℕ, (dyadicRegularizationCoefficient ε p.1 p.2 : ℂ)) *
        (Real.log 3 : ℂ)) = 1 := by
  rw [(dyadicRegularizationCoefficient_hasSum hε).tsum_eq]
  have hlog : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hq : 1 - triadicDampingRatio ε ≠ 0 :=
    ne_of_gt (sub_pos.mpr (triadicDampingRatio_lt_one hε))
  have hr : dyadicRegularizationNormalization ε *
      ((regularizationMobiusSeries ε / (1 - triadicDampingRatio ε)) * Real.log 3) = 1 := by
    calc
      _ = regularizationZetaSeries ε * regularizationMobiusSeries ε := by
        unfold dyadicRegularizationNormalization
        field_simp [hlog, hq]
      _ = 1 := regularizationZetaSeries_mul_mobius ε hε
  exact_mod_cast hr

end
end RiemannResearch.RH.Pareto
