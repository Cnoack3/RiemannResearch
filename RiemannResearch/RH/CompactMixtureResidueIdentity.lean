import RiemannResearch.RH.CompactMixtureResidueSummation
import RiemannResearch.RH.CompactFrequencyMellinEntire

/-!
# The full Mellin/Fubini identity for compact-frequency mixtures

Source: user-provided compact-frequency rigidity argument, 2026-09-21,
Section 3. The analytic summation and integrability providers in the imported
modules have the exact compact-frequency hypotheses; no further arithmetic
or measure-theoretic premise is introduced here.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.SpectralObstruction

private theorem nat_cpow_vertical_factor (σ t : ℝ) (d : ℕ) (hd : 2 ≤ d) :
    (d : ℂ) ^ (-verticalPoint σ t) =
      Complex.exp (-(σ : ℂ) * (Real.log (d : ℝ) : ℂ)) *
        Complex.exp (-(t : ℂ) * Complex.I * (Real.log (d : ℝ) : ℂ)) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hlog : Complex.log (d : ℂ) = (Real.log (d : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg d)).symm
  rw [Complex.cpow_def_of_ne_zero hd0, hlog, ← Complex.exp_add]
  congr 1
  unfold verticalPoint
  ring

private theorem reciprocal_eq_vertical_exp_product (σ : ℝ) (d : ℕ) (hd : 2 ≤ d) :
    (1 / (d : ℂ)) =
      Complex.exp (-(σ : ℂ) * (Real.log (d : ℝ) : ℂ)) *
        Complex.exp (((σ : ℂ) - 1) * (Real.log (d : ℝ) : ℂ)) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hlog : Complex.log (d : ℂ) = (Real.log (d : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg d)).symm
  have hL : Complex.exp (Real.log (d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← hlog, Complex.exp_log hd0]
  rw [← Complex.exp_add]
  rw [show -(σ : ℂ) * (Real.log (d : ℝ) : ℂ) +
      ((σ : ℂ) - 1) * (Real.log (d : ℝ) : ℂ) =
        -(Real.log (d : ℝ) : ℂ) by ring]
  rw [Complex.exp_neg, hL, one_div]

/-- The actual compact-mixture identity, including absolute summability,
holds on the critical line and throughout the stipulated half-strip. -/
theorem mixtureResidueIdentity_of_compact_data
    (σ T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hdata : CompactFrequencyData σ T μ a) : MixtureResidueIdentity σ μ a := by
  intro d hd
  have hsum := continuumMixture_residue_hasSum_integral σ T μ a hdata d hd
  refine ⟨hsum.summable, ?_⟩
  unfold residuePairing
  rw [hsum.tsum_eq]
  let L : ℂ := (Real.log (d : ℝ) : ℂ)
  let E : ℂ := Complex.exp (-(σ : ℂ) * L)
  let b : ℝ → ℂ := zetaWeightedDensity σ a
  have hb : Integrable b μ := zetaWeightedDensity_integrable σ T μ a hdata
  have hf : Integrable (fun t => b t * Complex.exp (-(t : ℂ) * Complex.I * L)) μ :=
    densityFourier_integrable T μ b hb hdata.2.2.2.2.2 L
  calc
    (∫ t, a t * ((1 / (d : ℂ) - (d : ℂ) ^ (-verticalPoint σ t)) *
        riemannZeta (verticalPoint σ t)) ∂μ) =
      ∫ t, E * (b t * Complex.exp (((σ : ℂ) - 1) * L) -
        b t * Complex.exp (-(t : ℂ) * Complex.I * L)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [nat_cpow_vertical_factor σ t d hd,
        reciprocal_eq_vertical_exp_product σ d hd]
      dsimp only [E, L, b, zetaWeightedDensity]
      ring
    _ = E * ((∫ t, b t ∂μ) * Complex.exp (((σ : ℂ) - 1) * L) -
        ∫ t, b t * Complex.exp (-(t : ℂ) * Complex.I * L) ∂μ) := by
      rw [integral_const_mul, integral_sub (hb.mul_const _) hf, integral_mul_const]
    _ = -Complex.exp (-(σ : ℂ) * (Real.log (d : ℝ) : ℂ)) *
        samplingDefect σ μ a (Real.log (d : ℝ)) := by
      dsimp only [E, L, b, samplingDefect, densityMass, densityFourier]
      ring

end RiemannResearch.RH.Pareto.SpectralObstruction
