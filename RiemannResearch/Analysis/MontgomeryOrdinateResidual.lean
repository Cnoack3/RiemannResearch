import RiemannResearch.Analysis.MontgomeryHorizontalPairing
import RiemannResearch.Analysis.MontgomeryFixedFrequencyResidual

/-! # The signed arithmetic correction for the ordinary form factor

At each positive frequency the zero-cutoff residual and the horizontal cross
term may cancel. The target for their signed difference is the requested
ordinary limit minus the diagonal slope. Source: user-provided comparison.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryOrdinateResidual
open MontgomeryFormFactor MontgomeryHorizontalTransfer
open MontgomeryHorizontalPairing MontgomeryHorizontalBessel

/-- Signed correction for the actual occurrence sums with cutoff (0,T]. -/
def signedHorizontalCorrection (T α : ℝ) : ℝ :=
  (2 * signedHorizontalCross T (α * Real.log T) +
    defectIntegral T (α * Real.log T)) / (T * Real.log T / (2 * Real.pi))

theorem sharp_sub_ordinate_eq (T α : ℝ) :
    sharpFormFactor T α - formFactor T α = signedHorizontalCorrection T α := by
  rw [sharpFormFactor, formFactor_eq_rawIntegral, ← sub_div, sharp_sub_raw_exact]
  rfl

/-- A necessary and sufficient signed arithmetic condition at each fixed
positive frequency. This keeps the prime term and the horizontal term together. -/
theorem ordinateLimit_iff_signedArithmeticCorrection {α ℓ : ℝ} (hα : 0 < α) :
    Tendsto (fun T : ℝ => formFactor T α) atTop (𝓝 ℓ) ↔
    Tendsto (fun T : ℝ => normalizedThirdAndPrimeOffDiagonal T α -
      signedHorizontalCorrection T α) atTop (𝓝 (ℓ - α)) := by
  have hb : Tendsto (fun T : ℝ => formFactor T α -
      (normalizedThirdAndPrimeOffDiagonal T α - signedHorizontalCorrection T α))
      atTop (𝓝 α) := by
    apply (sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_tendsto hα).congr'
    filter_upwards with T
    linarith only [sharp_sub_ordinate_eq T α]
  constructor
  · intro ho
    simpa only [sub_sub_cancel] using ho.sub hb
  · intro hc
    have h := hb.add hc
    rw [show α + (ℓ - α) = ℓ by ring] at h
    simpa only [sub_add_cancel] using h

end RiemannResearch.Analysis.MontgomeryOrdinateResidual
