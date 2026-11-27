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

/-- The signed remainder for the complete ordinary ordinate form factor. -/
def signedArithmeticCorrection (T h : ℝ) : ℝ :=
  normalizedThirdAndPrimeOffDiagonal T h - signedHorizontalCorrection T h

/-- After removing the signed correction the ordinary form factor tends to the
diagonal slope at every fixed positive frequency. -/
theorem formFactor_sub_signedArithmeticCorrection_tendsto {h : ℝ} (hh : 0 < h) :
    Tendsto (fun T : ℝ => formFactor T h - signedArithmeticCorrection T h) atTop (𝓝 h) := by
  apply (sharpFormFactor_sub_normalizedThirdAndPrimeOffDiagonal_tendsto hh).congr'
  filter_upwards with T
  dsimp only [signedArithmeticCorrection]
  linarith only [sharp_sub_ordinate_eq T h]

/-- Identify the signed correction on the very same sequence of physical heights. -/
theorem signedArithmeticCorrection_tendsto_of_formFactor {T : ℕ → ℝ} {h s : ℝ}
    (hh : 0 < h) (hT : Tendsto T atTop atTop)
    (hF : Tendsto (fun n => formFactor (T n) h) atTop (𝓝 s)) :
    Tendsto (fun n => signedArithmeticCorrection (T n) h) atTop (𝓝 (s - h)) := by
  simpa only [Function.comp_def, sub_sub_cancel] using
    hF.sub ((formFactor_sub_signedArithmeticCorrection_tendsto hh).comp hT)

/-- A necessary and sufficient signed arithmetic condition at each fixed
positive frequency. This keeps the prime term and the horizontal term together. -/
theorem ordinateLimit_iff_signedArithmeticCorrection {α ℓ : ℝ} (hα : 0 < α) :
    Tendsto (fun T : ℝ => formFactor T α) atTop (𝓝 ℓ) ↔
    Tendsto (fun T : ℝ => normalizedThirdAndPrimeOffDiagonal T α -
      signedHorizontalCorrection T α) atTop (𝓝 (ℓ - α)) := by
  have hb : Tendsto (fun T : ℝ => formFactor T α -
      (normalizedThirdAndPrimeOffDiagonal T α - signedHorizontalCorrection T α))
      atTop (𝓝 α) := formFactor_sub_signedArithmeticCorrection_tendsto hα
  constructor
  · intro ho
    simpa only [sub_sub_cancel] using ho.sub hb
  · intro hc
    have h := hb.add hc
    rw [show α + (ℓ - α) = ℓ by ring] at h
    simpa only [sub_add_cancel] using h

end RiemannResearch.Analysis.MontgomeryOrdinateResidual
