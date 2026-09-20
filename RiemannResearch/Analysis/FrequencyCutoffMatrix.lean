import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

/-!
# Finite Hermitian frequency regularization

Source: user-provided Hilbert--Polya discussion, 2026-09-20. This is the
finite cutoff integral construction. Hermitian symmetry follows from the
real frequency multiplier. No identification with zeta zeros is asserted.
-/

noncomputable section
open MeasureTheory
namespace RiemannResearch.Analysis.FrequencyCutoff

variable {ι : Type*}

def matrix (ψ : ι → ℝ → ℂ) (R : ℝ) : Matrix ι ι ℂ :=
  fun i j => ∫ t in Set.Icc (-R) R,
    ((t / (2 * Real.pi) : ℝ) : ℂ) * star (ψ i t) * ψ j t

theorem entry_integrable (ψ : ι → ℝ → ℂ) (hψ : ∀ i, Continuous (ψ i))
    (R : ℝ) (i j : ι) :
    IntegrableOn (fun t =>
      ((t / (2 * Real.pi) : ℝ) : ℂ) * star (ψ i t) * ψ j t)
      (Set.Icc (-R) R) := by
  apply Continuous.integrableOn_Icc
  exact ((Complex.continuous_ofReal.comp
    (continuous_id.div_const (2 * Real.pi))).mul (hψ i).star).mul (hψ j)

theorem matrix_isHermitian (ψ : ι → ℝ → ℂ) (R : ℝ) :
    (matrix ψ R).IsHermitian := by
  change (matrix ψ R).conjTranspose = matrix ψ R
  ext i j
  change (starRingEnd ℂ)
      (∫ t in Set.Icc (-R) R,
        ((t / (2 * Real.pi) : ℝ) : ℂ) * star (ψ j t) * ψ i t) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- Every spectral value of each finite regularization is real. This
contains no assertion relating those values to the completed zeta function. -/
theorem spectrum_im_eq_zero [Fintype ι] [DecidableEq ι]
    (ψ : ι → ℝ → ℂ) (R : ℝ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (matrix ψ R)) : z.im = 0 := by
  rw [(matrix_isHermitian ψ R).spectrum_eq_image_range] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  simp

end RiemannResearch.Analysis.FrequencyCutoff
