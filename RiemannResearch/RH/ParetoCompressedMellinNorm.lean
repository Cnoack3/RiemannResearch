import RiemannResearch.RH.ParetoMellinObstructionTargets
import RiemannResearch.RH.ParetoCompressedMellinSummability
import Mathlib.Analysis.Complex.Exponential

/-!
# Exact complete norm of compressed Mellin cells

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 3.1.  This module supplies `FullCosineIdentity` from the actual complex
cell formula. The mixed cosine term and the complete infinite Pareto tail are
retained exactly. It does not supply the phase-derivative or resonance providers.
-/

namespace RiemannResearch.RH.Pareto.CompressedMellin
noncomputable section
open scoped BigOperators

private theorem exp_I_mul_re (x : ℝ) :
    (Complex.exp (Complex.I * (x : ℂ))).re = Real.cos x := by
  rw [Complex.exp_re]
  simp

private theorem exp_I_mul_im (x : ℝ) :
    (Complex.exp (Complex.I * (x : ℂ))).im = Real.sin x := by
  rw [Complex.exp_im]
  simp

/-- Exact complex phase-difference norm, including its signed mixed term. -/
theorem norm_phase_difference_sq (a b x y : ℝ) :
    ‖(a : ℂ) * Complex.exp (Complex.I * (x : ℂ)) -
      (b : ℂ) * Complex.exp (Complex.I * (y : ℂ))‖ ^ 2 =
    a ^ 2 + b ^ 2 - 2 * a * b * Real.cos (x - y) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_sub, sub_zero, zero_add,
    add_zero, exp_I_mul_re, exp_I_mul_im]
  convert phase_difference_square a b x y using 1 <;> ring

private theorem norm_mellin_denominator_sq (t : ℝ) :
    ‖(1 : ℂ) - Complex.I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  <;> ring

private theorem cell_log_increment (n : ℕ) :
    Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) =
      Real.log (1 + 1 / ((n : ℝ) + 1)) := by
  have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  rw [← Real.log_div h₂ h₁]
  congr 1
  field_simp
  <;> ring

/-- The exact weighted square of every actual compressed Mellin cell. -/
theorem compressedMellinCell_weighted_square (t : ℝ) (n : ℕ) :
    paretoWeight n * ‖compressedMellinCell t n‖ ^ 2 =
      cellDensity t n / (1 + t ^ 2) := by
  have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  have hphase : t * Real.log ((n : ℝ) + 1) - t * Real.log ((n : ℝ) + 2) =
      -(t * Real.log (1 + 1 / ((n : ℝ) + 1))) := by
    rw [← cell_log_increment n]
    ring
  unfold compressedMellinCell
  rw [norm_div, div_pow, norm_phase_difference_sq, norm_mellin_denominator_sq,
    hphase, Real.cos_neg]
  unfold paretoWeight cellDensity
  field_simp
  <;> ring

theorem cellDensity_summable (t : ℝ) : Summable (cellDensity t) := by
  exact (paretoWeight_hasSum.summable.add
    ((cosineDeficit_summable t).mul_left 2)).congr
    (fun n => (cellDensity_eq t n).symm)

/-- Summability of the actual weighted complex-cell squares. -/
theorem compressedMellinCell_square_summable (t : ℝ) :
    Summable (fun n => paretoWeight n * ‖compressedMellinCell t n‖ ^ 2) := by
  exact ((cellDensity_summable t).div_const (1 + t ^ 2)).congr
    (fun n => (compressedMellinCell_weighted_square t n).symm)

/-- The complete compressed Mellin energy has the exact cosine representation. -/
theorem compressedMellinEnergy_eq (t : ℝ) :
    compressedMellinEnergy t = cosineMass t / (1 + t ^ 2) := by
  unfold compressedMellinEnergy
  simp_rw [compressedMellinCell_weighted_square]
  rw [tsum_div_const, tsum_cellDensity_unconditional]

/-- Provider for the named exact cosine-norm identity. -/
theorem fullCosineIdentity : FullCosineIdentity := by
  intro t
  exact ⟨cosineDeficit_summable t, compressedMellinCell_square_summable t,
    compressedMellinEnergy_eq t⟩

end
end RiemannResearch.RH.Pareto.CompressedMellin
