import RiemannResearch.Analysis.RationalGaussianWindows
import RiemannResearch.RH.ActualZeroSpectralWindows
import RiemannResearch.RH.ActualZeroGaussianCells

/-!
# Actual marked zeta-copy rational Fourier-window mass

The form contains every analytic multiplicity copy in (T,2T], including
self-copy diagonal terms and distinct zero copies at the same height.
The rational kernel is exactly 4/(4+(γᵢ-γⱼ)^2). The unconditional finite
bound is by the actual square cell budget. Uniform normalization displays
the remaining actual Tsang cluster-square hypothesis explicitly.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.ActualZeroGaussianCells
open RiemannResearch.Analysis

/-- Literal original marked rational Fourier form on the complete actual shell. -/
def rationalForm (T scale q u α : ℝ) : ℂ :=
  MarkedLaplaceKernel.kernelForm (Finset.univ : Finset (ShellCopies T)) ordinate (q + scale * α) u

/-- Normalization by the full number of occurrences; no simplicity is assumed. -/
def normalizedRationalForm (T scale q u α : ℝ) : ℂ :=
  rationalForm T scale q u α / (Fintype.card (ShellCopies T) : ℂ)

/-- Genuine unnormalized actual unit-frequency absolute mass bound. -/
theorem rationalForm_unit_window_mass_le (T scale q u b : ℝ) :
    (∫ α in Set.Ico b (b + 1), ‖rationalForm T scale q u α‖) ≤
      (6 / GaussianSpectralWindows.windowFloor) * squareBudget T (scale / Real.sqrt 2) := by
  have h := RationalGaussianWindows.unit_window_absolute_marked_Ico_mass_le
    (Finset.univ : Finset (ShellCopies T)) ordinate q scale u b
  rw [spectral_squareBudget_eq] at h
  exact h

/-- Genuine normalized absolute mass bound, with the exact unresolved cell budget visible. -/
theorem normalizedRationalForm_unit_window_mass_le (T scale q u b : ℝ) :
    (∫ α in Set.Ico b (b + 1), ‖normalizedRationalForm T scale q u α‖) ≤
      ((6 / GaussianSpectralWindows.windowFloor) * squareBudget T (scale / Real.sqrt 2)) /
        (Fintype.card (ShellCopies T) : ℝ) := by
  simp_rw [normalizedRationalForm, norm_div, Complex.norm_natCast]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right (rationalForm_unit_window_mass_le T scale q u b)
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (ShellCopies T)) :
        0 ≤ (Fintype.card (ShellCopies T) : ℝ)))

/-- Conditional uniform actual marked Fourier-window mass.
The explicit cluster-square input is the only remaining number-theoretic premise. -/
theorem normalizedRationalForm_unit_window_mass_le_of_squareBudget
    (T scale q u b C : ℝ) (hM : 0 < Fintype.card (ShellCopies T))
    (hbudget : squareBudget T (scale / Real.sqrt 2) ≤
      C * (Fintype.card (ShellCopies T) : ℝ)) :
    (∫ α in Set.Ico b (b + 1), ‖normalizedRationalForm T scale q u α‖) ≤
      (6 / GaussianSpectralWindows.windowFloor) * C := by
  have hMR : 0 < (Fintype.card (ShellCopies T) : ℝ) := by exact_mod_cast hM
  calc
    _ ≤ ((6 / GaussianSpectralWindows.windowFloor) * squareBudget T (scale / Real.sqrt 2)) /
        (Fintype.card (ShellCopies T) : ℝ) := normalizedRationalForm_unit_window_mass_le T scale q u b
    _ ≤ ((6 / GaussianSpectralWindows.windowFloor) *
        (C * (Fintype.card (ShellCopies T) : ℝ))) / (Fintype.card (ShellCopies T) : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbudget
          (div_nonneg (by norm_num) GaussianSpectralWindows.windowFloor_pos.le)) hMR.le
    _ = _ := by field_simp

/-- For nonnegative shell heights, this normalization is exactly the analytic zero count. -/
theorem normalizedRationalForm_eq_Ncount (T scale q u α : ℝ) (hT : 0 ≤ T) :
    normalizedRationalForm T scale q u α =
      rationalForm T scale q u α / (Zeta23.Ncount T (2 * T) : ℂ) := by
  rw [normalizedRationalForm, card_shellCopies_eq_Ncount hT]

end RiemannResearch.RH.ActualZeroGaussianCells
