import RiemannResearch.Analysis.GaussianSpectralWindows
import RiemannResearch.Analysis.GaussianAbsoluteWindowMass
import RiemannResearch.RH.ActualZeroGaussianCells

/-! Actual zeta-copy Gaussian unit spectral windows, preserving multiplicities. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.ActualZeroGaussianCells
open RiemannResearch.Analysis

/-- Actual angular amplitude over the complete zero-copy shell. -/
def spectralAmplitude (T scale q t : ℝ) : ℂ :=
  GaussianSpectralWindows.amplitude (Finset.univ : Finset (ShellCopies T))
    (fun c => scale * ordinate c) q t

/-- Exact rescaling of the characteristic-kernel cells to the actual copy budget. -/
theorem spectral_squareBudget_eq (T scale : ℝ) :
    GaussianSpectralWindows.squareBudget (Finset.univ : Finset (ShellCopies T))
      (fun c => scale * ordinate c) = squareBudget T (scale / Real.sqrt 2) := by
  have hf : (fun c : ShellCopies T => Int.floor ((scale * ordinate c) / Real.sqrt 2)) =
      (fun c : ShellCopies T => Int.floor ((scale / Real.sqrt 2) * ordinate c)) := by
    funext c
    congr 1
    ring
  simp only [GaussianSpectralWindows.squareBudget, squareBudget, cells, cellOccupancy, hf]

/-- Unconditional finite actual unit-window mass bound in terms of square occupancies. -/
theorem spectral_unit_window_energy_le (T scale q b : ℝ) :
    (∫ t in Set.Ico b (b + 1), ‖spectralAmplitude T scale q t‖ ^ 2) ≤
      (6 / GaussianSpectralWindows.windowFloor) * squareBudget T (scale / Real.sqrt 2) := by
  have h := GaussianSpectralWindows.unit_window_energy_Ico_le
    (Finset.univ : Finset (ShellCopies T)) (fun c => scale * ordinate c) q b
  rw [spectral_squareBudget_eq] at h
  exact h

/-- Actual marked spectral Cauchy estimate; all copies and equal heights remain. -/
theorem spectral_unit_window_marked_norm_le (T scale q u b : ℝ) :
    ‖∫ t in Set.Ico b (b + 1),
      spectralAmplitude T scale (q + u) t * star (spectralAmplitude T scale q t)‖ ≤
        (6 / GaussianSpectralWindows.windowFloor) * squareBudget T (scale / Real.sqrt 2) := by
  have h := GaussianSpectralWindows.unit_window_marked_Ico_norm_le
    (Finset.univ : Finset (ShellCopies T)) (fun c => scale * ordinate c) q u b
  rw [spectral_squareBudget_eq] at h
  exact h

/-- Uniform actual normalized mass from the explicit unresolved cluster budget. -/
theorem normalized_spectral_unit_window_energy_le_of_squareBudget
    (T scale q b C : ℝ) (hM : 0 < Fintype.card (ShellCopies T))
    (hbudget : squareBudget T (scale / Real.sqrt 2) ≤
      C * (Fintype.card (ShellCopies T) : ℝ)) :
    (∫ t in Set.Ico b (b + 1), ‖spectralAmplitude T scale q t‖ ^ 2) /
      (Fintype.card (ShellCopies T) : ℝ) ≤ (6 / GaussianSpectralWindows.windowFloor) * C := by
  rw [← integral_Icc_eq_integral_Ico]
  have hb : GaussianSpectralWindows.squareBudget (Finset.univ : Finset (ShellCopies T))
      (fun c => scale * ordinate c) ≤ C * ((Finset.univ : Finset (ShellCopies T)).card : ℝ) := by
    simpa only [spectral_squareBudget_eq, Finset.card_univ] using hbudget
  simpa only [spectralAmplitude, Finset.card_univ] using
    GaussianSpectralWindows.normalized_unit_window_energy_le_of_squareBudget
      (Finset.univ : Finset (ShellCopies T)) (fun c => scale * ordinate c) q b C
      (by simpa only [Finset.card_univ] using hM) hb


open RiemannResearch.Analysis
open scoped BigOperators

/-- Unconditional actual finite-copy absolute mass bound, before the Tsang input. -/
theorem spectral_unit_window_absolute_marked_mass_le (T scale q u b : ℝ) :
    (∫ t in Set.Ico b (b + 1),
      ‖spectralAmplitude T scale (q + u) t * star (spectralAmplitude T scale q t)‖) ≤
        (6 / GaussianSpectralWindows.windowFloor) * squareBudget T (scale / Real.sqrt 2) := by
  have h := GaussianSpectralWindows.unit_window_absolute_marked_Ico_mass_le
    (Finset.univ : Finset (ShellCopies T)) (fun c => scale * ordinate c) q u b
  rw [spectral_squareBudget_eq] at h
  exact h

/-- Uniform actual absolute spectral mass with the precise remaining budget displayed. -/
theorem normalized_spectral_unit_window_absolute_marked_mass_le_of_squareBudget
    (T scale q u b C : ℝ) (hM : 0 < Fintype.card (ShellCopies T))
    (hbudget : squareBudget T (scale / Real.sqrt 2) ≤
      C * (Fintype.card (ShellCopies T) : ℝ)) :
    (∫ t in Set.Ico b (b + 1),
      ‖spectralAmplitude T scale (q + u) t * star (spectralAmplitude T scale q t)‖) /
      (Fintype.card (ShellCopies T) : ℝ) ≤ (6 / GaussianSpectralWindows.windowFloor) * C := by
  have hMR : 0 < (Fintype.card (ShellCopies T) : ℝ) := by exact_mod_cast hM
  calc
    _ ≤ ((6 / GaussianSpectralWindows.windowFloor) * squareBudget T (scale / Real.sqrt 2)) /
        (Fintype.card (ShellCopies T) : ℝ) :=
      div_le_div_of_nonneg_right (spectral_unit_window_absolute_marked_mass_le T scale q u b) hMR.le
    _ ≤ ((6 / GaussianSpectralWindows.windowFloor) *
        (C * (Fintype.card (ShellCopies T) : ℝ))) / (Fintype.card (ShellCopies T) : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbudget
          (div_nonneg (by norm_num) GaussianSpectralWindows.windowFloor_pos.le)) hMR.le
    _ = _ := by field_simp


end RiemannResearch.RH.ActualZeroGaussianCells
