import RiemannResearch.RH.ActualMarkedRationalWindows
import RiemannResearch.Analysis.MarkedContinuousTail

/-!
# Literal original marked Fourier tails for actual zeta-copy shells

The finite-shell result is unconditional, with its exact square occupancy
budget retained. Uniformity in shell height is a separate consumer of the
explicit actual cluster-square premise. This module does not silently use
ordinary local zero counts to supply a Tsang second moment.
-/
noncomputable section
open MeasureTheory

namespace RiemannResearch.RH.ActualZeroGaussianCells
open RiemannResearch.Analysis
open TentFourierInversion MarkedFourierTail

/-- The literal complete normalized marked Fourier form is continuous. -/
theorem normalizedRationalForm_continuous (T scale q u : ℝ) :
    Continuous (normalizedRationalForm T scale q u) := by
  unfold normalizedRationalForm rationalForm MarkedLaplaceKernel.kernelForm MarkedLaplaceKernel.phase
  fun_prop

/-- The actual occurrence budget is nonnegative, including empty shells. -/
theorem squareBudget_nonneg (T scale : ℝ) : 0 ≤ squareBudget T scale := by
  unfold squareBudget
  exact Finset.sum_nonneg (fun a _ => sq_nonneg _)

/-- Unconditional finite-shell absolute Fourier tail with an exact occupancy constant.
The division is totalized when the shell has no zero copies. -/
theorem normalizedRationalForm_absolute_tail_integrable_and_le
    (T scale q u v : ℝ) {B : ℝ} (hB : 1 ≤ B) :
    IntegrableOn
      (fun α => tentTransform v α * ‖normalizedRationalForm T scale q u α‖)
      {α : ℝ | B ≤ |α|} ∧
    (∫ α in {α : ℝ | B ≤ |α|},
      tentTransform v α * ‖normalizedRationalForm T scale q u α‖) ≤
        24 * squareBudget T (scale / Real.sqrt 2) /
          (GaussianSpectralWindows.windowFloor * (Fintype.card (ShellCopies T) : ℝ) *
            Real.pi ^ 2 * B) := by
  let D : ℝ := ((6 / GaussianSpectralWindows.windowFloor) *
    squareBudget T (scale / Real.sqrt 2)) / (Fintype.card (ShellCopies T) : ℝ)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (mul_nonneg
      (div_nonneg (by norm_num) GaussianSpectralWindows.windowFloor_pos.le)
      (squareBudget_nonneg _ _)) (Nat.cast_nonneg _)
  have hw : ∀ a : ℝ, (∫ α in Set.Ico a (a + 1),
      ‖normalizedRationalForm T scale q u α‖) ≤ D :=
    fun a => normalizedRationalForm_unit_window_mass_le T scale q u a
  have h := MarkedContinuousTail.two_sided_tail_integrable_and_le
    (normalizedRationalForm T scale q u) (normalizedRationalForm_continuous T scale q u)
    v hB hD hw
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp [D]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Literal signed complex tail: absolute convergence and the same finite-shell bound. -/
theorem normalizedRationalForm_tail_integrable_and_norm_le
    (T scale q u v : ℝ) {B : ℝ} (hB : 1 ≤ B) :
    IntegrableOn
      (fun α => (tentTransform v α : ℂ) * normalizedRationalForm T scale q u α)
      {α : ℝ | B ≤ |α|} ∧
    ‖∫ α in {α : ℝ | B ≤ |α|},
      (tentTransform v α : ℂ) * normalizedRationalForm T scale q u α‖ ≤
        24 * squareBudget T (scale / Real.sqrt 2) /
          (GaussianSpectralWindows.windowFloor * (Fintype.card (ShellCopies T) : ℝ) *
            Real.pi ^ 2 * B) := by
  have habs := normalizedRationalForm_absolute_tail_integrable_and_le T scale q u v hB
  have hnorm (α : ℝ) :
      ‖(tentTransform v α : ℂ) * normalizedRationalForm T scale q u α‖ =
        tentTransform v α * ‖normalizedRationalForm T scale q u α‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tentTransform_nonneg v α)]
  have hm : AEStronglyMeasurable
      (fun α => (tentTransform v α : ℂ) * normalizedRationalForm T scale q u α)
      (volume.restrict {α : ℝ | B ≤ |α|}) := by
    apply Measurable.aestronglyMeasurable
    exact ((tentTransform_measurable v).complex_ofReal.mul
      (normalizedRationalForm_continuous T scale q u).measurable)
  have hi : IntegrableOn
      (fun α => (tentTransform v α : ℂ) * normalizedRationalForm T scale q u α)
      {α : ℝ | B ≤ |α|} := habs.1.mono' hm
        (Filter.Eventually.of_forall (fun α => (hnorm α).le))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ α in {α : ℝ | B ≤ |α|},
        ‖(tentTransform v α : ℂ) * normalizedRationalForm T scale q u α‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ α in {α : ℝ | B ≤ |α|},
        tentTransform v α * ‖normalizedRationalForm T scale q u α‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hnorm
    _ ≤ _ := habs.2

/-- Uniform actual absolute tail consumer; the known unconditional Tsang theorem
still requires a separate checked provider for this precise actual budget. -/
theorem normalizedRationalForm_absolute_tail_le_of_squareBudget
    (T scale q u v C : ℝ) {B : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hM : 0 < Fintype.card (ShellCopies T))
    (hbudget : squareBudget T (scale / Real.sqrt 2) ≤
      C * (Fintype.card (ShellCopies T) : ℝ)) :
    IntegrableOn
      (fun α => tentTransform v α * ‖normalizedRationalForm T scale q u α‖)
      {α : ℝ | B ≤ |α|} ∧
    (∫ α in {α : ℝ | B ≤ |α|},
      tentTransform v α * ‖normalizedRationalForm T scale q u α‖) ≤
        24 * C / (GaussianSpectralWindows.windowFloor * Real.pi ^ 2 * B) := by
  have hD : 0 ≤ (6 / GaussianSpectralWindows.windowFloor) * C :=
    mul_nonneg (div_nonneg (by norm_num) GaussianSpectralWindows.windowFloor_pos.le) hC
  have hw : ∀ a : ℝ, (∫ α in Set.Ico a (a + 1),
      ‖normalizedRationalForm T scale q u α‖) ≤
        (6 / GaussianSpectralWindows.windowFloor) * C :=
    fun a => normalizedRationalForm_unit_window_mass_le_of_squareBudget T scale q u a C hM hbudget
  have h := MarkedContinuousTail.two_sided_tail_integrable_and_le
    (normalizedRationalForm T scale q u) (normalizedRationalForm_continuous T scale q u)
    v hB hD hw
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end RiemannResearch.RH.ActualZeroGaussianCells
