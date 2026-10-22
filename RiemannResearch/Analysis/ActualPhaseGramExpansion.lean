import RiemannResearch.Analysis.ActualLandauOperatorResidual
import Mathlib.Tactic.Abel

/-!
# Complete signed expansion of the actual ordinate Gram

Source: the corrected prime-phase note of 2026-10-11, Sections 5, 8 and 9.
The actual Landau provider and complete even horizontal correction are reused
without a density or RH premise. The exact identity keeps every integer
frequency, original analytic multiplicity, prime-power interaction and signed
bad-copy correction. The convergence equivalence isolates the complete
horizontal correction; it does not prove that correction tends to zero and
does not identify the ordinate Gram with the Pareto optimizer Gram.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open HorizontalPhaseBootstrap

/-- The ordinate Gram residual after retaining its signed arithmetic main. -/
def actualPhaseResidual (T : ℝ) (d : ℕ) : Space d →L[ℂ] Space d :=
  phaseGram T d - 1 +
    (T / ((2 * Real.pi) * (Zeta23.Ncount 0 T : ℝ))) • finPrimePowerMainOperator d

/-- Exact weight-removal identity, with no omitted horizontal correction. -/
theorem actualPhaseResidual_eq_landau_sub_correction (T : ℝ) (d : ℕ) :
    actualPhaseResidual T d =
      actualLandauResidual T d - (landauGram T d - phaseGram T d) := by
  unfold actualPhaseResidual actualLandauResidual
  abel

/-- The arithmetic main, complete even series and complementary bad part
are all retained with their original signs. -/
theorem phaseGram_eq_complete_signed_expansion
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ) :
    phaseGram T d =
      1 - (T / ((2 * Real.pi) * (Zeta23.Ncount 0 T : ℝ))) •
          finPrimePowerMainOperator d + actualLandauResidual T d -
        (∑' k, evenTerm (logDiagonal d) (goodMoment T d δ) k) -
        badCorrection T d δ := by
  have h := landauGram_sub_phaseGram T d hd δ hδ
  rw [sub_eq_iff_eq_add] at h
  unfold actualLandauResidual
  rw [h]
  abel

/-- The smaller good-copy Gram controls only the good correction; the signed
bad term and the full arithmetic Landau residual remain explicit. -/
theorem actualPhaseResidual_norm_le
    (T : ℝ) (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖actualPhaseResidual T d‖ ≤ ‖actualLandauResidual T d‖ +
      (‖goodMoment T d δ 0‖ / 2) *
        (Real.cosh (δ * Real.log (d : ℝ)) - 1) + ‖badCorrection T d δ‖ := by
  rw [actualPhaseResidual_eq_landau_sub_correction]
  calc
    _ ≤ ‖actualLandauResidual T d‖ + ‖landauGram T d - phaseGram T d‖ :=
      norm_sub_le _ _
    _ ≤ _ := by
      have h := norm_landauGram_sub_phaseGram_le_zeroth T d hd δ hδ
      linarith

/-- Necessary and sufficient correction smallness when the actual signed
Landau residual vanishes. This scalar equivalence allows changing dimensions. -/
theorem actualPhaseResidual_tendsto_zero_iff_correction
    (d : ℝ → ℕ)
    (hL : Tendsto (fun T => ‖actualLandauResidual T (d T)‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖actualPhaseResidual T (d T)‖) atTop (nhds 0) ↔
      Tendsto (fun T => ‖landauGram T (d T) - phaseGram T (d T)‖)
        atTop (nhds 0) := by
  constructor
  · intro hP
    have hmajor := hL.add hP
    simp only [add_zero] at hmajor
    apply squeeze_zero (fun T => norm_nonneg _) _ hmajor
    intro T
    have he : landauGram T (d T) - phaseGram T (d T) =
        actualLandauResidual T (d T) - actualPhaseResidual T (d T) := by
      rw [actualPhaseResidual_eq_landau_sub_correction]
      abel
    rw [he]
    exact norm_sub_le _ _
  · intro hC
    have hmajor := hL.add hC
    simp only [add_zero] at hmajor
    apply squeeze_zero (fun T => norm_nonneg _) _ hmajor
    intro T
    rw [actualPhaseResidual_eq_landau_sub_correction]
    exact norm_sub_le _ _

/-- The existing unconditional actual-zero Landau theorem discharges the
Landau premise under its explicit elementary growing-support budget. -/
theorem actualPhaseResidual_tendsto_zero_iff_correction_of_leading_budget
    (d : ℝ → ℕ) (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hbudget : Tendsto (fun T : ℝ => (d T : ℝ) ^ (7 / 2 : ℝ) /
      ((T + 3) * Real.log (T + 3))) atTop (nhds 0)) :
    Tendsto (fun T => ‖actualPhaseResidual T (d T)‖) atTop (nhds 0) ↔
      Tendsto (fun T => ‖landauGram T (d T) - phaseGram T (d T)‖)
        atTop (nhds 0) := by
  exact actualPhaseResidual_tendsto_zero_iff_correction d
    (actualLandauResidual_norm_tendsto_zero_of_leading_budget d hd hbudget)

end RiemannResearch.Analysis.ActualZeroPhaseMoments
end
