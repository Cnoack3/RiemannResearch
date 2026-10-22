import RiemannResearch.Analysis.SignedAbel
import RiemannResearch.RH.ResidueProjectionCorrectionTail

/-!
# Signed Abel formulas for the actual inverse-Gram correction

Source: user-provided `AnthropicRHBridges20260928.md`, section 1, for
the physical-coordinate summation-by-parts strategy. All identities use
the actual canonical arithmetic tail and projected coefficient dual.
The complete later tails are retained. No RH hypothesis is used.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open GramMobiusCorrection
open RiemannResearch.Analysis.SignedAbel

def correctionTailWeight (n k : ℕ) : ℝ :=
  positiveWeight (k+n+1) * hilbertSequence (tailError n) (k+n+1)

def projectedDualSequence (n d k : ℕ) : ℝ :=
  hilbertSequence ((finiteSpace n).starProjection (coefficientRiesz d)) (k+n+1)

def correctionAbelValue (n d M : ℕ) : ℝ :=
  value (correctionTailWeight n) (projectedDualSequence n d) M

def correctionAbelSecondValue (n d M : ℕ) : ℝ :=
  secondValue (correctionTailWeight n) (projectedDualSequence n d) M

theorem correction_shell_abel (n d M : ℕ) :
    hilbertShellPairing ((finiteSpace n).starProjection (coefficientRiesz d))
      (tailError n) n M = correctionAbelValue n d M := by
  rw [hilbertShellPairing_weighted]
  unfold correctionAbelValue
  rw [← sum_eq_value]
  apply Finset.sum_congr rfl
  intro k hk
  unfold correctionTailWeight projectedDualSequence
  ring

theorem correction_shell_abel_second (n d M : ℕ) :
    hilbertShellPairing ((finiteSpace n).starProjection (coefficientRiesz d))
      (tailError n) n M = correctionAbelSecondValue n d M := by
  rw [correction_shell_abel]
  exact value_eq_secondValue _ _ _

theorem correction_eq_abel_add_tail (n d M : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    correction n d = correctionAbelValue n d M +
      inner ℝ
        (hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) (n+M))
        (hilbertTailShift (tailError n) (n+M)) := by
  rw [← correction_shell_abel]
  exact correction_signed_shell_split n d M hd hdn

theorem correction_eq_abel_second_add_tail (n d M : ℕ)
    (hd : 1 < d) (hdn : d ≤ n) :
    correction n d = correctionAbelSecondValue n d M +
      inner ℝ
        (hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) (n+M))
        (hilbertTailShift (tailError n) (n+M)) := by
  rw [← correction_shell_abel_second]
  exact correction_signed_shell_split n d M hd hdn

theorem correction_abs_le_abel_second_tail (n d M : ℕ)
    (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d| ≤ |correctionAbelSecondValue n d M| +
      ‖hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) (n+M)‖ *
      ‖hilbertTailShift (tailError n) (n+M)‖ := by
  rw [correction_eq_abel_second_add_tail n d M hd hdn]
  exact (abs_add_le _ _).trans
    (add_le_add le_rfl (abs_real_inner_le_norm _ _))

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
