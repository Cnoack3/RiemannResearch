import RiemannResearch.RH.ResidueCorrectionAbel
import RiemannResearch.RH.ResidueDualDifferences
import RiemannResearch.RH.ResidueCorrectionAbelLimits

/-!
# Signed progression sampling at exact zero endpoints

Source: the signed physical-tail target in AnthropicRHBridges20260928.md.
The first Abel interior is written with the actual signed inverse-Gram column.
A common conductor multiple removes its boundary exactly. These are finite
identities; smallness of the resulting signed discrepancy remains Open.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
open GramMobiusCorrection
open RiemannResearch.Analysis.SignedAbel

/-- The whole signed inverse-column pairing with centered progression samples. -/
def correctionDivisorAbelValue (n d M : ℕ) : ℝ :=
  ∑ i : Fin n, projectedDualColumn n d i * divisorSamplingDiscrepancy
    (i.val + 2) (n + 1) M (primitive (correctionTailWeight n))

theorem projectedDualSequence_eq_physical (n d k : ℕ) :
    projectedDualSequence n d k = projectedDualPhysical n d (n + 1 + k) := by
  unfold projectedDualSequence projectedDualPhysical
  congr 1
  omega

/-- Exact first Abel identity, retaining the full boundary and all signed samples. -/
theorem correctionAbelValue_eq_divisor_boundary (n d M : ℕ) :
    correctionAbelValue n d M =
      primitive (correctionTailWeight n) M * projectedDualPhysical n d (n + M + 1) +
        correctionDivisorAbelValue n d M := by
  have hs : (∑ k ∈ Finset.range M, primitive (correctionTailWeight n) (k + 1) *
      difference (projectedDualSequence n d) k) =
        -correctionDivisorAbelValue n d M := by
    simpa only [correctionDivisorAbelValue, difference,
      projectedDualSequence_eq_physical, Nat.add_assoc] using
      projectedDualPhysical_weighted_forward n d (n + 1) M
        (primitive (correctionTailWeight n))
  unfold correctionAbelValue value
  rw [hs, projectedDualSequence_eq_physical]
  rw [show n + 1 + M = n + M + 1 by omega]
  ring

/-- At a common conductor multiple the Abel boundary vanishes, not merely decays. -/
theorem correctionAbelValue_eq_divisor_of_common_multiple (n d M : ℕ)
    (hM : ∀ i : Fin n, i.val + 2 ∣ n + M + 1) :
    correctionAbelValue n d M = correctionDivisorAbelValue n d M := by
  rw [correctionAbelValue_eq_divisor_boundary,
    projectedDualPhysical_eq_zero_of_common_multiple n d (n + M + 1) hM]
  ring

theorem correctionShellValue_eq_divisor_of_common_multiple (n d M : ℕ)
    (hM : ∀ i : Fin n, i.val + 2 ∣ n + M + 1) :
    correctionShellValue n d M = correctionDivisorAbelValue n d M := by
  unfold correctionShellValue
  rw [correction_shell_abel]
  exact correctionAbelValue_eq_divisor_of_common_multiple n d M hM

/-- The complete correction is the pure signed progression value plus both entire
later tails; the zero-endpoint restriction loses no mixed or boundary term. -/
theorem correction_eq_divisor_add_tail (n d M : ℕ) (hd : 1 < d) (hdn : d ≤ n)
    (hM : ∀ i : Fin n, i.val + 2 ∣ n + M + 1) :
    correction n d = correctionDivisorAbelValue n d M +
      inner ℝ
        (hilbertTailShift ((finiteSpace n).starProjection (coefficientRiesz d)) (n + M))
        (hilbertTailShift (tailError n) (n + M)) := by
  rw [← correctionAbelValue_eq_divisor_of_common_multiple n d M hM]
  exact correction_eq_abel_add_tail n d M hd hdn

/-- The enlarged certified cutoff is a zero endpoint, giving a pure signed
arithmetic progression expression with no boundary contribution. -/
theorem correctionPeriodValue_eq_divisor (n d : ℕ) :
    correctionPeriodValue n d =
      correctionDivisorAbelValue n d (correctionPeriodCutoff n d) := by
  unfold correctionPeriodValue
  apply correctionShellValue_eq_divisor_of_common_multiple
  intro i
  have he : i.val + 2 ∣ (n + 1).factorial :=
    Nat.dvd_factorial (by omega) (by omega)
  have h := he.trans (correctionPeriodCutoff_endpoint_dvd n d)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Certified error for the pure signed progression expression. -/
theorem correction_sub_period_divisor_sq_le (n d : ℕ) (hd : 1 < d) (hdn : d ≤ n) :
    |correction n d - correctionDivisorAbelValue n d (correctionPeriodCutoff n d)| ^ 2 ≤
      1 / ((n : ℝ) + 1) := by
  rw [← correctionPeriodValue_eq_divisor]
  exact correction_sub_period_sq_le n d hd hdn

/-- The signed progression values have the same possibly nonzero limit as
the actual inverse-Gram correction. -/
theorem correctionPeriodDivisor_tendsto (d : ℕ) (hd : 1 < d) :
    Tendsto (fun n => correctionDivisorAbelValue n d (correctionPeriodCutoff n d))
      atTop (𝓝 (mobiusDifferenceCLM d limitResidual)) := by
  simpa only [correctionPeriodValue_eq_divisor] using correctionPeriodValue_tendsto d hd

/-- CONDITIONAL RESEARCH REDUCTION: cofinal smallness of the signed inverse-column
pairing with centered progression samples implies RH. No provider is asserted;
the cofinal indices may depend on both the conductor and the requested accuracy. -/
theorem riemannHypothesis_of_cofinal_period_divisor
    (hsmall : ∀ d : ℕ, 1 < d → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |correctionDivisorAbelValue n d (correctionPeriodCutoff n d)| < ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_period
  intro d hd ε hε
  simpa only [correctionPeriodValue_eq_divisor] using hsmall d hd ε hε

end RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail
