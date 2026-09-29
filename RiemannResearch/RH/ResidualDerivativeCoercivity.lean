/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ResidueDerivativeCompatibility
import RiemannResearch.RH.ResidueDerivativeOptimization
import RiemannResearch.RH.FiniteDyadicDefect

/-!
# Exact canonical derivative coercivity

The anchored first site and the complete normalized-dilation remainder give
an exact four-term decomposition of the limiting derivative energy. This is
specific to the actual canonical projection residual. It is not a bounded
inverse theorem for differentiation, and it does not prove vanishing.

Source: the user-directed vanishing attempt, continuing
`CRTPrimitiveTransferAudit20260929.md`, Section 6, and the existing
repository dyadic and arithmetic identities.
-/

noncomputable section
open scoped Topology
open Filter

namespace RiemannResearch.RH.Pareto

/-- The exact first-site orthogonal split, retaining the complete derivative tail. -/
theorem hilbertDifference_first_site_split (f : ThresholdHilbert) :
    ‖hilbertDifference f‖ ^ 2 = (hilbertSequence f 1) ^ 2 / 2 +
      ‖hilbertDifference f - hilbertSequence f 1 • hilbertAtom 1 (by decide)‖ ^ 2 := by
  have hi : inner ℝ (hilbertDifference f) (hilbertAtom 1 (by decide)) =
      hilbertSequence f 1 / 2 := by
    rw [real_inner_comm, hilbertAtom_inner, hilbertDifference_sequence]
    simp [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift, positiveWeight]
    ring
  have h := norm_sub_sq_real (hilbertDifference f)
    (hilbertSequence f 1 • hilbertAtom 1 (by decide))
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    CRTPrimitiveEscape.target_atom_one_norm_sq, real_inner_smul_right, hi] at h
  linarith

namespace CoefficientStabilization.DerivativeCompatibility

def residualDerivativeTail : ThresholdHilbert :=
  hilbertDifference limitResidual -
    hilbertSequence limitResidual 1 • hilbertAtom 1 (by decide)

def residualDyadicRemainder : ℝ :=
  ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2

/-- No signed term or norm-square remainder is dropped. -/
theorem derivative_limit_exact_four_terms :
    ‖hilbertDifference limitResidual‖ ^ 2 =
      (3 - 2 * Real.sqrt 2) * limitEnergy ^ 2 +
      (Real.sqrt 2 - 1) * limitEnergy * residualDyadicRemainder +
      residualDyadicRemainder ^ 2 / 4 + ‖residualDerivativeTail‖ ^ 2 := by
  have h := hilbertDifference_first_site_split limitResidual
  change ‖hilbertDifference limitResidual‖ ^ 2 =
    (hilbertSequence limitResidual 1) ^ 2 / 2 + ‖residualDerivativeTail‖ ^ 2 at h
  rw [firstCoordinate_eq_energy_add_dyadicRemainder] at h
  change ‖hilbertDifference limitResidual‖ ^ 2 =
    ((2 - Real.sqrt 2) * limitEnergy +
      (Real.sqrt 2 / 2) * residualDyadicRemainder) ^ 2 / 2 +
      ‖residualDerivativeTail‖ ^ 2 at h
  rw [h]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Nonlinear coercivity of the actual limiting residual; all omitted terms
in this inequality are displayed in `derivative_limit_exact_four_terms`. -/
theorem canonical_derivative_nonlinear_coercivity :
    (3 - 2 * Real.sqrt 2) * limitEnergy ^ 2 ≤
      ‖hilbertDifference limitResidual‖ ^ 2 := by
  rw [derivative_limit_exact_four_terms]
  have hs : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have he : 0 ≤ limitEnergy := sq_nonneg _
  have hr : 0 ≤ residualDyadicRemainder := sq_nonneg _
  have hm : 0 ≤ (Real.sqrt 2 - 1) * limitEnergy * residualDyadicRemainder :=
    mul_nonneg (mul_nonneg (by linarith) he) hr
  nlinarith [sq_nonneg residualDyadicRemainder, sq_nonneg ‖residualDerivativeTail‖]

/-- Explicit inversion of the nonlinear estimate, with constant 3+2√2. -/
theorem canonical_energy_sq_le_derivative_energy :
    limitEnergy ^ 2 ≤ (3 + 2 * Real.sqrt 2) *
      ‖hilbertDifference limitResidual‖ ^ 2 := by
  have h := mul_le_mul_of_nonneg_left canonical_derivative_nonlinear_coercivity
    (show 0 ≤ 3 + 2 * Real.sqrt 2 by positivity)
  have hc : (3 + 2 * Real.sqrt 2) * (3 - 2 * Real.sqrt 2) = 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [← mul_assoc, hc, one_mul] using h

/-- A finite certificate retains both the derivative compatibility cost and
the complete outstanding projection gap. Neither is declared zero. -/
theorem canonical_energy_sq_le_finite_compatibility (n : ℕ) :
    limitEnergy ^ 2 ≤ 2 * (3 + 2 * Real.sqrt 2) *
      (derivativeBestError n + mismatchEnergy n + (energy n - limitEnergy)) := by
  have hfirst := hilbertDifference_first_site_split limitResidual
  have hfull := derivative_limit_exact_four_terms
  have hs : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have he : 0 ≤ limitEnergy := sq_nonneg _
  have hr : 0 ≤ residualDyadicRemainder := sq_nonneg _
  have hm : 0 ≤ (Real.sqrt 2 - 1) * limitEnergy * residualDyadicRemainder :=
    mul_nonneg (mul_nonneg (by linarith) he) hr
  change ‖hilbertDifference limitResidual‖ ^ 2 =
    (hilbertSequence limitResidual 1) ^ 2 / 2 + ‖residualDerivativeTail‖ ^ 2 at hfirst
  have hlower : (3 - 2 * Real.sqrt 2) * limitEnergy ^ 2 ≤
      (hilbertSequence limitResidual 1) ^ 2 / 2 := by
    nlinarith [sq_nonneg residualDyadicRemainder]
  have hseq : hilbertSequence limitResidual 1 =
      hilbertSequence (projectionResidual n) 1 -
        hilbertSequence (limitProjection - projection n) 1 := by
    have hv : limitResidual = projectionResidual n - (limitProjection - projection n) := by
      unfold limitResidual projectionResidual
      abel
    rw [hv, hilbertSequence_sub]
    rfl
  have hstage := hilbertDifference_first_site_split (projectionResidual n)
  change ‖derivativeResidual n‖ ^ 2 =
    (hilbertSequence (projectionResidual n) 1) ^ 2 / 2 +
      ‖derivativeResidual n - hilbertSequence (projectionResidual n) 1 •
        hilbertAtom 1 (by decide)‖ ^ 2 at hstage
  have hcoordinate := hilbertSequence_sq_le_norm_sq (limitProjection - projection n) 1
  simp only [Nat.cast_one, one_mul, show (1 : ℝ) + 1 = 2 by norm_num] at hcoordinate
  have hgap := energy_eq_limit_add n
  have hup : (hilbertSequence limitResidual 1) ^ 2 / 2 ≤
      2 * (‖derivativeResidual n‖ ^ 2 + (energy n - limitEnergy)) := by
    rw [hseq]
    nlinarith [sq_nonneg (hilbertSequence (projectionResidual n) 1 +
      hilbertSequence (limitProjection - projection n) 1),
      sq_nonneg ‖derivativeResidual n - hilbertSequence (projectionResidual n) 1 •
        hilbertAtom 1 (by decide)‖]
  have h := mul_le_mul_of_nonneg_left (hlower.trans hup)
    (show 0 ≤ 3 + 2 * Real.sqrt 2 by positivity)
  have hc : (3 + 2 * Real.sqrt 2) * (3 - 2 * Real.sqrt 2) = 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← mul_assoc, hc, one_mul, derivative_error_exact_split] at h
  nlinarith

/-- The same complete first-site split at every actual projection stage;
the finite dyadic defect keeps its sign inside the square. -/
theorem derivative_stage_exact_dyadic_split (n : ℕ) :
    ‖derivativeResidual n‖ ^ 2 =
      ((2 - Real.sqrt 2) * energy n +
        (Real.sqrt 2 / 2) * finiteDyadicResidualRemainder n -
          finiteDyadicDefect n) ^ 2 / 2 +
      ‖derivativeResidual n - hilbertSequence (projectionResidual n) 1 •
          hilbertAtom 1 (by decide)‖ ^ 2 := by
  have h := hilbertDifference_first_site_split (projectionResidual n)
  change ‖derivativeResidual n‖ ^ 2 =
    (hilbertSequence (projectionResidual n) 1) ^ 2 / 2 +
      ‖derivativeResidual n - hilbertSequence (projectionResidual n) 1 •
        hilbertAtom 1 (by decide)‖ ^ 2 at h
  nth_rw 1 [finite_firstCoordinate_eq_dyadicSquare_sub_defect,
    finiteDyadicSquare_eq_energy_add_remainder] at h
  exact h

/-- The limiting compatibility cost is quantified by the full exact
decomposition above, rather than merely declared nonnegative. -/
theorem mismatchEnergy_tendsto_four_terms :
    Tendsto mismatchEnergy atTop
      (𝓝 ((3 - 2 * Real.sqrt 2) * limitEnergy ^ 2 +
        (Real.sqrt 2 - 1) * limitEnergy * residualDyadicRemainder +
        residualDyadicRemainder ^ 2 / 4 + ‖residualDerivativeTail‖ ^ 2)) := by
  simpa only [derivative_limit_exact_four_terms] using mismatchEnergy_tendsto

end CoefficientStabilization.DerivativeCompatibility
end RiemannResearch.RH.Pareto
