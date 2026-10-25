/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerPolynomialOrthonormal
import RiemannResearch.RH.QPrimePowerCofactorResidual
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.InfiniteSum.Module
/-!
# Infinite signed polynomial trials for the floor-log target

Source: user-provided valuation/Meixner research direction and
FpOrthonormalBasisResearch20261020.md. Mathlib's orthogonal-family
summability criterion supplies unconditional synthesis for exactly the
square-summable signed coefficients. Continuity extends the established
finite-trial equality to the full infinite series.

The complete cofactor residual and every coefficient discrepancy remain.
This does not assert polynomial density in the valuation space, tensor
completeness, or membership of either floor-log target in the legal closure.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert

/-- Square summability is exactly the condition for unconditional higher-mode synthesis. -/
theorem valuationPolynomial_summable_iff (p : ℕ) (hp : p.Prime) (a : ℕ → ℝ) :
    Summable (fun j => a j • valuationPolynomialMode p hp (j+1)) ↔
      Summable (fun j => (a j) ^ 2) := by
  have ho := (valuationPolynomialMode_orthonormal p hp).comp
    (fun j : ℕ => j+1) Nat.succ_injective
  simpa [Real.norm_eq_abs, sq_abs] using
    ho.orthogonalFamily.summable_iff_norm_sq_summable a

/-- The complete signed infinite-trial identity retains the cofactor residual. -/
theorem qTarget_valuationPolynomial_infinite_error (p : ℕ) (hp : p.Prime)
    (a : ℕ → ℝ) (ha : Summable (fun j => (a j) ^ 2)) (mu b : ℝ) :
    ‖qTarget p hp.one_lt - (mu • qOne + b • valuationPolynomialMode p hp 0 +
      ∑' j : ℕ, a j • valuationPolynomialMode p hp (j+1))‖^2 =
      ‖primeCofactorResidual p hp‖^2 +
      (inner ℝ (qTarget p hp.one_lt) qOne-mu)^2 +
      ((p : ℝ)/((p : ℝ)^2-1)-b)^2 + ∑' j : ℕ, (a j) ^ 2 := by
  have hs := ((valuationPolynomial_summable_iff p hp a).mpr ha).hasSum.tendsto_sum_nat
  have hl := ((tendsto_const_nhds (x := qTarget p hp.one_lt)).sub
    ((tendsto_const_nhds
      (x := mu • qOne + b • valuationPolynomialMode p hp 0)).add hs)).norm.pow 2
  have hr := (tendsto_const_nhds (x := ‖primeCofactorResidual p hp‖^2 +
    (inner ℝ (qTarget p hp.one_lt) qOne-mu)^2 +
    ((p : ℝ)/((p : ℝ)^2-1)-b)^2)).add ha.hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique hl
  convert hr using 1
  ext N
  exact qTarget_valuationPolynomial_signed_error p hp (Finset.range N) a mu b

/-- Infinite synthesis recovers every signed coefficient without a completeness hypothesis. -/
theorem valuationPolynomial_tsum_coefficient (p : ℕ) (hp : p.Prime)
    (a : ℕ → ℝ) (ha : Summable (fun j => (a j) ^ 2)) (i : ℕ) :
    inner ℝ (valuationPolynomialMode p hp (i+1))
      (∑' j : ℕ, a j • valuationPolynomialMode p hp (j+1)) = a i := by
  have hs := (valuationPolynomial_summable_iff p hp a).mpr ha
  change (innerSL ℝ (valuationPolynomialMode p hp (i+1))) (∑' j : ℕ, _) = _
  rw [(innerSL ℝ (valuationPolynomialMode p hp (i+1))).map_tsum hs]
  change (∑' j : ℕ, inner ℝ (valuationPolynomialMode p hp (i+1))
    (a j • valuationPolynomialMode p hp (j+1))) = _
  simp only [real_inner_smul_right,
    orthonormal_iff_ite.mp (valuationPolynomialMode_orthonormal p hp)]
  simp

/-- Only the zero coefficient sequence synthesizes the zero higher-mode vector. -/
theorem valuationPolynomial_tsum_eq_zero_iff (p : ℕ) (hp : p.Prime)
    (a : ℕ → ℝ) (ha : Summable (fun j => (a j) ^ 2)) :
    (∑' j : ℕ, a j • valuationPolynomialMode p hp (j+1)) = 0 ↔ ∀ j, a j = 0 := by
  constructor
  · intro h i
    have hi := valuationPolynomial_tsum_coefficient p hp a ha i
    rw [h, inner_zero_right] at hi
    exact hi.symm
  · intro h
    simp [h]

end RiemannResearch.RH.PrimePowerTarget
