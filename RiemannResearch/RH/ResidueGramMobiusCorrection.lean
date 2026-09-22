import RiemannResearch.RH.ResidueGramCofactors
import RiemannResearch.RH.ParetoNormClosure

/-!
# Exact inverse-Gram Möbius corrections

Source: user-provided Pareto projection argument, 22 September 2026,
for the coefficient decomposition and proposed convergence-to-RH chain.
The proof assembles existing full-Pareto projection and coefficient theorems.

Stage n uses g_2,...,g_(n+1), corresponding to manuscript cutoff N=n+1.
The matrix entries are the complete Hilbert inner products. The source vector
has entries log(i+2)/(i+2). No tail truncation is used.

Established: the inverse-Gram vector equals the canonical projection
coefficients; its decomposition holds for every reference vector; the actual
Möbius correction is c+mu and every fixed correction has a limit.
Correction convergence to zero is equivalent to full Pareto norm convergence.

CONDITIONAL RESEARCH REDUCTION: riemannHypothesis_of_correction_limits.
OPEN: every fixed arithmetic correction tends to zero. The algebraic
decomposition neither supplies nor assumes that analytic limit.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.Pareto.IntegerDPP

def source (n : ℕ) : Fin n → ℝ :=
  cross (fun i : Fin n => residueAtom i.val) hilbertOne

def mobiusVector (n : ℕ) : Fin n → ℝ :=
  fun i => (ArithmeticFunction.moebius (i.val + 2) : ℝ)

def canonicalVector (n : ℕ) : Fin n → ℝ :=
  (fullGram n)⁻¹.mulVec (source n)

def correctionVector (n : ℕ) : Fin n → ℝ :=
  (fullGram n)⁻¹.mulVec (source n + (fullGram n).mulVec (mobiusVector n))

def correction (n m : ℕ) : ℝ :=
  coefficient n m + (ArithmeticFunction.moebius m : ℝ)

theorem source_apply (n : ℕ) (i : Fin n) :
    source n i = Real.log ((i.val + 2 : ℕ) : ℝ) / ((i.val + 2 : ℕ) : ℝ) :=
  residueAtom_inner_one i.val

theorem canonicalVector_apply (n : ℕ) (i : Fin n) :
    canonicalVector n i = coefficient n (i.val + 2) :=
  (projection_coefficient_eq_inverseGram n hilbertOne i).symm

theorem projection_eq_inverseGram_synthesis (n : ℕ) :
    projection n = ∑ i : Fin n, canonicalVector n i • residueAtom i.val := by
  simpa only [canonicalVector_apply] using projection_expansion n

theorem inverse_mulVec_cancel (n : ℕ) (u : Fin n → ℝ) :
    (fullGram n)⁻¹.mulVec ((fullGram n).mulVec u) = u := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt (fullGram_det_pos n))),
    Matrix.one_mulVec]

/-- The decomposition holds for every reference vector, not only Möbius values. -/
theorem canonical_decomposition (n : ℕ) (u : Fin n → ℝ) :
    canonicalVector n =
      -u + (fullGram n)⁻¹.mulVec (source n + (fullGram n).mulVec u) := by
  rw [Matrix.mulVec_add, inverse_mulVec_cancel]
  change canonicalVector n = -u + (canonicalVector n + u)
  abel

theorem correctionVector_eq (n : ℕ) :
    correctionVector n = canonicalVector n + mobiusVector n := by
  unfold correctionVector
  rw [Matrix.mulVec_add, inverse_mulVec_cancel]
  rfl

theorem canonical_mobius_decomposition (n : ℕ) :
    canonicalVector n = -mobiusVector n + correctionVector n :=
  canonical_decomposition n (mobiusVector n)

theorem correctionVector_apply (n : ℕ) (i : Fin n) :
    correctionVector n i = correction n (i.val + 2) := by
  rw [correctionVector_eq]
  change canonicalVector n i + mobiusVector n i = correction n (i.val + 2)
  rw [canonicalVector_apply]
  rfl

/-- Unconditional existence of the fixed correction limit; its value may be nonzero. -/
theorem correction_tendsto (m : ℕ) :
    Tendsto (fun n => correction n m) atTop
      (𝓝 (limitCoefficient m + (ArithmeticFunction.moebius m : ℝ))) := by
  exact (coefficient_tendsto m).add_const _

theorem correction_tendsto_zero_iff (m : ℕ) :
    Tendsto (fun n => correction n m) atTop (𝓝 0) ↔
      Tendsto (fun n => coefficient n m) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ))) := by
  constructor
  · intro h
    simpa only [correction, add_sub_cancel_right, zero_sub] using
      h.sub_const (ArithmeticFunction.moebius m : ℝ)
  · intro h
    simpa only [correction, neg_add_cancel] using
      h.add_const (ArithmeticFunction.moebius m : ℝ)

/-- Exact equivalence, with neither vanishing condition asserted unconditionally. -/
theorem correction_limits_iff_norm :
    (∀ m : ℕ, 1 < m →
      Tendsto (fun n => correction n m) atTop (𝓝 0)) ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) := by
  have hc :
      (∀ m : ℕ, 1 < m → Tendsto (fun n => correction n m) atTop (𝓝 0)) ↔
      (∀ m : ℕ, 1 < m → Tendsto (fun n => coefficient n m) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) := by
    constructor
    · intro h m hm
      exact (correction_tendsto_zero_iff m).mp (h m hm)
    · intro h m hm
      exact (correction_tendsto_zero_iff m).mpr (h m hm)
  exact hc.trans (coefficients_tendsto_mobius_iff.trans
    (limitCoefficients_eq_mobius_iff_mem.trans
      projection_norm_tendsto_zero_iff_mem.symm))

/-- Conditional research reduction. The correction-decay hypothesis is OPEN. -/
theorem riemannHypothesis_of_correction_limits
    (h : ∀ m : ℕ, 1 < m →
      Tendsto (fun n => correction n m) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_projection_norm_tendsto_zero
    (correction_limits_iff_norm.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
