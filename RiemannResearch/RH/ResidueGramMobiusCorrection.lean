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

/-- Exact arithmetic correction as a finite-coordinate test of the full residual. -/
theorem correction_eq_residual_coordinate (n m : ℕ) (hm : 0 < m) :
    correction n m = mobiusDifferenceCLM m (hilbertOne - projection n) := by
  simp only [correction, coefficient, coefficientCLM, neg_apply,
    map_sub, mobius_coordinate_one m hm]
  ring

/-- The limit exists unconditionally and is identified by the limiting residual. -/
theorem correction_tendsto_residual (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => correction n m) atTop
      (𝓝 (mobiusDifferenceCLM m limitResidual)) := by
  have he : limitCoefficient m + (ArithmeticFunction.moebius m : ℝ) =
      mobiusDifferenceCLM m limitResidual := by
    rw [limitCoefficient_eq_residual m hm]
    ring
  simpa only [he] using correction_tendsto m

/-- Explicit finite divisor-sum value of the limiting inverse-Gram correction. -/
theorem correction_tendsto_divisor_sum (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => correction n m) atTop
      (𝓝 (∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) *
        (hilbertSequence limitResidual d - hilbertSequence limitResidual (d - 1)))) := by
  simpa only [mobiusDifferenceCLM_apply, mobiusDifference] using
    correction_tendsto_residual m hm

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

/-- The natural finite Möbius synthesis, in the complete Pareto Hilbert space. -/
def mobiusSynthesis (n : ℕ) : ThresholdHilbert :=
  ∑ i : Fin n, mobiusVector n i • residueAtom i.val

/-- The uncorrected residual R_N, where N=n+1. -/
def mobiusResidual (n : ℕ) : ThresholdHilbert := hilbertOne + mobiusSynthesis n

/-- The Hilbert synthesis of the exact inverse-Gram correction vector. -/
def correctionSynthesis (n : ℕ) : ThresholdHilbert :=
  ∑ i : Fin n, correctionVector n i • residueAtom i.val

theorem mobiusSynthesis_mem (n : ℕ) :
    (∑ i : Fin n, mobiusVector n i • residueAtom i.val) ∈ finiteSpace n :=
  synthesis_mem (fun i : Fin n => residueAtom i.val) (mobiusVector n)

theorem correctionSynthesis_eq (n : ℕ) :
    correctionSynthesis n = projection n + mobiusSynthesis n := by
  simp only [correctionSynthesis, correctionVector_eq, Pi.add_apply,
    add_smul, Finset.sum_add_distrib, ← projection_eq_inverseGram_synthesis,
    mobiusSynthesis]

/-- The correction is the projection of the natural residual. -/
theorem mobiusResidual_projection (n : ℕ) :
    (finiteSpace n).starProjection (mobiusResidual n) = correctionSynthesis n := by
  rw [mobiusResidual, map_add,
    Submodule.starProjection_eq_self_iff.mpr
      (show mobiusSynthesis n ∈ finiteSpace n from mobiusSynthesis_mem n),
    correctionSynthesis_eq]
  rfl

theorem mobiusResidual_sub_correction (n : ℕ) :
    mobiusResidual n - correctionSynthesis n = hilbertOne - projection n := by
  rw [mobiusResidual, correctionSynthesis_eq]
  abel

theorem mobiusSynthesis_norm_sq (n : ℕ) :
    ‖mobiusSynthesis n‖ ^ 2 =
      dotProduct (mobiusVector n) ((fullGram n).mulVec (mobiusVector n)) := by
  rw [fullGram, gramMatrix_mulVec]
  exact gram_quadratic (fun i : Fin n => residueAtom i.val) (mobiusVector n)

theorem mobiusSynthesis_inner_one (n : ℕ) :
    inner ℝ (mobiusSynthesis n) hilbertOne = dotProduct (mobiusVector n) (source n) :=
  inner_synthesis_left (fun i : Fin n => residueAtom i.val) (mobiusVector n) hilbertOne

theorem mobiusResidual_source (n : ℕ) :
    cross (fun i : Fin n => residueAtom i.val) (mobiusResidual n) =
      source n + (fullGram n).mulVec (mobiusVector n) := by
  rw [fullGram, gramMatrix_mulVec]
  funext i
  change inner ℝ (residueAtom i.val) (hilbertOne + mobiusSynthesis n) =
    inner ℝ (residueAtom i.val) hilbertOne +
      inner ℝ (residueAtom i.val) (mobiusSynthesis n)
  exact inner_add_right _ _ _

theorem mobiusResidual_norm_sq (n : ℕ) :
    ‖mobiusResidual n‖ ^ 2 = 1 +
      2 * dotProduct (mobiusVector n) (source n) +
      dotProduct (mobiusVector n) ((fullGram n).mulVec (mobiusVector n)) := by
  have hi : inner ℝ hilbertOne (mobiusSynthesis n) =
      inner ℝ (mobiusSynthesis n) hilbertOne := real_inner_comm _ _
  rw [mobiusResidual, norm_add_sq_real, hilbertOne_norm_sq,
    hi, mobiusSynthesis_inner_one, mobiusSynthesis_norm_sq]

/-- Exact complete energy removed by the inverse-Gram correction. -/
theorem correctionSynthesis_norm_sq (n : ℕ) :
    ‖correctionSynthesis n‖ ^ 2 =
      dotProduct (source n + (fullGram n).mulVec (mobiusVector n))
        ((fullGram n)⁻¹.mulVec (source n + (fullGram n).mulVec (mobiusVector n))) := by
  have h := projection_inner_eq_inverseGram (TailCapacity.finiteAtom_independent n)
    (mobiusResidual n) (mobiusResidual n)
  change inner ℝ ((finiteSpace n).starProjection (mobiusResidual n))
    ((finiteSpace n).starProjection (mobiusResidual n)) =
      dotProduct (cross (fun i : Fin n => residueAtom i.val) (mobiusResidual n))
        ((fullGram n)⁻¹.mulVec
          (cross (fun i : Fin n => residueAtom i.val) (mobiusResidual n))) at h
  simpa only [mobiusResidual_projection, real_inner_self_eq_norm_sq,
    mobiusResidual_source] using h

/-- Pythagoras for the natural residual and its finite orthogonal correction. -/
theorem mobiusResidual_energy_split (n : ℕ) :
    ‖mobiusResidual n‖ ^ 2 =
      ‖hilbertOne - projection n‖ ^ 2 + ‖correctionSynthesis n‖ ^ 2 := by
  have h := residual_completion (TailCapacity.finiteAtom_independent n)
    hilbertOne (-mobiusVector n)
  rw [synthesis_inverseCoeff_eq_projection] at h
  have hi : inverseCoeff (TailCapacity.finiteAtom_independent n) hilbertOne =
      canonicalVector n := by
    rw [canonicalVector, fullGram, gramMatrix_inverseSource]
    rfl
  rw [hi] at h
  have hs : Fintype.linearCombination ℝ (fun i : Fin n => residueAtom i.val)
      (-mobiusVector n) = -mobiusSynthesis n := by
    simp [Fintype.linearCombination_apply, mobiusSynthesis]
  have hd : Fintype.linearCombination ℝ (fun i : Fin n => residueAtom i.val)
      (-mobiusVector n - canonicalVector n) = -correctionSynthesis n := by
    have hv : -mobiusVector n - canonicalVector n = -correctionVector n := by
      rw [correctionVector_eq]
      abel
    rw [hv]
    simp [Fintype.linearCombination_apply, correctionSynthesis]
  rw [hs, hd, sub_neg_eq_add, norm_neg] at h
  exact h

/-- Equation (34), including the entire infinite Pareto error. -/
theorem error_eq_mobius_matrix_correction (n : ℕ) :
    ‖hilbertOne - projection n‖ ^ 2 = 1 +
      2 * dotProduct (mobiusVector n) (source n) +
      dotProduct (mobiusVector n) ((fullGram n).mulVec (mobiusVector n)) -
      dotProduct (source n + (fullGram n).mulVec (mobiusVector n))
        ((fullGram n)⁻¹.mulVec (source n + (fullGram n).mulVec (mobiusVector n))) := by
  have h := mobiusResidual_energy_split n
  rw [mobiusResidual_norm_sq, correctionSynthesis_norm_sq] at h
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
