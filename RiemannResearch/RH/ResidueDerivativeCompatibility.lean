import RiemannResearch.Analysis.FiniteGramCompatibility
import RiemannResearch.Analysis.ClosedSpanCompatibility
import RiemannResearch.RH.ThresholdHilbertDifference
import RiemannResearch.RH.PrimeSieveDerivativeClosure
import RiemannResearch.RH.ResidueGramMobiusCorrection

/-!
# Exact derivative compatibility of the actual Pareto projections

Source: `CRTPrimitiveTransferAudit20260929.md`, Section 6. This module
formalizes the actual finite matrix identity and strengthens the remaining
criterion to fixed derivative pairings, using the already established strong
limit of the original legal projections. The first-site target is retained.

Neither the compatibility energy nor its fixed pairings are asserted to tend
to zero unconditionally. The conditional RH implication uses those exact
open hypotheses, not a uniform inverse estimate for differentiation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility

open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk
open GramMobiusCorrection

def derivativeAtom (i : ℕ) : ThresholdHilbert := hilbertDifference (residueAtom i)

def derivativeFamily (n : ℕ) : Fin n → ThresholdHilbert :=
  fun i => derivativeAtom i.val

def derivativeGram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  gramMatrix (derivativeFamily n)

def derivativeSource (n : ℕ) : Fin n → ℝ :=
  cross (derivativeFamily n) (hilbertAtom 1 (by decide))

def derivativeBestCoeff (n : ℕ) : Fin n → ℝ :=
  (derivativeGram n)⁻¹.mulVec (derivativeSource n)

def derivativeBestError (n : ℕ) : ℝ :=
  ‖hilbertAtom 1 (by decide) -
    Fintype.linearCombination ℝ (derivativeFamily n) (derivativeBestCoeff n)‖ ^ 2

/-- Complete derivative normal-equation mismatch of the legal optimizer. -/
def mismatchSource (n : ℕ) : Fin n → ℝ :=
  derivativeSource n - (derivativeGram n).mulVec (canonicalVector n)

/-- Every signed covariance contribution is retained in this inverse form. -/
def mismatchEnergy (n : ℕ) : ℝ :=
  dotProduct (mismatchSource n) ((derivativeGram n)⁻¹.mulVec (mismatchSource n))

def derivativeResidual (n : ℕ) : ThresholdHilbert :=
  hilbertDifference (hilbertOne - projection n)

/-- A fixed coordinate is defined even before its conductor enters the finite matrix. -/
def fixedMismatch (n i : ℕ) : ℝ :=
  inner ℝ (derivativeAtom i) (derivativeResidual n)

theorem derivativeFamily_independent (n : ℕ) :
    LinearIndependent ℝ (derivativeFamily n) := by
  exact (residueAtom_linearIndependent.map' hilbertDifference.toLinearMap
    (LinearMap.ker_eq_bot.mpr hilbertDifference_injective)).comp
      (fun i : Fin n => i.val) Fin.val_injective

theorem derivativeGram_det_pos (n : ℕ) : 0 < (derivativeGram n).det :=
  gramMatrix_det_pos (derivativeFamily_independent n)

theorem derivativeSource_apply (n : ℕ) (i : Fin n) :
    derivativeSource n i = 1 / (2 * ((i.val + 2 : ℕ) : ℝ)) := by
  change inner ℝ (hilbertDifference (residueAtom i.val))
    (hilbertAtom 1 (by decide)) = _
  rw [real_inner_comm, hilbertAtom_inner, hilbertDifference_sequence,
    residueAtom, normalizedResidueHilbert_sequence]
  have hi : 1 < i.val + 2 := by omega
  simp only [PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift,
    ArithmeticCumulative.residueFraction, Nat.sub_self, Nat.zero_mod, Nat.cast_zero,
    zero_div, sub_zero, Nat.mod_eq_of_lt hi, Nat.cast_one]
  norm_num [positiveWeight]
  ring

theorem derivative_projection_synthesis (n : ℕ) :
    hilbertDifference (projection n) =
      Fintype.linearCombination ℝ (derivativeFamily n) (canonicalVector n) := by
  rw [projection_eq_inverseGram_synthesis, Fintype.linearCombination_apply]
  simp only [map_sum, map_smul, derivativeFamily, derivativeAtom]

theorem derivativeResidual_eq (n : ℕ) :
    derivativeResidual n = hilbertAtom 1 (by decide) -
      Fintype.linearCombination ℝ (derivativeFamily n) (canonicalVector n) := by
  rw [derivativeResidual, map_sub, hilbertDifference_hilbertOne,
    derivative_projection_synthesis]

theorem derivativeAtom_inner_target (i : ℕ) :
    inner ℝ (derivativeAtom i) (hilbertAtom 1 (by decide)) =
      1 / (2 * ((i + 2 : ℕ) : ℝ)) :=
  derivativeSource_apply (i + 1) ⟨i, Nat.lt_succ_self i⟩

/-- The fixed-coordinate criterion is an explicit signed arithmetic row,
valid even before the test conductor is included in the optimization stage. -/
theorem fixedMismatch_eq_signed_row (n i : ℕ) :
    fixedMismatch n i = 1 / (2 * ((i + 2 : ℕ) : ℝ)) -
      ∑ j : Fin n, canonicalVector n j *
        inner ℝ (derivativeAtom i) (derivativeAtom j.val) := by
  rw [fixedMismatch, derivativeResidual_eq, inner_sub_right,
    derivativeAtom_inner_target, Fintype.linearCombination_apply, inner_sum]
  simp only [real_inner_smul_right, derivativeFamily]

theorem mismatchSource_eq_compatibilitySource (n : ℕ) :
    mismatchSource n = compatibilitySource (derivativeFamily n)
      (hilbertAtom 1 (by decide)) (canonicalVector n) := by
  rw [compatibilitySource_eq_matrix]
  rfl

theorem mismatchSource_apply (n : ℕ) (i : Fin n) :
    mismatchSource n i = fixedMismatch n i.val := by
  rw [mismatchSource_eq_compatibilitySource, compatibilitySource_eq_cross]
  change inner ℝ (derivativeAtom i.val)
    (hilbertAtom 1 (by decide) -
      Fintype.linearCombination ℝ (derivativeFamily n) (canonicalVector n)) = _
  rw [← derivativeResidual_eq]
  rfl

theorem mismatchEnergy_eq_compatibilityEnergy (n : ℕ) :
    mismatchEnergy n = compatibilityEnergy (derivativeFamily_independent n)
      (hilbertAtom 1 (by decide)) (canonicalVector n) := by
  rw [compatibilityEnergy_eq_matrix, ← mismatchSource_eq_compatibilitySource]
  rfl

theorem mismatchEnergy_nonneg (n : ℕ) : 0 ≤ mismatchEnergy n := by
  rw [mismatchEnergy_eq_compatibilityEnergy]
  exact compatibilityEnergy_nonneg _ _ _

/-- The all-stage arithmetic identity, with the actual legal coefficients
and the complete inverse derivative Gram remainder. -/
theorem derivative_error_exact_split (n : ℕ) :
    ‖derivativeResidual n‖ ^ 2 = derivativeBestError n + mismatchEnergy n := by
  rw [derivativeResidual_eq]
  exact residual_compatibility_matrix (derivativeFamily_independent n)
    (hilbertAtom 1 (by decide)) (canonicalVector n)

theorem derivativeBestError_eq_walkError (n : ℕ) :
    derivativeBestError n = walkError derivativeAtom id (hilbertAtom 1 (by decide)) n := by
  rw [derivativeBestError, derivativeBestCoeff, derivativeGram, derivativeSource,
    gramMatrix_inverseSource (derivativeFamily_independent n)]
  change ‖hilbertAtom 1 (by decide) -
    Fintype.linearCombination ℝ (derivativeFamily n)
      (inverseCoeff (derivativeFamily_independent n) (hilbertAtom 1 (by decide)))‖ ^ 2 = _
  rw [synthesis_inverseCoeff_eq_projection]
  rfl

/-- This vanishing is unconditional: the actual sieve supplies target membership. -/
theorem derivativeBestError_tendsto_zero :
    Tendsto derivativeBestError atTop (𝓝 0) := by
  have hm : hilbertAtom 1 (by decide) ∈ dictionaryClosure derivativeAtom := by
    exact derivative_target_mem_dictionaryClosure
  change Tendsto (fun n => derivativeBestError n) atTop (𝓝 0)
  simpa only [derivativeBestError_eq_walkError] using
    (walkError_tendsto_zero_iff derivativeAtom id Function.surjective_id
      (hilbertAtom 1 (by decide))).mpr hm

/-- The original legal projections already have a strong limit. Continuity
of differentiation therefore supplies this unconditional strong limit. -/
theorem derivativeResidual_tendsto :
    Tendsto derivativeResidual atTop (𝓝 (hilbertDifference limitResidual)) := by
  exact (hilbertDifference.continuous.tendsto limitResidual).comp
    (tendsto_const_nhds.sub projection_tendsto)

/-- The complete compatibility cost always converges; its limit may be positive. -/
theorem mismatchEnergy_tendsto :
    Tendsto mismatchEnergy atTop (𝓝 (‖hilbertDifference limitResidual‖ ^ 2)) := by
  have he (n : ℕ) : mismatchEnergy n =
      ‖derivativeResidual n‖ ^ 2 - derivativeBestError n := by
    linarith [derivative_error_exact_split n]
  change Tendsto (fun n => mismatchEnergy n) atTop
    (𝓝 (‖hilbertDifference limitResidual‖ ^ 2))
  simpa only [he, sub_zero] using
    (derivativeResidual_tendsto.norm.pow 2).sub derivativeBestError_tendsto_zero

theorem mismatchEnergy_tendsto_zero_iff_residual_zero :
    Tendsto mismatchEnergy atTop (𝓝 0) ↔ limitResidual = 0 := by
  constructor
  · intro h
    have he : ‖hilbertDifference limitResidual‖ ^ 2 = 0 :=
      tendsto_nhds_unique mismatchEnergy_tendsto h
    have hz : hilbertDifference limitResidual = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (hilbertDifference limitResidual)]
    apply hilbertDifference_injective
    simpa only [map_zero] using hz
  · intro h
    simpa only [h, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      mismatchEnergy_tendsto

theorem residual_zero_iff_projection_norm_zero :
    limitResidual = 0 ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [h, norm_zero] using projection_norm_error_tendsto
  · intro h
    exact norm_eq_zero.mp (tendsto_nhds_unique projection_norm_error_tendsto h)

theorem mismatchEnergy_tendsto_zero_iff_projection_norm_zero :
    Tendsto mismatchEnergy atTop (𝓝 0) ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) :=
  mismatchEnergy_tendsto_zero_iff_residual_zero.trans
    residual_zero_iff_projection_norm_zero

theorem derivative_projection_mem_dictionaryClosure (n : ℕ) :
    hilbertDifference (projection n) ∈ dictionaryClosure derivativeAtom := by
  rw [derivative_projection_synthesis, Fintype.linearCombination_apply]
  apply (dictionaryClosure derivativeAtom).sum_mem
  intro i _
  apply (dictionaryClosure derivativeAtom).smul_mem
  exact (Submodule.span ℝ (Set.range derivativeAtom)).le_topologicalClosure
    (Submodule.subset_span ⟨i.val, rfl⟩)

theorem derivativeResidual_mem_dictionaryClosure (n : ℕ) :
    derivativeResidual n ∈ dictionaryClosure derivativeAtom := by
  change hilbertDifference (hilbertOne - projection n) ∈ _
  rw [map_sub, hilbertDifference_hilbertOne]
  exact (dictionaryClosure derivativeAtom).sub_mem
    derivative_target_mem_dictionaryClosure (derivative_projection_mem_dictionaryClosure n)

theorem derivative_limit_mem_dictionaryClosure :
    hilbertDifference limitResidual ∈ dictionaryClosure derivativeAtom := by
  exact (Submodule.span ℝ (Set.range derivativeAtom)).isClosed_topologicalClosure.mem_of_tendsto
    derivativeResidual_tendsto (Eventually.of_forall derivativeResidual_mem_dictionaryClosure)

/-- Every fixed compatibility coordinate has an unconditional, explicitly
identified limit, with no assertion that this limit is zero. -/
theorem fixedMismatch_tendsto (i : ℕ) :
    Tendsto (fun n => fixedMismatch n i) atTop
      (𝓝 (inner ℝ (derivativeAtom i) (hilbertDifference limitResidual))) := by
  exact ((innerSL ℝ (derivativeAtom i)).continuous.tendsto _).comp
    derivativeResidual_tendsto

/-- For the actual convergent legal projections, fixed derivative normal
equations suffice. No uniform inverse Gram bound is needed in this criterion. -/
theorem fixedMismatch_limits_iff_residual_zero :
    (∀ i : ℕ, Tendsto (fun n => fixedMismatch n i) atTop (𝓝 0)) ↔
      limitResidual = 0 := by
  have h := RiemannResearch.Analysis.ClosedSpanCompatibility.strongLimit_eq_zero_iff
    derivativeAtom derivativeResidual (hilbertDifference limitResidual)
    derivativeResidual_tendsto derivative_limit_mem_dictionaryClosure
  have hinj : hilbertDifference limitResidual = 0 ↔ limitResidual = 0 := by
    constructor
    · intro hz
      apply hilbertDifference_injective
      simpa only [map_zero] using hz
    · rintro hz
      rw [hz, map_zero]
  exact h.symm.trans hinj

theorem fixedMismatch_limits_iff_projection_norm_zero :
    (∀ i : ℕ, Tendsto (fun n => fixedMismatch n i) atTop (𝓝 0)) ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) :=
  fixedMismatch_limits_iff_residual_zero.trans residual_zero_iff_projection_norm_zero

/-- Conditional RH consequence: fixed signed derivative compatibility is
the explicit remaining arithmetic hypothesis. -/
theorem riemannHypothesis_of_fixedMismatch_limits
    (h : ∀ i : ℕ, Tendsto (fun n => fixedMismatch n i) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_projection_norm_tendsto_zero
    (fixedMismatch_limits_iff_projection_norm_zero.mp h)

theorem riemannHypothesis_of_mismatchEnergy_tendsto_zero
    (h : Tendsto mismatchEnergy atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_projection_norm_tendsto_zero
    (mismatchEnergy_tendsto_zero_iff_projection_norm_zero.mp h)

/-- Full limiting primitive identity: all symmetric and shift-defect energy
is retained alongside the compatibility limit. -/
theorem limiting_full_primitive_identity :
    4 * limitEnergy = ‖hilbertDifference limitResidual‖ ^ 2 +
      ‖limitResidual + hilbertBackwardShift limitResidual‖ ^ 2 +
      2 * PrimitiveEnergy.shiftDefect (hilbertSequence limitResidual) :=
  hilbert_full_primitive_energy_identity limitResidual

theorem limiting_mismatch_bounds :
    0 ≤ ‖hilbertDifference limitResidual‖ ^ 2 ∧
      ‖hilbertDifference limitResidual‖ ^ 2 ≤ 4 * limitEnergy := by
  refine ⟨sq_nonneg _, ?_⟩
  change ‖hilbertDifference limitResidual‖ ^ 2 ≤ 4 * ‖limitResidual‖ ^ 2
  have h := hilbertDifference_norm_le limitResidual
  nlinarith [norm_nonneg (hilbertDifference limitResidual), norm_nonneg limitResidual]

/-- Failure of RH would force a strictly positive compatibility limit. -/
theorem limiting_mismatch_pos_of_not_rh (h : ¬ RiemannHypothesis) :
    0 < ‖hilbertDifference limitResidual‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  have hr : limitResidual = 0 := by
    apply hilbertDifference_injective
    simpa only [map_zero] using hz
  apply h
  exact riemannHypothesis_of_projection_norm_tendsto_zero
    (residual_zero_iff_projection_norm_zero.mp hr)

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
