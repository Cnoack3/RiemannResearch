import RiemannResearch.NumberTheory.ParityResidueConvolutionMoments
import RiemannResearch.RH.ParetoDirichletExponential
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The parity convolution as an actual Pareto and Q vector
Source: user-provided parity-convolution agenda (13 November 2026).
Finite inverse-Gram systems use the actual complete Q inner product.
The Möbius-difference coordinates use Balazard, arXiv:1812.04309, Sections 1--2,
as background for the existing repository duality. Closed-span membership
and saturation remain open; the exact signed residual is retained.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.ParetoParityConvolution
open RiemannResearch.NumberTheory.DirichletExponential
open RiemannResearch.NumberTheory.ParityResidueConvolution
open Pareto Pareto.ConvolutionExponential Pareto.CoefficientStabilization
open ZetaTwoHilbert ZetaTwoProbability QParetoEquivalence

theorem paritySquare_inv_sq_summable :
    Summable (fun n => paritySquare n ^ 2 / (n : ℝ) ^ 2) := by
  simpa only [pow_two, paritySquare] using
    (bounded_power_square_summable_and_bound (residueAF 2) (by norm_num : (0 : ℝ) ≤ 1)
      (residueAF_abs_le_one 2) 2).1

theorem paritySquare_pareto_summable :
    Summable (fun n => positiveWeight n * paritySquare n ^ 2) :=
  weighted_square_summable_of_inv_sq _ paritySquare_inv_sq_summable

def pTarget : ThresholdHilbert := sequenceHilbert paritySquare paritySquare_pareto_summable

@[simp] theorem pTarget_sequence : hilbertSequence pTarget = paritySquare := by
  apply hilbertSequence_sequenceHilbert
  simp [paritySquare]

def qTarget : QHilbert := toQ pTarget

@[simp] theorem qTarget_sequence : qSequence qTarget = paritySquare := by
  simp [qTarget]

theorem pTarget_not_mem_atomSpan :
    pTarget ∉ Submodule.span ℝ (Set.range residueAtom) := by
  intro h
  obtain ⟨C,hC⟩ := bounded_physical_sequence_of_mem_atomSpan h
  apply paritySquare_not_bounded
  exact ⟨C, by simpa only [pTarget_sequence] using hC⟩

theorem target_mem_q_iff_p :
    qTarget ∈ QFullResidueProjection.closure ↔ pTarget ∈ closedSpace := by
  have h := mem_closure_span_iff (fun i : ℕ => qResidue (i + 2)) qTarget
  simpa only [ZetaTwoParetoTransfer.toPareto_residueAtom, qTarget, toPareto_toQ,
    QFullResidueProjection.closure, QFullResidueProjection.legalSpan,
    closedSpace, RiemannResearch.Analysis.ExhaustiveWalk.dictionaryClosure] using h

theorem qTarget_norm_series :
    ‖qTarget‖ ^ 2 = (1 / zetaTwo) * ∑' n, paritySquare n ^ 2 / (n : ℝ) ^ 2 := by
  rw [qNorm_weighted_sq, qTarget_sequence, ← tsum_mul_left]
  congr 1
  funext n
  simp [positiveQWeight, div_eq_mul_inv]
  ring

@[simp] theorem paritySquare_one : paritySquare 1 = (1 / 4 : ℝ) := by
  norm_num [paritySquare, ArithmeticFunction.mul_apply_one, residueAF_apply]

theorem coefficient_target_prime_formula {p : ℕ} (hp : p.Prime) :
    coefficientCLM p pTarget =
      (1 / 4 : ℝ) - paritySquare p + paritySquare (p - 1) := by
  simp only [coefficientCLM, neg_apply, mobiusDifferenceCLM_apply,
    pTarget_sequence, mobiusDifference, hp.sum_divisors]
  simp only [Nat.div_self hp.pos, Nat.div_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_one, Int.cast_neg,
    one_mul, neg_one_mul, Nat.sub_self, ArithmeticFunction.map_zero, paritySquare_one]
  ring

theorem coefficient_target_prime {p : ℕ} (hp : p.Prime) (hpodd : p % 2 = 1) :
    coefficientCLM p pTarget = -(1 / 4 : ℝ) := by
  have hprev : paritySquare (p - 1) = 0 := by
    rw [paritySquare_parity, if_neg (by omega : (p - 1) % 2 ≠ 1)]
  rw [coefficient_target_prime_formula hp, paritySquare_prime hp hpodd, hprev]
  norm_num

theorem coefficient_target_two : coefficientCLM 2 pTarget = (1 / 2 : ℝ) := by
  rw [coefficient_target_prime_formula (by decide)]
  norm_num [paritySquare_one, paritySquare_parity]

open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk
open QFullResidueProjection QCovarianceInvertibility

def atoms (n : ℕ) (i : Fin n) : QHilbert := qResidue (conductor n i)
def gram (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := gramMatrix (atoms n)
def rhs (n : ℕ) : Fin n → ℝ := cross (atoms n) qTarget
def coeff (n : ℕ) : Fin n → ℝ := (gram n)⁻¹.mulVec (rhs n)
def fit (n : ℕ) : QHilbert := Fintype.linearCombination ℝ (atoms n) (coeff n)
def capacity (n : ℕ) : ℝ := dotProduct (rhs n) (coeff n)
def residual (n : ℕ) : ℝ := ‖qTarget - fit n‖ ^ 2

theorem atoms_independent (n : ℕ) : LinearIndependent ℝ (atoms n) :=
  qResidue_linearIndependent (conductor n) (conductor_gt_one n) (conductor_injective n)

theorem gram_posDef (n : ℕ) : (gram n).PosDef := gramMatrix_posDef (atoms_independent n)

theorem fit_eq_projection (n : ℕ) : fit n = (stage n).starProjection qTarget := by
  unfold fit coeff gram rhs
  rw [← inverseCoeff_eq_inv_mulVec (atoms_independent n)]
  exact synthesis_inverseCoeff_eq_projection (atoms_independent n) qTarget

theorem residual_identity (n : ℕ) :
    residual n = ‖qTarget‖ ^ 2 - capacity n :=
  residual_matrix_value (atoms_independent n) qTarget

theorem fit_tendsto :
    Tendsto fit atTop (𝓝 (QFullResidueProjection.closure.starProjection qTarget)) := by
  change Tendsto (fun n => fit n) atTop _
  simp_rw [fit_eq_projection]
  exact walkProjection_tendsto (fun i => qResidue (i + 2)) id Function.surjective_id qTarget

theorem residual_tendsto_zero_iff :
    Tendsto residual atTop (𝓝 0) ↔ qTarget ∈ QFullResidueProjection.closure := by
  change Tendsto (fun n => residual n) atTop _ ↔ _
  simp_rw [residual, fit_eq_projection]
  exact walkError_tendsto_zero_iff (fun i => qResidue (i + 2))
      id Function.surjective_id qTarget

theorem capacity_saturation_iff :
    Tendsto capacity atTop (𝓝 (‖qTarget‖ ^ 2)) ↔ pTarget ∈ closedSpace := by
  rw [← target_mem_q_iff_p, ← residual_tendsto_zero_iff]
  constructor
  · intro h
    have ht : Tendsto (fun n => ‖qTarget‖ ^ 2 - capacity n) atTop
        (𝓝 (‖qTarget‖ ^ 2 - ‖qTarget‖ ^ 2)) := tendsto_const_nhds.sub h
    simpa only [← residual_identity, sub_self] using ht
  · intro h
    have ht : Tendsto (fun n => ‖qTarget‖ ^ 2 - residual n) atTop
        (𝓝 (‖qTarget‖ ^ 2 - 0)) := tendsto_const_nhds.sub h
    have he (n : ℕ) : ‖qTarget‖ ^ 2 - residual n = capacity n := by
      rw [residual_identity]
      ring
    simpa only [he, sub_zero] using ht

def pFit (n : ℕ) : ThresholdHilbert := (finiteSpace n).starProjection pTarget
def pLimit : ThresholdHilbert := closedSpace.starProjection pTarget
def pDefect : ThresholdHilbert := pTarget - pLimit

theorem pFit_tendsto : Tendsto pFit atTop (𝓝 pLimit) :=
  walkProjection_tendsto residueAtom id Function.surjective_id pTarget

theorem coefficient_limit (m : ℕ) :
    Tendsto (fun n => coefficientCLM m (pFit n)) atTop
      (𝓝 (coefficientCLM m pLimit)) :=
  (coefficientCLM m).continuous.continuousAt.tendsto.comp pFit_tendsto

theorem coefficient_limit_signed_defect (m : ℕ) :
    coefficientCLM m pLimit =
      coefficientCLM m pTarget - coefficientCLM m pDefect := by
  simp only [pDefect, map_sub]
  ring

theorem prime_coefficient_limit_of_mem
    (h : pTarget ∈ closedSpace) {p : ℕ} (hp : p.Prime) (hpodd : p % 2 = 1) :
    Tendsto (fun n => coefficientCLM p (pFit n)) atTop (𝓝 (-(1/4 : ℝ))) := by
  have he : pLimit = pTarget := Submodule.starProjection_eq_self_iff.mpr h
  simpa only [he, coefficient_target_prime hp hpodd] using coefficient_limit p

end RiemannResearch.RH.ParetoParityConvolution
open Filter
open scoped Topology
namespace RiemannResearch.RH.ParetoParityConvolution
open RiemannResearch.NumberTheory.ParityResidueConvolution
open Pareto Pareto.ConvolutionExponential Pareto.CoefficientStabilization
open ZetaTwoHilbert ZetaTwoProbability

theorem qTarget_norm_exact : ‖qTarget‖ ^ 2 = 9 * Real.pi ^ 2 / 1024 := by
  rw [qTarget_norm_series, paritySquare_exact_moment, zetaTwo_eq_nat_sum,
    hasSum_zeta_two.tsum_eq]
  field_simp [Real.pi_ne_zero]
  ring

theorem pTarget_norm_bound : ‖pTarget‖ ^ 2 ≤ 3 * Real.pi ^ 4 / 2048 := by
  rw [hilbert_norm_weighted_sq, pTarget_sequence]
  exact (weighted_square_tsum_le_inv_sq _ paritySquare_inv_sq_summable).trans_eq
    paritySquare_exact_moment

theorem residual_identity_exact (n : ℕ) :
    residual n = 9 * Real.pi ^ 2 / 1024 - capacity n := by
  rw [residual_identity, qTarget_norm_exact]

theorem exact_saturation_iff :
    Tendsto capacity atTop (𝓝 (9 * Real.pi ^ 2 / 1024)) ↔ pTarget ∈ closedSpace := by
  simpa only [qTarget_norm_exact] using capacity_saturation_iff

theorem all_coefficient_limits_iff_mem :
    (∀ m : ℕ, 1 < m → Tendsto (fun n => coefficientCLM m (pFit n)) atTop
      (𝓝 (coefficientCLM m pTarget))) ↔ pTarget ∈ closedSpace := by
  constructor
  · intro h
    have hz : pDefect = 0 := by
      apply eq_zero_of_mobius_coordinates_zero
      intro m hm
      have he := tendsto_nhds_unique (coefficient_limit m) (h m hm)
      have hc : coefficientCLM m pDefect = 0 := by
        simp only [pDefect, map_sub, he, sub_self]
      simpa only [coefficientCLM, neg_apply, neg_eq_zero] using hc
    have he : closedSpace.starProjection pTarget = pTarget := by
      change pTarget - pLimit = 0 at hz
      exact (sub_eq_zero.mp hz).symm
    exact Submodule.starProjection_eq_self_iff.mp he
  · intro h m hm
    have he : pLimit = pTarget := Submodule.starProjection_eq_self_iff.mpr h
    simpa only [he] using coefficient_limit m

/-- In particular there is no continuous real-valued profinite extension. -/
theorem no_continuous_compact_extension {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (sites : ℕ → X) :
    ¬ ∃ F : X → ℝ, Continuous F ∧ ∀ n, F (sites n) = paritySquare n := by
  rintro ⟨F, hF, he⟩
  obtain ⟨C, hC⟩ := (isCompact_range hF.abs).bddAbove
  apply paritySquare_not_bounded
  refine ⟨C, fun n => ?_⟩
  rw [← he n]
  exact hC ⟨sites n, rfl⟩

end RiemannResearch.RH.ParetoParityConvolution
