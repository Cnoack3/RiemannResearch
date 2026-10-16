import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QDivisibilityResidueCoefficients
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.LinearAlgebra.CenteredNormalEquations
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Genuine inverse covariance coordinates for squarefree approximation

Source: user-provided squarefree-coordinate and covariance argument, continued
16 October 2026. Finite normal equations and completion of the square supply
the proof strategy; the arithmetic wavelet Parseval identity is the existing
project result in `QDivisorHilbertBasis`.

The masked dictionary in `QSquarefreeCapacity` includes zero vectors at
nonsquarefree entries. Here `Index n` removes precisely those entries.
Its conductors are the distinct squarefree integers from 2 through n+1,
so the existing positive-definiteness theorem makes covariance inversion
genuine at every finite stage.

The resulting capacity is exactly the existing geometric capacity.
The optimizer, full Parseval error, determinant-ratio error, and epsilon
approximation criterion are proved without an arithmetic hypothesis.
The RH conclusions remain conditional on capacity divergence or arbitrarily
small actual approximation error. Neither arithmetic provider is proved here.
The RH-to-squarefree-density converse is also not supplied by this module.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeInverseCapacity
open ZetaTwoHilbert ZetaTwoOptimizerStage QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.LinearAlgebra
open RiemannResearch.LinearAlgebra.CenteredNormalEquations
open RiemannResearch.Analysis.ExhaustiveWalk

abbrev Index (n : ℕ) := {i : Fin n // Squarefree (i.val + 2)}
def conductor (n : ℕ) (i : Index n) : ℕ := i.val.val + 2

theorem conductor_gt_one (n : ℕ) (i : Index n) : 1 < conductor n i := by
  unfold conductor
  omega

theorem conductor_injective (n : ℕ) : Function.Injective (conductor n) := by
  intro i j h
  apply Subtype.ext
  apply Fin.ext
  change i.val.val + 2 = j.val.val + 2 at h
  omega

theorem residue_span_eq_stage (n : ℕ) :
    Submodule.span ℝ (Set.range (fun i : Index n => qResidue (conductor n i))) = stage n := by
  unfold stage walkSpan
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨i.val, ?_⟩
    simp [squarefreeAtom, conductor, i.property]
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change squarefreeAtom i.val ∈ _
    by_cases hi : Squarefree (i.val + 2)
    · rw [squarefreeAtom, if_pos hi]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · simp [squarefreeAtom, hi]

def coefficients (n : ℕ) (i : Index n) : ℝ :=
  covarianceInverseSource (conductor n) i / (1 + covarianceInformation (conductor n))

def candidate (n : ℕ) : QHilbert := qSynthesis (conductor n) (coefficients n)

theorem coefficients_normal (n : ℕ) (i : Index n) :
    inner ℝ (qResidue (conductor n i)) (candidate n) =
      inner ℝ (qResidue (conductor n i)) qOne := by
  rw [candidate, qGram_synthesis]
  rw [qGram_rankOne]
  rw [← real_inner_comm (qResidue (conductor n i)) qOne]
  change action (rankOneAdd (qCov (conductor n)) (qMean (conductor n)))
    (fun j => covarianceInverseSource (conductor n) j /
      (1 + dot (qMean (conductor n)) (covarianceInverseSource (conductor n)))) i =
        qMean (conductor n) i
  apply normalized_normal_equations
  · exact covarianceInverseSource_normal _ (conductor_gt_one n) (conductor_injective n)
  · have h := qInformation_nonneg (conductor n) (covarianceInverseSource (conductor n))
      (covarianceInverseSource_normal _ (conductor_gt_one n) (conductor_injective n))
    linarith

theorem candidate_eq_optimizer (n : ℕ) : candidate n = optimizer n := by
  have hp : optimizer n ∈ Submodule.span ℝ
      (Set.range (fun i : Index n => qResidue (conductor n i))) := by
    rw [residue_span_eq_stage]
    exact (stage n).starProjection_apply_mem qOne
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  have ha' : finiteSchurCombination (fun i : Index n => qResidue (conductor n i)) a =
      optimizer n := ha
  have hn (i : Index n) : inner ℝ (qResidue (conductor n i))
      (finiteSchurCombination (fun j : Index n => qResidue (conductor n j)) a) =
        inner ℝ (qResidue (conductor n i)) qOne := by
    rw [ha']
    have hi : qResidue (conductor n i) ∈ stage n := by
      rw [← residue_span_eq_stage]
      exact Submodule.subset_span ⟨i, rfl⟩
    have ho := ((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hi
    change inner ℝ (qResidue (conductor n i)) (qOne - optimizer n) = 0 at ho
    rw [inner_sub_right] at ho
    linarith
  have h1 := finiteSchurResidual_completion qOne
    (fun i : Index n => qResidue (conductor n i)) a (coefficients n)
    (coefficients_normal n)
  have h2 := finiteSchurResidual_completion qOne
    (fun i : Index n => qResidue (conductor n i)) (coefficients n) a hn
  change ‖qOne - finiteSchurCombination (fun i : Index n => qResidue (conductor n i)) a‖ ^ 2 =
    ‖qOne - candidate n‖ ^ 2 +
      ‖finiteSchurCombination (fun i : Index n => qResidue (conductor n i)) a -
        candidate n‖ ^ 2 at h1
  change ‖qOne - candidate n‖ ^ 2 =
    ‖qOne - finiteSchurCombination (fun i : Index n => qResidue (conductor n i)) a‖ ^ 2 +
      ‖candidate n -
        finiteSchurCombination (fun i : Index n => qResidue (conductor n i)) a‖ ^ 2 at h2
  rw [ha'] at h1 h2
  rw [norm_sub_rev (optimizer n) (candidate n)] at h1
  have hz : ‖candidate n - optimizer n‖ ^ 2 = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The genuine inverse covariance energy of the distinct squarefree family. -/
def inverseCapacity (n : ℕ) : ℝ := covarianceInformation (conductor n)

theorem inverseCapacity_nonneg (n : ℕ) : 0 ≤ inverseCapacity n :=
  qInformation_nonneg (conductor n) (covarianceInverseSource (conductor n))
    (covarianceInverseSource_normal _ (conductor_gt_one n) (conductor_injective n))

theorem error_eq_reciprocal (n : ℕ) :
    error n = 1 / (1 + inverseCapacity n) := by
  change ‖qOne - optimizer n‖ ^ 2 = _
  rw [← candidate_eq_optimizer]
  exact qError_genuine_inverse _ (conductor_gt_one n) (conductor_injective n)

theorem inverseCapacity_eq_capacity (n : ℕ) :
    inverseCapacity n = QSquarefreeCapacity.capacity n := by
  have hden : 1 + inverseCapacity n ≠ 0 := by
    have h := inverseCapacity_nonneg n
    linarith
  unfold QSquarefreeCapacity.capacity
  rw [error_eq_reciprocal]
  field_simp [hden]
  ring

theorem inverseCapacity_monotone : Monotone inverseCapacity := by
  intro m n hmn
  rw [inverseCapacity_eq_capacity, inverseCapacity_eq_capacity]
  exact QSquarefreeCapacity.capacity_monotone hmn

theorem error_eq_determinant_ratio (n : ℕ) :
    error n = (residueCovarianceMatrix (conductor n)).det /
      (residueGramMatrix (conductor n)).det := by
  change ‖qOne - optimizer n‖ ^ 2 = _
  rw [← candidate_eq_optimizer]
  exact qError_eq_determinant_ratio _ (conductor_gt_one n) (conductor_injective n)

/-- The full arithmetic coordinate energy, including the constant mode. -/
theorem candidate_parseval_error (n : ℕ) :
    (∑' r : ℕ+, ((if r = 1 then (1 : ℝ) else 0) -
      ∑ i : Index n, coefficients n i *
        qResidueDivisorCoefficient (conductor n i) (r : ℕ)) ^ 2 /
          qJordanTwo (r : ℕ)) = 1 / (1 + inverseCapacity n) := by
  rw [QDivisorHilbert.qSynthesis_error_parseval]
  exact qError_genuine_inverse _ (conductor_gt_one n) (conductor_injective n)

theorem inverseCapacity_tendsto_iff_squarefree_closure :
    Filter.Tendsto inverseCapacity Filter.atTop Filter.atTop ↔
      qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure := by
  have he : inverseCapacity = QSquarefreeCapacity.capacity :=
    funext inverseCapacity_eq_capacity
  rw [he]
  exact QSquarefreeCapacity.capacity_tendsto_iff_squarefree_closure

/-- This is an exact epsilon criterion, without an exact-head requirement. -/
theorem squarefree_closure_iff_forall_epsilon :
    qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure ↔
      ∀ ε : ℝ, 0 < ε → ∃ n, 1 / (1 + inverseCapacity n) < ε := by
  rw [← QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  rw [← error_tendsto_zero_iff_mem_closure]
  constructor
  · intro ht ε hε
    obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
    exact ⟨n, by simpa only [error_eq_reciprocal] using hn⟩
  · intro h
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => ha.trans (error_pos n))
    · intro b hb
      obtain ⟨n, hn⟩ := h b hb
      rw [← error_eq_reciprocal] at hn
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      have hanti : error m ≤ error n :=
        walkError_antitone squarefreeAtom id qOne hm
      exact hanti.trans_lt hn


/-- Completion of the square retains every optimization remainder. -/
theorem exact_minimum (n : ℕ) (c : Index n → ℝ) :
    ‖qOne - qSynthesis (conductor n) c‖ ^ 2 =
      1 / (1 + inverseCapacity n) +
        ‖qSynthesis (conductor n) c - candidate n‖ ^ 2 := by
  have h := finiteSchurResidual_completion qOne
    (fun i : Index n => qResidue (conductor n i)) c (coefficients n)
    (coefficients_normal n)
  change ‖qOne - qSynthesis (conductor n) c‖ ^ 2 =
    ‖qOne - candidate n‖ ^ 2 +
      ‖qSynthesis (conductor n) c - candidate n‖ ^ 2 at h
  have he : ‖qOne - candidate n‖ ^ 2 = 1 / (1 + inverseCapacity n) := by
    rw [candidate_eq_optimizer]
    exact error_eq_reciprocal n
  rwa [he] at h

/-- Every inverse-covariance candidate is literally a finite legal synthesis. -/
theorem candidate_mem_squarefree_span (n : ℕ) :
    candidate n ∈ ZetaTwoProbability.qSquarefreeCRTSpan := by
  unfold candidate qSynthesis
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span
    ⟨⟨conductor n i, by unfold conductor; omega, i.property⟩, rfl⟩

/-- Equivalent epsilon formulation with arbitrary finite legal coefficients. -/
theorem squarefree_closure_iff_legal_epsilon :
    qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure ↔
      ∀ ε : ℝ, 0 < ε → ∃ n, ∃ c : Index n → ℝ,
        ‖qOne - qSynthesis (conductor n) c‖ ^ 2 < ε := by
  rw [squarefree_closure_iff_forall_epsilon]
  constructor
  · intro h ε hε
    obtain ⟨n, hn⟩ := h ε hε
    refine ⟨n, coefficients n, ?_⟩
    change ‖qOne - candidate n‖ ^ 2 < ε
    rw [candidate_eq_optimizer]
    change error n < ε
    rwa [error_eq_reciprocal]
  · intro h ε hε
    obtain ⟨n, c, hc⟩ := h ε hε
    refine ⟨n, ?_⟩
    rw [exact_minimum] at hc
    exact lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg _)) hc

theorem riemannHypothesis_of_inverseCapacity_tendsto
    (h : Filter.Tendsto inverseCapacity Filter.atTop Filter.atTop) : RiemannHypothesis := by
  apply QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
  have he : inverseCapacity = QSquarefreeCapacity.capacity :=
    funext inverseCapacity_eq_capacity
  rw [he] at h
  exact h

/-- The missing arithmetic estimate is explicit in the hypothesis. -/
theorem riemannHypothesis_of_forall_epsilon
    (h : ∀ ε : ℝ, 0 < ε → ∃ n, 1 / (1 + inverseCapacity n) < ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_inverseCapacity_tendsto
    (inverseCapacity_tendsto_iff_squarefree_closure.mpr
      (squarefree_closure_iff_forall_epsilon.mpr h))

end RiemannResearch.RH.QSquarefreeInverseCapacity
