import RiemannResearch.RH.QSquarefreeInverseCapacity
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Primorial cofinality for the Q squarefree legal spaces

Source: user-provided cofinality argument, 16 October 2026.

This file compares finite *spans* only. It deliberately makes no additive
CRT decomposition of residue atoms: the carry terms in such a decomposition
are not discarded. In particular, no capacity-divergence estimate is proved here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreePrimorialCofinality

open ZetaTwoHilbert ZetaTwoProbability
open QSquarefreeInverseCapacity
open Pareto.SquarefreeStageExhaustion

/-- The legal span indexed by the divisors greater than one of a primorial. -/
def primorialStage (n : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ {f | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧ f = qResidue d}

theorem exhaustive_le_primorial (n : ℕ) :
    ZetaTwoOptimizerStage.stage n ≤ primorialStage (n + 1) := by
  rw [← residue_span_eq_stage]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨conductor n i, conductor_gt_one n i, ?_, rfl⟩
  apply squarefree_dvd_primorialPeriod
  · exact i.property
  · unfold conductor
    omega

theorem primorial_le_exhaustive (n : ℕ) :
    primorialStage n ≤ ZetaTwoOptimizerStage.stage (primorialPeriod n + 1) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, hdvd, rfl⟩
  rw [← residue_span_eq_stage]
  apply Submodule.subset_span
  have hpos : 0 < primorialPeriod n := primorialPeriod_pos n
  have hdle : d ≤ primorialPeriod n := Nat.le_of_dvd hpos hdvd
  have hsq : Squarefree d := (primorialPeriod_squarefree n).squarefree_of_dvd hdvd
  let i : Fin (primorialPeriod n + 1) := ⟨d - 2, by omega⟩
  have hi : Squarefree (i.val + 2) := by
    change Squarefree (d - 2 + 2)
    convert hsq using 1; omega
  refine ⟨⟨i, hi⟩, ?_⟩
  change qResidue (i.val + 2) = qResidue d
  congr 1
  change d - 2 + 2 = d
  omega

/-- The primorial family lies inside the literal squarefree legal span. -/
theorem primorialStage_le_squarefreeSpan (n : ℕ) :
    primorialStage n ≤ qSquarefreeCRTSpan := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, hdvd, rfl⟩
  have hsq : Squarefree d := (primorialPeriod_squarefree n).squarefree_of_dvd hdvd
  exact Submodule.subset_span ⟨⟨d, by omega, hsq⟩, rfl⟩

/-- Every finite exhaustive stage is covered by a later primorial stage. -/
theorem exhaustive_eventually_le_primorial (n : ℕ) :
    ∃ m, ZetaTwoOptimizerStage.stage n ≤ primorialStage m :=
  ⟨n + 1, exhaustive_le_primorial n⟩

/-- Every primorial stage is covered by an exhaustive squarefree stage. -/
theorem primorial_eventually_le_exhaustive (n : ℕ) :
    ∃ m, primorialStage n ≤ ZetaTwoOptimizerStage.stage m :=
  ⟨primorialPeriod n + 1, primorial_le_exhaustive n⟩

theorem primorialStage_mono : Monotone primorialStage := by
  intro n m hnm
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, hdvd, rfl⟩
  exact Submodule.subset_span
    ⟨d, hd, dvd_trans hdvd (primorialPeriod_nested hnm), rfl⟩

/-- Cofinality is equality of the algebraic unions of finite legal spans. -/
theorem iSup_exhaustive_eq_primorial :
    (⨆ n, ZetaTwoOptimizerStage.stage n) = ⨆ n, primorialStage n := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact (exhaustive_le_primorial n).trans (le_iSup primorialStage (n + 1))
  · refine iSup_le fun n => ?_
    exact (primorial_le_exhaustive n).trans
      (le_iSup ZetaTwoOptimizerStage.stage (primorialPeriod n + 1))

/-- Primorial divisors exhaust the literal squarefree legal span. -/
theorem iSup_primorial_eq_squarefreeSpan :
    (⨆ n, primorialStage n) = qSquarefreeCRTSpan := by
  apply le_antisymm
  · exact iSup_le primorialStage_le_squarefreeSpan
  · unfold qSquarefreeCRTSpan
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    apply (le_iSup primorialStage d.val)
    apply Submodule.subset_span
    refine ⟨d.val, by have := d.property.1; omega, ?_, rfl⟩
    exact squarefree_dvd_primorialPeriod d.val d.val d.property.2 le_rfl

theorem primorial_closedSpan_eq_squarefree_closedSpan :
    (⨆ n, primorialStage n).topologicalClosure =
      qSquarefreeCRTSpan.topologicalClosure := by
  rw [iSup_primorial_eq_squarefreeSpan]

/-- The generator set is finite because its conductors divide one nonzero period. -/
instance primorialStage_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (primorialStage n) := by
  unfold primorialStage
  let s : Finset ℕ := (primorialPeriod n).divisors
  have hs : Set.Finite {f : QHilbert |
      ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧ f = qResidue d} := by
    have hr : Set.Finite
        (Set.range (fun d : {d : ℕ // d ∈ s} => qResidue d.val)) :=
      Set.finite_range _
    apply hr.subset
    rintro f ⟨d, hd, hdvd, rfl⟩
    refine ⟨⟨d, ?_⟩, rfl⟩
    exact Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt (primorialPeriod_pos n)⟩
  exact FiniteDimensional.span_of_finite ℝ hs

def primorialOptimizer (n : ℕ) : QHilbert :=
  (primorialStage n).starProjection qOne

def primorialError (n : ℕ) : ℝ :=
  ‖qOne - primorialOptimizer n‖ ^ 2

theorem primorialOptimizer_tendsto :
    Filter.Tendsto primorialOptimizer Filter.atTop
      (𝓝 (qSquarefreeCRTSpan.topologicalClosure.starProjection qOne)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    primorialStage primorialStage_mono qOne
  change Filter.Tendsto (fun n => (primorialStage n).starProjection qOne)
    Filter.atTop (𝓝 (qSquarefreeCRTSpan.topologicalClosure.starProjection qOne))
  simpa only [iSup_primorial_eq_squarefreeSpan] using h

theorem primorialError_tendsto :
    Filter.Tendsto primorialError Filter.atTop
      (𝓝 (‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖ ^ 2)) := by
  exact (tendsto_const_nhds.sub primorialOptimizer_tendsto).norm.pow 2

theorem exhaustiveError_tendsto_same :
    Filter.Tendsto ZetaTwoOptimizerStage.error Filter.atTop
      (𝓝 (‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖ ^ 2)) := by
  have h := ZetaTwoOptimizerStage.residual_tendsto.norm.pow 2
  change Filter.Tendsto ZetaTwoOptimizerStage.error Filter.atTop
    (𝓝 (‖qOne - ZetaTwoOptimizerStage.closure.starProjection qOne‖ ^ 2)) at h
  simpa only [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure] using h

/-- The exact projection remainder retained under the stage inclusion. -/
theorem primorial_error_eq_exhaustive_error_add (n : ℕ) :
    primorialError n =
      ZetaTwoOptimizerStage.error (primorialPeriod n + 1) +
        ‖ZetaTwoOptimizerStage.optimizer (primorialPeriod n + 1) -
          primorialOptimizer n‖ ^ 2 := by
  exact RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (primorialStage n) (ZetaTwoOptimizerStage.stage (primorialPeriod n + 1))
    (primorial_le_exhaustive n) qOne

/-- The reverse comparison retains the full optimizer-displacement square. -/
theorem exhaustive_error_eq_primorial_error_add (n : ℕ) :
    ZetaTwoOptimizerStage.error n =
      primorialError (n + 1) +
        ‖primorialOptimizer (n + 1) - ZetaTwoOptimizerStage.optimizer n‖ ^ 2 := by
  exact RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (ZetaTwoOptimizerStage.stage n) (primorialStage (n + 1))
    (exhaustive_le_primorial n) qOne

theorem primorialError_pos (n : ℕ) : 0 < primorialError n := by
  have h := primorial_error_eq_exhaustive_error_add n
  have he := ZetaTwoOptimizerStage.error_pos (primorialPeriod n + 1)
  nlinarith [sq_nonneg
    ‖ZetaTwoOptimizerStage.optimizer (primorialPeriod n + 1) -
      primorialOptimizer n‖]

def primorialCapacity (n : ℕ) : ℝ :=
  (1 - primorialError n) / primorialError n

theorem primorial_error_eq_reciprocal (n : ℕ) :
    primorialError n = 1 / (1 + primorialCapacity n) := by
  have he : primorialError n ≠ 0 := ne_of_gt (primorialError_pos n)
  have hd : 1 + primorialCapacity n ≠ 0 := by
    have hh : 1 + primorialCapacity n = 1 / primorialError n := by
      unfold primorialCapacity
      field_simp [he]
      ring
    rw [hh]
    exact ne_of_gt (div_pos zero_lt_one (primorialError_pos n))
  apply (eq_div_iff hd).mpr
  unfold primorialCapacity
  field_simp [he]
  ring

theorem primorialError_tendsto_zero_iff :
    Filter.Tendsto primorialError Filter.atTop (𝓝 0) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro hzero
    have hlim := tendsto_nhds_unique primorialError_tendsto hzero
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm,
      Submodule.starProjection_eq_self_iff] at hlim
    exact hlim
  · intro hmem
    have he : ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖ ^ 2 = 0 := by
      rw [Submodule.starProjection_eq_self_iff.mpr hmem, sub_self, norm_zero]
      norm_num
    simpa only [he] using primorialError_tendsto

theorem primorialCapacity_tendsto_iff_error_tendsto :
    Tendsto primorialCapacity atTop atTop ↔
      Tendsto primorialError atTop (𝓝 0) := by
  constructor
  · intro ht
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => ha.trans (primorialError_pos n))
    · intro b hb
      filter_upwards [(tendsto_atTop.mp ht) (1 / b)] with n hn
      change 1 / b ≤ (1 - primorialError n) / primorialError n at hn
      have h := (le_div_iff₀ (primorialError_pos n)).mp hn
      have h' : primorialError n / b ≤ 1 - primorialError n := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using h
      have h'' := (div_le_iff₀ hb).mp h'
      nlinarith [mul_pos hb (primorialError_pos n)]
  · intro he
    apply tendsto_atTop.2
    intro B
    have hp : 0 < max B 0 + 2 := by positivity
    have hε : 0 < 1 / (max B 0 + 2) := by positivity
    filter_upwards [he.eventually (Iio_mem_nhds hε)] with n hn
    change B ≤ (1 - primorialError n) / primorialError n
    apply (le_div_iff₀ (primorialError_pos n)).mpr
    have h := (lt_div_iff₀ hp).mp hn
    have hB := mul_le_mul_of_nonneg_right (le_max_left B 0)
      (primorialError_pos n).le
    nlinarith [primorialError_pos n]

/-- Both capacity divergences have the same unresolved arithmetic content. -/
theorem primorialCapacity_tendsto_iff_exhaustive :
    Tendsto primorialCapacity atTop atTop ↔
      Tendsto inverseCapacity atTop atTop :=
  primorialCapacity_tendsto_iff_error_tendsto.trans
    (primorialError_tendsto_zero_iff.trans
      inverseCapacity_tendsto_iff_squarefree_closure.symm)

/-- Actual distinct divisors of the squarefree common period, excluding one. -/
abbrev DivisorIndex (n : ℕ) :=
  {d : ℕ // d ∈ (primorialPeriod n).divisors ∧ 1 < d}

instance divisorIndex_fintype (n : ℕ) : Fintype (DivisorIndex n) := by
  classical
  let e : DivisorIndex n → Fin (primorialPeriod n + 1) := fun i =>
    ⟨i.val, by
      have hdvd : i.val ∣ primorialPeriod n := (Nat.mem_divisors.mp i.property.1).1
      exact Nat.lt_succ_of_le (Nat.le_of_dvd (primorialPeriod_pos n) hdvd)⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    exact congrArg Fin.val h
  exact Fintype.ofInjective e he

def divisorConductor (n : ℕ) (i : DivisorIndex n) : ℕ := i.val

theorem divisorConductor_gt_one (n : ℕ) (i : DivisorIndex n) :
    1 < divisorConductor n i := i.property.2

theorem divisorConductor_injective (n : ℕ) :
    Function.Injective (divisorConductor n) := by
  intro i j hij
  exact Subtype.ext hij

theorem divisor_span_eq_primorialStage (n : ℕ) :
    Submodule.span ℝ
      (Set.range (fun i : DivisorIndex n => qResidue (divisorConductor n i))) =
        primorialStage n := by
  unfold primorialStage
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨i.val, i.property.2,
      (Nat.mem_divisors.mp i.property.1).1, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, hdvd, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨d, ?_, hd⟩, rfl⟩
    exact Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt (primorialPeriod_pos n)⟩

/-- The divisor list embeds into the larger exhaustive covariance system. -/
def toExhaustive (n : ℕ) (i : DivisorIndex n) :
    QSquarefreeInverseCapacity.Index (primorialPeriod n + 1) := by
  have hdvd : i.val ∣ primorialPeriod n := (Nat.mem_divisors.mp i.property.1).1
  have hle : i.val ≤ primorialPeriod n :=
    Nat.le_of_dvd (primorialPeriod_pos n) hdvd
  refine ⟨⟨i.val - 2, by omega⟩, ?_⟩
  change Squarefree (i.val - 2 + 2)
  have hsq : Squarefree i.val :=
    (primorialPeriod_squarefree n).squarefree_of_dvd hdvd
  convert hsq using 1; omega

theorem conductor_toExhaustive (n : ℕ) (i : DivisorIndex n) :
    conductor (primorialPeriod n + 1) (toExhaustive n i) =
      divisorConductor n i := by
  change i.val - 2 + 2 = i.val
  omega

theorem toExhaustive_injective (n : ℕ) :
    Function.Injective (toExhaustive n) := by
  intro i j hij
  have h := congrArg (conductor (primorialPeriod n + 1)) hij
  rw [conductor_toExhaustive, conductor_toExhaustive] at h
  exact divisorConductor_injective n h

theorem mean_principal (n : ℕ) (i : DivisorIndex n) :
    QCovarianceInverse.qMean (divisorConductor n) i =
      QCovarianceInverse.qMean (conductor (primorialPeriod n + 1))
        (toExhaustive n i) := by
  simp only [QCovarianceInverse.qMean, conductor_toExhaustive]

theorem covariance_principal (n : ℕ) (i j : DivisorIndex n) :
    QCovarianceInverse.qCov (divisorConductor n) i j =
      QCovarianceInverse.qCov (conductor (primorialPeriod n + 1))
        (toExhaustive n i) (toExhaustive n j) := by
  simp only [QCovarianceInverse.qCov, QCovarianceInverse.qGram,
    QCovarianceInverse.qMean, conductor_toExhaustive]

theorem covarianceMatrix_principal (n : ℕ) (i j : DivisorIndex n) :
    QCovarianceInvertibility.residueCovarianceMatrix (divisorConductor n) i j =
      QCovarianceInvertibility.residueCovarianceMatrix
        (conductor (primorialPeriod n + 1))
        (toExhaustive n i) (toExhaustive n j) :=
  covariance_principal n i j

/-- The actual covariance-inverse optimizer coefficients on the divisor list. -/
def divisorCoefficients (n : ℕ) (i : DivisorIndex n) : ℝ :=
  QCovarianceInvertibility.covarianceInverseSource (divisorConductor n) i /
    (1 + QCovarianceInvertibility.covarianceInformation (divisorConductor n))

def divisorCandidate (n : ℕ) : QHilbert :=
  QCovarianceInverse.qSynthesis (divisorConductor n) (divisorCoefficients n)

theorem divisorCoefficients_normal (n : ℕ) (i : DivisorIndex n) :
    inner ℝ (qResidue (divisorConductor n i)) (divisorCandidate n) =
      inner ℝ (qResidue (divisorConductor n i)) qOne := by
  rw [divisorCandidate, QCovarianceInverse.qGram_synthesis]
  rw [QCovarianceInverse.qGram_rankOne]
  rw [← real_inner_comm (qResidue (divisorConductor n i)) qOne]
  change RiemannResearch.LinearAlgebra.CenteredNormalEquations.action
      (RiemannResearch.LinearAlgebra.CenteredNormalEquations.rankOneAdd
        (QCovarianceInverse.qCov (divisorConductor n))
        (QCovarianceInverse.qMean (divisorConductor n)))
      (fun j => QCovarianceInvertibility.covarianceInverseSource
        (divisorConductor n) j /
        (1 + RiemannResearch.LinearAlgebra.CenteredNormalEquations.dot
          (QCovarianceInverse.qMean (divisorConductor n))
          (QCovarianceInvertibility.covarianceInverseSource
            (divisorConductor n)))) i =
        QCovarianceInverse.qMean (divisorConductor n) i
  apply RiemannResearch.LinearAlgebra.CenteredNormalEquations.normalized_normal_equations
  · exact QCovarianceInvertibility.covarianceInverseSource_normal _
      (divisorConductor_gt_one n) (divisorConductor_injective n)
  · have h := QCovarianceInverse.qInformation_nonneg (divisorConductor n)
      (QCovarianceInvertibility.covarianceInverseSource (divisorConductor n))
      (QCovarianceInvertibility.covarianceInverseSource_normal _
        (divisorConductor_gt_one n) (divisorConductor_injective n))
    linarith

theorem divisorCandidate_eq_primorialOptimizer (n : ℕ) :
    divisorCandidate n = primorialOptimizer n := by
  have hp : primorialOptimizer n ∈ Submodule.span ℝ
      (Set.range (fun i : DivisorIndex n => qResidue (divisorConductor n i))) := by
    rw [divisor_span_eq_primorialStage]
    exact (primorialStage n).starProjection_apply_mem qOne
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  have ha' : RiemannResearch.LinearAlgebra.finiteSchurCombination
      (fun i : DivisorIndex n => qResidue (divisorConductor n i)) a =
        primorialOptimizer n := ha
  have hn (i : DivisorIndex n) :
      inner ℝ (qResidue (divisorConductor n i))
        (RiemannResearch.LinearAlgebra.finiteSchurCombination
          (fun j : DivisorIndex n => qResidue (divisorConductor n j)) a) =
        inner ℝ (qResidue (divisorConductor n i)) qOne := by
    rw [ha']
    have hi : qResidue (divisorConductor n i) ∈ primorialStage n := by
      rw [← divisor_span_eq_primorialStage]
      exact Submodule.subset_span ⟨i, rfl⟩
    have ho := ((primorialStage n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal qOne) _ hi
    change inner ℝ (qResidue (divisorConductor n i))
      (qOne - primorialOptimizer n) = 0 at ho
    rw [inner_sub_right] at ho
    linarith
  have h1 := RiemannResearch.LinearAlgebra.finiteSchurResidual_completion qOne
    (fun i : DivisorIndex n => qResidue (divisorConductor n i)) a
    (divisorCoefficients n) (divisorCoefficients_normal n)
  have h2 := RiemannResearch.LinearAlgebra.finiteSchurResidual_completion qOne
    (fun i : DivisorIndex n => qResidue (divisorConductor n i))
    (divisorCoefficients n) a hn
  change ‖qOne -
    RiemannResearch.LinearAlgebra.finiteSchurCombination
      (fun i : DivisorIndex n => qResidue (divisorConductor n i)) a‖ ^ 2 =
    ‖qOne - divisorCandidate n‖ ^ 2 +
    ‖RiemannResearch.LinearAlgebra.finiteSchurCombination
      (fun i : DivisorIndex n => qResidue (divisorConductor n i)) a -
      divisorCandidate n‖ ^ 2 at h1
  change ‖qOne - divisorCandidate n‖ ^ 2 =
    ‖qOne -
      RiemannResearch.LinearAlgebra.finiteSchurCombination
        (fun i : DivisorIndex n => qResidue (divisorConductor n i)) a‖ ^ 2 +
    ‖divisorCandidate n -
      RiemannResearch.LinearAlgebra.finiteSchurCombination
        (fun i : DivisorIndex n => qResidue (divisorConductor n i)) a‖ ^ 2 at h2
  rw [ha'] at h1 h2
  rw [norm_sub_rev (primorialOptimizer n) (divisorCandidate n)] at h1
  have hz : ‖divisorCandidate n - primorialOptimizer n‖ ^ 2 = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem primorialCapacity_eq_covarianceInformation (n : ℕ) :
    primorialCapacity n =
      QCovarianceInvertibility.covarianceInformation (divisorConductor n) := by
  have hnonneg := QCovarianceInverse.qInformation_nonneg (divisorConductor n)
    (QCovarianceInvertibility.covarianceInverseSource (divisorConductor n))
    (QCovarianceInvertibility.covarianceInverseSource_normal _
      (divisorConductor_gt_one n) (divisorConductor_injective n))
  have hden : 1 +
      QCovarianceInvertibility.covarianceInformation (divisorConductor n) ≠ 0 := by
    change 1 + RiemannResearch.LinearAlgebra.CenteredNormalEquations.dot
      (QCovarianceInverse.qMean (divisorConductor n))
      (QCovarianceInvertibility.covarianceInverseSource (divisorConductor n)) ≠ 0
    linarith
  have he : primorialError n =
      1 / (1 + QCovarianceInvertibility.covarianceInformation
        (divisorConductor n)) := by
    change ‖qOne - primorialOptimizer n‖ ^ 2 = _
    rw [← divisorCandidate_eq_primorialOptimizer]
    exact QCovarianceInvertibility.qError_genuine_inverse _
      (divisorConductor_gt_one n) (divisorConductor_injective n)
  unfold primorialCapacity
  rw [he]
  field_simp [hden]
  ring

theorem divisorCoefficients_eq_gramInverse (n : ℕ) :
    divisorCoefficients n =
      (QCovarianceInvertibility.residueGramMatrix
        (divisorConductor n))⁻¹.mulVec
          (QCovarianceInverse.qMean (divisorConductor n)) := by
  funext i
  exact congrFun
    ((QCovarianceInvertibility.gramInverseSource_eq_normalized_covariance _
      (divisorConductor_gt_one n) (divisorConductor_injective n)).symm) i

theorem primorial_error_step (n : ℕ) :
    primorialError n = primorialError (n + 1) +
      ‖primorialOptimizer (n + 1) - primorialOptimizer n‖ ^ 2 := by
  exact RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (primorialStage n) (primorialStage (n + 1))
    (primorialStage_mono (Nat.le_succ n)) qOne

/-- Exact Schur gain, without dropping the norm-square remainder. -/
theorem primorial_capacity_increment (n : ℕ) :
    primorialCapacity (n + 1) - primorialCapacity n =
      ‖primorialOptimizer (n + 1) - primorialOptimizer n‖ ^ 2 /
        (primorialError n * primorialError (n + 1)) := by
  have h := primorial_error_step n
  unfold primorialCapacity
  field_simp [ne_of_gt (primorialError_pos n),
    ne_of_gt (primorialError_pos (n + 1))]
  nlinarith

/-- The finite covariance-information gain from adding all omitted
squarefree conductors in the containing exhaustive stage. -/
theorem exhaustive_minus_primorial_capacity (n : ℕ) :
    inverseCapacity (primorialPeriod n + 1) - primorialCapacity n =
      ‖ZetaTwoOptimizerStage.optimizer (primorialPeriod n + 1) -
        primorialOptimizer n‖ ^ 2 /
        (primorialError n * ZetaTwoOptimizerStage.error
          (primorialPeriod n + 1)) := by
  have h := primorial_error_eq_exhaustive_error_add n
  rw [QSquarefreeInverseCapacity.inverseCapacity_eq_capacity]
  unfold QSquarefreeCapacity.capacity primorialCapacity
  field_simp [ne_of_gt (primorialError_pos n),
    ne_of_gt (ZetaTwoOptimizerStage.error_pos (primorialPeriod n + 1))]
  nlinarith

end RiemannResearch.RH.QSquarefreePrimorialCofinality
