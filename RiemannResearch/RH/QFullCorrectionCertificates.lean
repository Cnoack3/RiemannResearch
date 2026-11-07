/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullCrossedDistances
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QParetoSquareRootEnergy
import RiemannResearch.RH.QParetoSquareRootCompactness
import RiemannResearch.RH.QParetoIsometricTransport
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.Analysis.OrthogonalDistanceBound
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Complete finite Gram corrections for the common square-root target

Source: CrossedDistanceLeanHandoff20261106.md, Priority 1. The finite
coefficients minimize the complete Hilbert norm. No probability-law tail
is truncated. Finite-head targets have finite cross pairings, but their
Gram matrices remain the complete matrices. The limits are projections
onto the two actual target spaces; no vanishing-distance provider is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QFullCorrectionCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QParetoClosedProjectionComparison QFullCrossedDistances
open QCovarianceInverse QCovarianceInvertibility
open QFullResidueProjection QFullDisplacement QParetoIsometricTransport
open QFiniteSupportDualCriterion
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk

def correctionCoefficients (N : ℕ) (x : QHilbert) : Fin N → ℝ :=
  inverseCoeff (qResidue_linearIndependent (conductor N)
    (conductor_gt_one N) (conductor_injective N)) x

/-- The coefficients are the ordinary inverse of the complete finite Q Gram matrix. -/
theorem correctionCoefficients_eq_inv_mulVec (N : ℕ) (x : QHilbert) :
    correctionCoefficients N x =
      (gramMatrix (fun i : Fin N => qResidue (conductor N i)))⁻¹.mulVec
        (cross (fun i : Fin N => qResidue (conductor N i)) x) :=
  inverseCoeff_eq_inv_mulVec (qResidue_linearIndependent (conductor N)
    (conductor_gt_one N) (conductor_injective N)) x

def correction (N : ℕ) (x : QHilbert) : QHilbert :=
  qSynthesis (conductor N) (correctionCoefficients N x)

theorem correction_eq_projection (N : ℕ) (x : QHilbert) :
    correction N x = (stage N).starProjection x := by
  simpa only [correction, correctionCoefficients, qSynthesis,
    Fintype.linearCombination_apply, synthesisSpan, stage, walkSpan, conductor, id_eq]
    using synthesis_inverseCoeff_eq_projection
      (qResidue_linearIndependent (conductor N)
        (conductor_gt_one N) (conductor_injective N)) x

theorem correction_mem_legalSpan (N : ℕ) (x : QHilbert) :
    correction N x ∈ legalSpan := by
  rw [correction_eq_projection]
  exact walkSpan_le (fun i => qResidue (i + 2)) id N
    ((stage N).starProjection_apply_mem x)

theorem correction_mem_closure (N : ℕ) (x : QHilbert) :
    correction N x ∈ closure :=
  legalSpan.le_topologicalClosure (correction_mem_legalSpan N x)

theorem correction_tendsto (x : QHilbert) :
    Tendsto (fun N => correction N x) atTop (𝓝 (closure.starProjection x)) := by
  have h := walkProjection_tendsto (fun i => qResidue (i + 2))
    id Function.surjective_id x
  simpa only [correction_eq_projection, stage, QFullResidueProjection.closure,
    QFullResidueProjection.legalSpan, dictionaryClosure] using h

/-- Actual finite legal approximants to the full-conductor displacement. -/
theorem displacement_correction_tendsto :
    Tendsto (fun N => correction N displacement) atTop (𝓝 displacement) := by
  simpa only [Submodule.starProjection_eq_self_iff.mpr displacement_mem]
    using correction_tendsto displacement

/-- The complete inverse-Gram objective, including every coordinate of each atom. -/
theorem correction_error_exact (N : ℕ) (x : QHilbert) :
    ‖x - correction N x‖ ^ 2 = ‖x‖ ^ 2 -
      ∑ i, correctionCoefficients N x i * inner ℝ (qResidue (conductor N i)) x := by
  simpa only [correction, correctionCoefficients, qSynthesis,
    Fintype.linearCombination_apply, cross] using
    residual_schur_value (qResidue_linearIndependent (conductor N)
      (conductor_gt_one N) (conductor_injective N)) x

/-- Exact completion retains the full nonnegative coefficient-error term. -/
theorem correction_completion (N : ℕ) (x : QHilbert) (c : Fin N → ℝ) :
    ‖x - qSynthesis (conductor N) c‖ ^ 2 = ‖x - correction N x‖ ^ 2 +
      ‖qSynthesis (conductor N) (c - correctionCoefficients N x)‖ ^ 2 := by
  simpa only [correction, correctionCoefficients, qSynthesis,
    Fintype.linearCombination_apply] using
    residual_completion (qResidue_linearIndependent (conductor N)
      (conductor_gt_one N) (conductor_injective N)) x c

theorem correction_error_tendsto (x : QHilbert) :
    Tendsto (fun N => ‖x - correction N x‖ ^ 2) atTop
      (𝓝 (‖x - closure.starProjection x‖ ^ 2)) :=
  (tendsto_const_nhds.sub (correction_tendsto x)).norm.pow 2

private theorem inverse_atoms_independent (N : ℕ) :
    LinearIndependent ℝ (fun i : Fin N => inversePhysical (qResidue (conductor N i))) := by
  have hi : Function.Injective inversePhysical := by
    intro f g h
    apply paretoEquiv.injective
    change inversePhysical f = inversePhysical g
    exact h
  exact (qResidue_linearIndependent (conductor N)
    (conductor_gt_one N) (conductor_injective N)).map'
      inversePhysical.toLinearMap (LinearMap.ker_eq_bot.mpr hi)

def inverseStage (N : ℕ) : Submodule ℝ QHilbert :=
  walkSpan (fun i => inversePhysical (qResidue (i + 2))) id N

instance inverseStage_finiteDimensional (N : ℕ) : FiniteDimensional ℝ (inverseStage N) := by
  unfold inverseStage
  infer_instance

def inverseClosure : Submodule ℝ QHilbert :=
  dictionaryClosure (fun i => inversePhysical (qResidue (i + 2)))

instance inverseClosure_hasOrthogonalProjection : inverseClosure.HasOrthogonalProjection := by
  unfold inverseClosure
  infer_instance

/-- Transporting this Q-encoded inverse image gives the physical Pareto closure. -/
theorem inverseClosure_image : imageSubmodule inverseClosure = paretoClosure := by
  change inverseClosure.map (LinearMap.id : QHilbert →ₗ[ℝ] QHilbert) = paretoClosure
  rw [Submodule.map_id]
  unfold inverseClosure dictionaryClosure paretoClosure legalSpan
  rw [Submodule.map_span]
  have hs : paretoEquiv.toLinearMap '' (Set.range (fun i : ℕ => qResidue (i + 2))) =
      Set.range (fun i : ℕ => inversePhysical (qResidue (i + 2))) := by
    ext f
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨qResidue (i + 2), ⟨i, rfl⟩, rfl⟩
  rw [hs]

def inverseCorrectionCoefficients (N : ℕ) (x : QHilbert) : Fin N → ℝ :=
  inverseCoeff (inverse_atoms_independent N) x

/-- The second solve uses the full Gram matrix of the inversePhysical atoms. -/
theorem inverseCorrectionCoefficients_eq_inv_mulVec (N : ℕ) (x : QHilbert) :
    inverseCorrectionCoefficients N x =
      (gramMatrix (fun i : Fin N => inversePhysical (qResidue (conductor N i))))⁻¹.mulVec
        (cross (fun i : Fin N => inversePhysical (qResidue (conductor N i))) x) :=
  inverseCoeff_eq_inv_mulVec (inverse_atoms_independent N) x

/-- A legal h whose inversePhysical image is the optimal fit to x in the T dictionary. -/
def inverseCorrection (N : ℕ) (x : QHilbert) : QHilbert :=
  qSynthesis (conductor N) (inverseCorrectionCoefficients N x)

theorem inverseCorrection_mem_legalSpan (N : ℕ) (x : QHilbert) :
    inverseCorrection N x ∈ legalSpan := by
  apply walkSpan_le (fun i => qResidue (i + 2)) id N
  simpa only [inverseCorrection, qSynthesis, Fintype.linearCombination_apply,
    synthesisSpan, stage, walkSpan, conductor, id_eq] using
    synthesis_mem (fun i : Fin N => qResidue (conductor N i))
      (inverseCorrectionCoefficients N x)

theorem inverseCorrection_mem_closure (N : ℕ) (x : QHilbert) :
    inverseCorrection N x ∈ closure :=
  legalSpan.le_topologicalClosure (inverseCorrection_mem_legalSpan N x)

theorem inversePhysical_synthesis (N : ℕ) (c : Fin N → ℝ) :
    inversePhysical (qSynthesis (conductor N) c) =
      Fintype.linearCombination ℝ
        (fun i : Fin N => inversePhysical (qResidue (conductor N i))) c := by
  simp only [qSynthesis, map_sum, map_smul, Fintype.linearCombination_apply]

theorem inverseCorrection_eq_projection (N : ℕ) (x : QHilbert) :
    inversePhysical (inverseCorrection N x) = (inverseStage N).starProjection x := by
  rw [inverseCorrection, inversePhysical_synthesis]
  simpa only [inverseCorrectionCoefficients, synthesisSpan, inverseStage,
    walkSpan, conductor, id_eq] using
    synthesis_inverseCoeff_eq_projection (inverse_atoms_independent N) x

theorem inverseCorrection_tendsto (x : QHilbert) :
    Tendsto (fun N => inversePhysical (inverseCorrection N x)) atTop
      (𝓝 (inverseClosure.starProjection x)) := by
  have h := walkProjection_tendsto (fun i => inversePhysical (qResidue (i + 2)))
    id Function.surjective_id x
  simpa only [inverseCorrection_eq_projection, inverseStage, inverseClosure] using h

theorem inverseCorrection_error_exact (N : ℕ) (x : QHilbert) :
    ‖x - inversePhysical (inverseCorrection N x)‖ ^ 2 = ‖x‖ ^ 2 -
      ∑ i, inverseCorrectionCoefficients N x i *
        inner ℝ (inversePhysical (qResidue (conductor N i))) x := by
  rw [inverseCorrection, inversePhysical_synthesis]
  exact residual_schur_value (inverse_atoms_independent N) x

theorem inverseCorrection_completion (N : ℕ) (x : QHilbert) (c : Fin N → ℝ) :
    ‖x - inversePhysical (qSynthesis (conductor N) c)‖ ^ 2 =
      ‖x - inversePhysical (inverseCorrection N x)‖ ^ 2 +
      ‖inversePhysical (qSynthesis (conductor N)
        (c - inverseCorrectionCoefficients N x))‖ ^ 2 := by
  simp only [inverseCorrection, inversePhysical_synthesis]
  exact residual_completion (inverse_atoms_independent N) x c

theorem inverseCorrection_error_tendsto (x : QHilbert) :
    Tendsto (fun N => ‖x - inversePhysical (inverseCorrection N x)‖ ^ 2) atTop
      (𝓝 (‖x - inverseClosure.starProjection x‖ ^ 2)) :=
  (tendsto_const_nhds.sub (inverseCorrection_tendsto x)).norm.pow 2

/-- The second metric fit converges to the actual physical Pareto projection. -/
theorem inverseCorrection_tendsto_pFit (x : QHilbert) :
    Tendsto (fun N => inverseCorrection N (inversePhysical x)) atTop
      (𝓝 (pFit paretoClosure x)) := by
  have he : inverseClosure = paretoClosure := by
    have h := inverseClosure_image
    change inverseClosure.map (LinearMap.id : QHilbert →ₗ[ℝ] QHilbert) = paretoClosure at h
    simpa only [Submodule.map_id] using h
  have h := inverseCorrection_tendsto (inversePhysical x)
  simp only [he] at h
  change Tendsto (fun N => toPareto (inverseCorrection N (inversePhysical x))) atTop
    (𝓝 (paretoClosure.starProjection (toPareto x))) at h
  have ht := (paretoEquiv.symm.continuous.tendsto _).comp h
  change Tendsto (fun N => toQ (toPareto (inverseCorrection N (inversePhysical x)))) atTop
    (𝓝 (toQ (paretoClosure.starProjection (toPareto x)))) at ht
  simpa only [toQ_toPareto, pFit] using ht

/-- Both finite Gram solves use the explicit constant target, not the unknown d. -/
def matchedApprox (N : ℕ) : QHilbert :=
  correction N qOne - inverseCorrection N (inversePhysical qOne)

theorem matchedApprox_mem_legalSpan (N : ℕ) : matchedApprox N ∈ legalSpan :=
  legalSpan.sub_mem (correction_mem_legalSpan N qOne)
    (inverseCorrection_mem_legalSpan N (inversePhysical qOne))

theorem matchedApprox_mem_closure (N : ℕ) : matchedApprox N ∈ closure :=
  legalSpan.le_topologicalClosure (matchedApprox_mem_legalSpan N)

/-- The explicit finite full-metric fits approach the actual matched displacement. -/
theorem matchedApprox_tendsto : Tendsto matchedApprox atTop (𝓝 displacement) := by
  change Tendsto (fun N => correction N qOne - inverseCorrection N (inversePhysical qOne))
    atTop (𝓝 (closure.starProjection qOne - pFit paretoClosure qOne))
  exact (correction_tendsto qOne).sub (inverseCorrection_tendsto_pFit qOne)

def headTarget (M N : ℕ) : QHilbert :=
  rootDefect (finiteHead N (matchedApprox M))

/-- An actual finite Gram certificate, retaining its full infinite remainder. -/
theorem matched_head_certificate (M N H K : ℕ) :
    Real.sqrt (zetaTwo / 2) * ‖displacement‖ ^ 2 + inverseEnergy (matchedApprox M) ≤
      2 * (‖toPareto pResidual‖ *
          (‖headTarget M N - inversePhysical (inverseCorrection H (headTarget M N))‖ +
            ‖matchedApprox M - finiteHead N (matchedApprox M)‖ / (2 * (N : ℝ) + 3)) +
        ‖qResidual‖ * (Real.sqrt zetaTwo *
          (‖headTarget M N - correction K (headTarget M N)‖ +
            ‖matchedApprox M - finiteHead N (matchedApprox M)‖ / (2 * (N : ℝ) + 3)))) +
      Real.sqrt zetaTwo * ‖displacement - matchedApprox M‖ ^ 2 := by
  exact two_distance_head_certificate (matchedApprox M) (finiteHead N (matchedApprox M))
    (inverseCorrection H (headTarget M N)) (correction K (headTarget M N)) N
    (matchedApprox_mem_closure M) (inverseCorrection_mem_closure H _)
    (correction_mem_closure K _)
    (fun n hn => (finiteHead_apply_of_lt N (matchedApprox M) n hn).symm)

/-- The best complete Q correction error approaches the exact crossed distance. -/
theorem correction_rootDefect_error_tendsto (g : QHilbert) (hg : g ∈ closure) :
    Tendsto (fun N => Real.sqrt zetaTwo *
      ‖rootDefect g - correction N (rootDefect g)‖) atTop (𝓝 (inverseDistance g)) := by
  have he : Real.sqrt zetaTwo * ‖rootDefect g - closure.starProjection (rootDefect g)‖ =
      inverseDistance g := by
    rw [inverseDistance_eq_rootDefect g hg,
      closure.infDist_eq_norm_sub_starProjection]
  have ht := ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => rootDefect g) atTop (𝓝 (rootDefect g))).sub
      (correction_tendsto (rootDefect g))).norm.const_mul
    (Real.sqrt zetaTwo)
  simpa only [he] using ht

/-- The best complete T-dictionary correction has the other exact distance as limit. -/
theorem inverseCorrection_rootDefect_error_tendsto (g : QHilbert) (hg : g ∈ closure) :
    Tendsto (fun N =>
      ‖rootDefect g - inversePhysical (inverseCorrection N (rootDefect g))‖)
      atTop (𝓝 (forwardDistance g)) := by
  have he : ‖rootDefect g - inverseClosure.starProjection (rootDefect g)‖ =
      forwardDistance g := by
    calc
      _ = Metric.infDist (rootDefect g) (inverseClosure : Set QHilbert) :=
        (inverseClosure.infDist_eq_norm_sub_starProjection _).symm
      _ = Metric.infDist (A (rootDefect g))
          (imageSubmodule inverseClosure : Set ThresholdHilbert) :=
        (infDist_A_image inverseClosure (rootDefect g)).symm
      _ = forwardDistance g := by
        rw [inverseClosure_image]
        exact (forwardDistance_eq_rootDefect g hg).symm
  have ht := ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => rootDefect g) atTop (𝓝 (rootDefect g))).sub
      (inverseCorrection_tendsto (rootDefect g))).norm
  simpa only [he] using ht

/-- Optimal finite corrections approach the actual budget, with no zero-limit assertion. -/
theorem optimized_correction_budget_tendsto (g : QHilbert) (hg : g ∈ closure) :
    Tendsto (fun N =>
      ‖toPareto pResidual‖ *
        ‖rootDefect g - inversePhysical (inverseCorrection N (rootDefect g))‖ +
      ‖qResidual‖ * (Real.sqrt zetaTwo *
        ‖rootDefect g - correction N (rootDefect g)‖))
      atTop (𝓝 (crossedBudget g)) := by
  exact ((inverseCorrection_rootDefect_error_tendsto g hg).const_mul
    ‖toPareto pResidual‖).add
    ((correction_rootDefect_error_tendsto g hg).const_mul ‖qResidual‖)

end RiemannResearch.RH.QFullCorrectionCertificates
