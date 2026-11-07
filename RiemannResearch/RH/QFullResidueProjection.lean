import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Metrizable.Basic
import Lean.Elab.Tactic.Omega

/-!
# Full Q residue inverse-Gram candidates are the actual projections

Source: the user's Q inverse-Gram candidate construction, 13 October 2026.
The finite inverse and projection machinery is reused without changing the
actual Q inner product. All conductors 2 through n+1 occur at stage n.
Unconditionally the candidates converge to the projection onto the closed
legal span. Convergence to one requires the explicitly stated membership.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QFullResidueProjection

open ZetaTwoHilbert QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.LinearAlgebra.CenteredNormalEquations

def conductor (n : ℕ) (i : Fin n) : ℕ := i.val + 2

theorem conductor_gt_one (n : ℕ) (i : Fin n) : 1 < conductor n i := by
  simp only [conductor]
  omega

theorem conductor_injective (n : ℕ) : Function.Injective (conductor n) := by
  intro i j h
  apply Fin.ext
  simp only [conductor] at h
  omega

/-- Literal genuine matrix-inverse coefficients for all conductors in the stage. -/
def coefficients (n : ℕ) : Fin n → ℝ :=
  (residueGramMatrix (conductor n))⁻¹.mulVec (qMean (conductor n))

/-- An actual finite legal synthesis; the underlying Q law is not truncated. -/
def candidate (n : ℕ) : QHilbert := qSynthesis (conductor n) (coefficients n)

def stage (n : ℕ) : Submodule ℝ QHilbert :=
  walkSpan (fun i => qResidue (i + 2)) id n

instance stage_finiteDimensional (n : ℕ) : FiniteDimensional ℝ (stage n) := by
  unfold stage
  infer_instance

def legalSpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun i : ℕ => qResidue (i + 2)))

def closure : Submodule ℝ QHilbert := legalSpan.topologicalClosure

instance closure_hasOrthogonalProjection : closure.HasOrthogonalProjection := by
  unfold closure
  infer_instance

/-- The full legal closure is complete and countably generated in closure. -/
instance closure_completeSpace : CompleteSpace closure :=
  (show IsClosed (closure : Set QHilbert) from
    legalSpan.isClosed_topologicalClosure).completeSpace_coe

instance closure_separableSpace : TopologicalSpace.SeparableSpace closure := by
  apply TopologicalSpace.IsSeparable.separableSpace
  change TopologicalSpace.IsSeparable
    ((Submodule.span ℝ (Set.range (fun i : ℕ => qResidue (i + 2)))).topologicalClosure :
      Set QHilbert)
  rw [Submodule.topologicalClosure_coe]
  exact ((Set.countable_range (fun i : ℕ => qResidue (i + 2))).isSeparable.span
    (R := ℝ)).closure

theorem coefficients_normal (n : ℕ) (i : Fin n) :
    action (qGram (conductor n)) (coefficients n) i = qMean (conductor n) i := by
  have hdet : IsUnit (residueGramMatrix (conductor n)).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt
      (qGram_posDef (conductor n) (conductor_gt_one n) (conductor_injective n)).det_pos)
  have hh : (residueGramMatrix (conductor n)).mulVec (coefficients n) =
      qMean (conductor n) := by
    unfold coefficients
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact congrFun hh i

theorem coefficients_eq_inverseCoeff (n : ℕ) :
    coefficients n = inverseCoeff
      (qResidue_linearIndependent (conductor n)
        (conductor_gt_one n) (conductor_injective n)) qOne := by
  have hm : qMean (conductor n) =
      cross (fun i => qResidue (conductor n i)) qOne := by
    funext i
    exact (real_inner_comm qOne (qResidue (conductor n i))).symm
  change (gramMatrix (fun i => qResidue (conductor n i)))⁻¹.mulVec
    (qMean (conductor n)) = _
  rw [hm, gramMatrix_inverseSource
    (qResidue_linearIndependent (conductor n)
      (conductor_gt_one n) (conductor_injective n))]
  rfl

/-- The literal inverse-matrix candidate is the unique actual stage projection. -/
theorem candidate_eq_projection (n : ℕ) :
    candidate n = (stage n).starProjection qOne := by
  rw [candidate, coefficients_eq_inverseCoeff]
  simpa only [qSynthesis, Fintype.linearCombination_apply,
    synthesisSpan, stage, walkSpan, conductor, id_eq] using
    synthesis_inverseCoeff_eq_projection
      (qResidue_linearIndependent (conductor n)
        (conductor_gt_one n) (conductor_injective n)) qOne

theorem candidate_mem_stage (n : ℕ) : candidate n ∈ stage n := by
  rw [candidate_eq_projection]
  exact (stage n).starProjection_apply_mem qOne

theorem candidate_mem_legalSpan (n : ℕ) : candidate n ∈ legalSpan :=
  walkSpan_le (fun i => qResidue (i + 2)) id n (candidate_mem_stage n)

/-- The unconditional limit is the projection onto the complete legal closure. -/
theorem candidate_tendsto_projection :
    Tendsto candidate atTop (𝓝 (closure.starProjection qOne)) := by
  have h : Tendsto (fun n => (stage n).starProjection qOne) atTop
      (𝓝 (closure.starProjection qOne)) :=
    walkProjection_tendsto (fun i => qResidue (i + 2))
      id Function.surjective_id qOne
  simpa only [← candidate_eq_projection] using h

/-- Conditional convergence to the intended target, with the missing
arithmetic closure assertion exposed as a hypothesis. -/
theorem candidate_tendsto_qOne (h : qOne ∈ closure) :
    Tendsto candidate atTop (𝓝 qOne) := by
  have hp : closure.starProjection qOne = qOne :=
    Submodule.starProjection_eq_self_iff.mpr h
  simpa only [hp] using candidate_tendsto_projection

end RiemannResearch.RH.QFullResidueProjection
