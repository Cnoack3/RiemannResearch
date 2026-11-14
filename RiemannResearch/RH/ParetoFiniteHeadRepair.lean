import RiemannResearch.Analysis.FiniteConstraintClosure
import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.ParetoLegalApproximationClosure
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Exact finite-head repair in the Pareto space

Source: user-provided endpoint proof, Theorem 12.2. Finite interpolation
constructs a continuous right inverse into the actual algebraic legal
subspace. Its norm may depend on the fixed head length.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.FiniteHeadRepair

private theorem exists_basis (Y : ℕ) (i : Fin Y) :
    ∃ f ∈ hilbertLegalSubspace (Set.Ici 1),
      ∀ j : Fin Y, hilbertSequence f (j + 1) = if j = i then 1 else 0 := by
  classical
  obtain ⟨g, hg, hh⟩ := exists_full_legal_head
    (fun n => if n = (i : ℕ) + 1 then 1 else 0) Y
  obtain ⟨f, hf, hfg⟩ := legalSeedSpan_exists_hilbert
    (Set.Ici 1) (by intro a ha; exact ha) hg
  refine ⟨f, hf, ?_⟩
  intro j
  rw [hfg, hh (j + 1) (by omega) (by omega)]
  simp only [Nat.add_right_cancel_iff, Fin.val_inj]

private def headBasis (Y : ℕ) (i : Fin Y) : ThresholdHilbert :=
  Classical.choose (exists_basis Y i)

private theorem headBasis_mem (Y : ℕ) (i : Fin Y) :
    headBasis Y i ∈ hilbertLegalSubspace (Set.Ici 1) :=
  (Classical.choose_spec (exists_basis Y i)).1

private theorem headBasis_coord (Y : ℕ) (i j : Fin Y) :
    hilbertSequence (headBasis Y i) (j + 1) = if j = i then 1 else 0 :=
  (Classical.choose_spec (exists_basis Y i)).2 j

/-- Restriction to the first Y physical coordinates. -/
def headMap (Y : ℕ) : ThresholdHilbert →L[ℝ] (Fin Y → ℝ) :=
  ContinuousLinearMap.pi fun i => physicalEvaluationCLM (i : ℕ)

theorem headMap_apply (Y : ℕ) (f : ThresholdHilbert) (i : Fin Y) :
    headMap Y f i = hilbertSequence f (i + 1) :=
  physicalEvaluationCLM_apply i f

/-- Finite-dimensional interpolation as a continuous linear map. -/
def headRepair (Y : ℕ) : (Fin Y → ℝ) →L[ℝ] ThresholdHilbert :=
  (Fintype.linearCombination ℝ (headBasis Y)).toContinuousLinearMap

private theorem headRepair_apply (Y : ℕ) (a : Fin Y → ℝ) :
    headRepair Y a = ∑ i : Fin Y, a i • headBasis Y i := by
  change Fintype.linearCombination ℝ (headBasis Y) a = _
  rw [Fintype.linearCombination_apply]

theorem headRepair_mem (Y : ℕ) (a : Fin Y → ℝ) :
    headRepair Y a ∈ hilbertLegalSubspace (Set.Ici 1) := by
  classical
  rw [headRepair_apply]
  exact (hilbertLegalSubspace (Set.Ici 1)).sum_mem fun i _ =>
    (hilbertLegalSubspace (Set.Ici 1)).smul_mem _ (headBasis_mem Y i)

theorem headRepair_rightInverse (Y : ℕ) :
    Function.RightInverse (headRepair Y) (headMap Y) := by
  classical
  intro a
  ext j
  rw [headRepair_apply, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul,
    headMap_apply, headBasis_coord]
  simp

/-- Each fixed physical head can be preserved by norm-convergent finite legal approximants. -/
theorem exists_exact_head_approximants (Y : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalClosure (Set.Ici 1)) :
    ∃ u : ℕ → ThresholdHilbert,
      (∀ j, u j ∈ hilbertLegalSubspace (Set.Ici 1) ∧
        ∀ n, 0 < n → n ≤ Y → hilbertSequence (u j) n = hilbertSequence f n) ∧
      Tendsto u atTop (𝓝 f) := by
  obtain ⟨u, hu, ht⟩ :=
    RiemannResearch.Analysis.FiniteConstraintClosure.exists_exact_approximants
      (hilbertLegalSubspace (Set.Ici 1)) (headMap Y) (headRepair Y)
      (headRepair_rightInverse Y) (headRepair_mem Y) (headMap Y f) f hf rfl
  refine ⟨u, ?_, ht⟩
  intro j
  refine ⟨(hu j).1, ?_⟩
  intro n hn hnY
  have h := congrFun (hu j).2 (⟨n - 1, by omega⟩ : Fin Y)
  simpa only [headMap_apply, Nat.sub_add_cancel hn] using h

end RiemannResearch.RH.Pareto.FiniteHeadRepair
