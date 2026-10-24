import RiemannResearch.RH.RamanujanMultipleConstraints
import RiemannResearch.RH.RamanujanCoordinateCapacityLimits
import RiemannResearch.Analysis.NestedProjectionGram
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Full limiting source Gram for finitely many Ramanujan coordinates

Source: user-requested fourth Ramanujan dual continuation, 23 October 2026.
All finite and limiting rows are actual orthogonal projections of the
continuous Moebius coordinate Riesz vectors. The limiting source Gram is
positive definite, independently of RH. Every difference of finite or
limiting Grams is the complete Gram of the missing projected vectors.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanMultipleCapacityLimits
open Pareto Pareto.CoefficientStabilization RamanujanCoefficientConstraints
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramMultipleConstraint
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.NestedProjectionGram

variable {κ : Type*} [Fintype κ]

def finiteRows (n : ℕ) (e : κ ↪ ℕ) (j : κ) : ThresholdHilbert :=
  coordinateRepresenter n (e j + 2)

def limitRows (e : κ ↪ ℕ) (j : κ) : ThresholdHilbert :=
  coordinateLimitRepresenter (e j + 2)

def finiteGram (n : ℕ) (e : κ ↪ ℕ) : Matrix κ κ ℝ := gramMatrix (finiteRows n e)
def limitGram (e : κ ↪ ℕ) : Matrix κ κ ℝ := gramMatrix (limitRows e)

def stageEmbedding (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) : κ ↪ Fin n where
  toFun j := ⟨e j, hn j⟩
  inj' := by
    intro i j hij
    exact e.injective (congrArg Fin.val hij)

/-- The projected Riesz family is exactly the arithmetic inverse-Gram source family. -/
theorem finiteRows_eq_stageRows (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) :
    finiteRows n e = RamanujanMultipleConstraints.rows n (stageEmbedding n e hn) := by
  funext j
  symm
  exact minimumVector_eq_coordinateRepresenter n (e j + 2) (by omega)

theorem finiteRows_independent (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) :
    LinearIndependent ℝ (finiteRows n e) := by
  rw [finiteRows_eq_stageRows n e hn]
  exact RamanujanMultipleConstraints.rows_independent n (stageEmbedding n e hn)

theorem limitRows_mem (e : κ ↪ ℕ) (j : κ) : limitRows e j ∈ closedSpace :=
  closedSpace.starProjection_apply_mem (coordinateRiesz (e j + 2))

theorem residueAtom_mem_closedSpace (i : ℕ) : residueAtom i ∈ closedSpace :=
  (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (Submodule.subset_span (Set.mem_range_self i))

theorem limitRows_biorthogonal [DecidableEq κ] (e : κ ↪ ℕ) (i j : κ) :
    inner ℝ (limitRows e i) (residueAtom (e j)) = if i = j then 1 else 0 := by
  rw [limitRows, coordinateLimitRepresenter_inner _ _ (residueAtom_mem_closedSpace (e j)),
    coefficientCLM_biorthogonal]
  simp only [e.injective.eq_iff]

/-- Distinct legal coordinates remain independent after projection to the full closed span. -/
theorem limitRows_independent (e : κ ↪ ℕ) : LinearIndependent ℝ (limitRows e) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  change Fintype.linearCombination ℝ (limitRows e) a = 0 at ha
  have hz : inner ℝ (Fintype.linearCombination ℝ (limitRows e) a)
      (residueAtom (e j)) = 0 := by rw [ha, inner_zero_left]
  rw [inner_synthesis_left] at hz
  simp_rw [limitRows_biorthogonal] at hz
  simpa using hz

theorem limitGram_posDef (e : κ ↪ ℕ) : (limitGram e).PosDef :=
  gramMatrix_posDef (limitRows_independent e)

theorem limitGram_det_pos [DecidableEq κ] (e : κ ↪ ℕ) :
    0 < (limitGram e).det := gramMatrix_det_pos (limitRows_independent e)

theorem limitGram_entry (e : κ ↪ ℕ) (i j : κ) :
    limitGram e i j = coefficientCLM (e i + 2) (limitRows e j) :=
  coordinateLimitRepresenter_inner (e i + 2) _ (limitRows_mem e j)

theorem finiteSpace_le_closedSpace (n : ℕ) : finiteSpace n ≤ closedSpace :=
  (walkSpan_le residueAtom id n).trans
    (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure

/-- Every signed entry of the finite-to-limit Gram defect is explicit. -/
theorem gram_limit_exact (n : ℕ) (e : κ ↪ ℕ) (i j : κ) :
    limitGram e i j = finiteGram n e i j +
      inner ℝ (limitRows e i - finiteRows n e i) (limitRows e j - finiteRows n e j) :=
  gram_increment_exact (finiteSpace n) closedSpace (finiteSpace_le_closedSpace n)
    (coordinateRiesz (e i + 2)) (coordinateRiesz (e j + 2))

/-- The entire matrix defect is an actual Gram matrix, not a diagonal estimate. -/
theorem gram_limit_difference (n : ℕ) (e : κ ↪ ℕ) :
    limitGram e - finiteGram n e = gramMatrix (fun j => limitRows e j - finiteRows n e j) := by
  ext i j
  change limitGram e i j - finiteGram n e i j =
    inner ℝ (limitRows e i - finiteRows n e i) (limitRows e j - finiteRows n e j)
  have h := gram_limit_exact n e i j
  linarith

theorem gram_stage_exact (n k : ℕ) (hnk : n ≤ k) (e : κ ↪ ℕ) (i j : κ) :
    finiteGram k e i j = finiteGram n e i j +
      inner ℝ (finiteRows k e i - finiteRows n e i)
        (finiteRows k e j - finiteRows n e j) :=
  gram_increment_exact (finiteSpace n) (finiteSpace k) (walkSpan_mono residueAtom id hnk)
    (coordinateRiesz (e i + 2)) (coordinateRiesz (e j + 2))

theorem quadratic_limit_exact (n : ℕ) (e : κ ↪ ℕ) (c : κ → ℝ) :
    ‖Fintype.linearCombination ℝ (limitRows e) c‖ ^ 2 =
      ‖Fintype.linearCombination ℝ (finiteRows n e) c‖ ^ 2 +
        ‖Fintype.linearCombination ℝ (fun j => limitRows e j - finiteRows n e j) c‖ ^ 2 :=
  synthesis_increment_exact (finiteSpace n) closedSpace (finiteSpace_le_closedSpace n)
    (fun j => coordinateRiesz (e j + 2)) c

theorem quadratic_monotone (e : κ ↪ ℕ) (c : κ → ℝ) :
    Monotone (fun n => ‖Fintype.linearCombination ℝ (finiteRows n e) c‖ ^ 2) := by
  intro n k hnk
  have h := synthesis_increment_exact (finiteSpace n) (finiteSpace k)
    (walkSpan_mono residueAtom id hnk) (fun j => coordinateRiesz (e j + 2)) c
  change ‖Fintype.linearCombination ℝ (finiteRows k e) c‖ ^ 2 =
    ‖Fintype.linearCombination ℝ (finiteRows n e) c‖ ^ 2 + _ at h
  dsimp only
  rw [h]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem finiteRows_tendsto (e : κ ↪ ℕ) (j : κ) :
    Tendsto (fun n => finiteRows n e j) atTop (𝓝 (limitRows e j)) :=
  coordinateRepresenter_tendsto (e j + 2)

/-- The full matrix, including every mixed coordinate, converges to a positive definite limit. -/
theorem finiteGram_tendsto (e : κ ↪ ℕ) :
    Tendsto (fun n => finiteGram n e) atTop (𝓝 (limitGram e)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact (finiteRows_tendsto e i).inner (finiteRows_tendsto e j)

end RiemannResearch.RH.RamanujanMultipleCapacityLimits
