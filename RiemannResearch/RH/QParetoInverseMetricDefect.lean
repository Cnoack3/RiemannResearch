import RiemannResearch.RH.QParetoGramComparison
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact defects between complete P and Q inverse metrics

Source: user-requested continuation of Ramanujan duality, 23 October 2026.
The same prescribed source is used under both metrics. The upper comparison
has an exact sum of the optimizer displacement and the reciprocal metric
correction; consequently it is strict for every nonzero source. The second
identity retains the complete defect in the lower comparison as well.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QParetoGramComparison
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QParetoMetric
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity

variable {ι : Type*} [Fintype ι]

/-- Exact defect in the upper inverse-metric comparison, including displacement. -/
theorem capacity_upper_gap_exact {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    zetaTwo * (zetaTwo * capacity (paretoFamily_independent hv) b - capacity hv b) =
      ‖toPareto (minimumVector hv b) -
        zetaTwo • minimumVector (paretoFamily_independent hv) b‖ ^ 2 +
      metricCorrection (minimumVector hv b) := by
  have hp : inner ℝ (toPareto (minimumVector hv b))
      (minimumVector (paretoFamily_independent hv) b) = capacity hv b := by
    change inner ℝ (toPareto (Fintype.linearCombination ℝ v (inverseSource hv b)))
      (minimumVector (paretoFamily_independent hv) b) = _
    rw [toPareto_synthesis, inner_synthesis_minimumVector]
    rfl
  have hn := norm_identity (minimumVector hv b)
  rw [← capacity_eq_norm_sq] at hn
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, hp, ← capacity_eq_norm_sq]
  nlinarith only [hn]

/-- The original weak upper bound is strict exactly off the zero source. -/
theorem capacity_upper_strict_iff {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    capacity hv b < zetaTwo * capacity (paretoFamily_independent hv) b ↔ b ≠ 0 := by
  constructor
  · intro h hb
    simp [hb, capacity] at h
  · intro hb
    have hnonzero : minimumVector hv b ≠ 0 := by
      intro hz
      have h := capacity_pos hv b hb
      rw [capacity_eq_norm_sq, hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
      exact (lt_irrefl 0) h
    have hk : 0 < metricCorrection (minimumVector hv b) := by
      apply lt_of_le_of_ne (metricCorrection_nonneg _)
      intro he
      exact hnonzero ((metricCorrection_eq_zero_iff _).mp he.symm)
    have hg := capacity_upper_gap_exact hv b
    have hsq := sq_nonneg ‖toPareto (minimumVector hv b) -
      zetaTwo • minimumVector (paretoFamily_independent hv) b‖
    by_contra hnot
    have hgap : zetaTwo * capacity (paretoFamily_independent hv) b -
        capacity hv b ≤ 0 := by linarith
    have hprod := mul_nonpos_of_nonneg_of_nonpos zetaTwo_pos.le hgap
    linarith

/-- Exact lower-comparison defect. Both correction terms are retained. -/
theorem capacity_lower_gap_exact {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    capacity hv b - (zetaTwo / 2) * capacity (paretoFamily_independent hv) b =
      ‖minimumVector hv b - (zetaTwo / 2) •
        toQ (minimumVector (paretoFamily_independent hv) b)‖ ^ 2 +
      (zetaTwo / 4) * (capacity (paretoFamily_independent hv) b -
        metricCorrection (toQ (minimumVector (paretoFamily_independent hv) b))) := by
  let cp := inverseSource (paretoFamily_independent hv) b
  have hmap : toQ (minimumVector (paretoFamily_independent hv) b) =
      Fintype.linearCombination ℝ v cp := by
    apply paretoEquiv.injective
    change toPareto (toQ _) = toPareto _
    rw [toPareto_toQ, toPareto_synthesis]
    rfl
  have hp : inner ℝ (minimumVector hv b)
      (toQ (minimumVector (paretoFamily_independent hv) b)) =
        capacity (paretoFamily_independent hv) b := by
    rw [hmap, real_inner_comm, inner_synthesis_minimumVector]
    rfl
  have hn := norm_identity (toQ (minimumVector (paretoFamily_independent hv) b))
  rw [toPareto_toQ, ← capacity_eq_norm_sq] at hn
  have hscaled := congrArg (fun t : ℝ => (zetaTwo / 4) * t) hn
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, hp, ← capacity_eq_norm_sq]
  nlinarith only [hscaled]

/-- All signed mixed source pairings have the actual Gram inverse representation. -/
theorem capacity_eq_matrix [DecidableEq ι] {v : ι → QHilbert}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    capacity hv b = dotProduct b ((gramMatrix v)⁻¹.mulVec b) := by
  rw [gramMatrix_inverseSource hv]
  unfold capacity dotProduct
  apply Finset.sum_congr rfl
  intro i _
  ring

end RiemannResearch.RH.QParetoGramComparison
