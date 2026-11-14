import RiemannResearch.Analysis.ResidualCorrectionCost
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith

/-!
# Exact cost of correcting the actual full-conductor Q residual

Source: user-provided Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md,
formula (F), specialized using the existing full-conductor inverse-Gram
projections. The minimum cost is the reciprocal of the exact energy decrease.

The uniform-budget RH theorem is a conditional research reduction. Its open
input concerns corrections to the actual residual, in the full legal span,
with one constant independent of stage. Finite CRT does not prove that input.
A logarithmic stage-dependent budget alone is not identified with this
uniform criterion.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullResidualCorrectionCost
open ZetaTwoHilbert QFullResidueProjection
open RiemannResearch.Analysis.ResidualCorrectionCost
open RiemannResearch.Analysis.ExhaustiveWalk

def residual (N : ℕ) : QHilbert := qOne - candidate N

theorem stage_mono : Monotone stage :=
  walkSpan_mono (fun i => qResidue (i + 2)) id

/-- The projection of the old residual is the actual inverse-Gram increment. -/
theorem projected_residual (N M : ℕ) (hNM : N ≤ M) :
    (stage M).starProjection (residual N) = candidate M - candidate N := by
  have hmem : candidate N ∈ stage M := stage_mono hNM (candidate_mem_stage N)
  have hp : (stage M).starProjection (candidate N) = candidate N :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  rw [residual, map_sub, hp, ← candidate_eq_projection M]

/-- Exact energy decrease, retaining the complete norm-square increment. -/
theorem residual_energy_completion (N M : ℕ) (hNM : N ≤ M) :
    ‖residual N‖ ^ 2 = ‖residual M‖ ^ 2 + ‖candidate M - candidate N‖ ^ 2 := by
  simpa only [residual, ← candidate_eq_projection] using
    nested_projection_energy (stage N) (stage M) (stage_mono hNM) qOne

/-- The least unscaled correction cost is attained and equals the inverse
of the actual residual-energy decrease. -/
theorem correction_cost_isLeast (N M : ℕ) (hNM : N ≤ M)
    (hgain : candidate M - candidate N ≠ 0) :
    IsLeast {E : ℝ | ∃ w ∈ stage M, inner ℝ (residual N) w ≠ 0 ∧
      ‖w‖ ^ 2 / (inner ℝ (residual N) w) ^ 2 = E}
      (1 / (‖residual N‖ ^ 2 - ‖residual M‖ ^ 2)) := by
  have hp : (stage M).starProjection (residual N) ≠ 0 := by
    rwa [projected_residual N M hNM]
  have h := cost_isLeast (stage M) (residual N) hp
  rw [projected_residual N M hNM] at h
  have he : ‖candidate M - candidate N‖ ^ 2 =
      ‖residual N‖ ^ 2 - ‖residual M‖ ^ 2 := by
    linarith only [residual_energy_completion N M hNM]
  simpa only [he] using h

/-- A normalized correction budget is precisely a quantitative residual decrease. -/
theorem correction_budget_iff_gain (N M : ℕ) (hNM : N ≤ M)
    (hr : residual N ≠ 0) (K : ℝ) (hK : 0 < K) :
    (∃ w ∈ stage M, inner ℝ (residual N) w ≠ 0 ∧
      ‖residual N‖ ^ 2 * (‖w‖ ^ 2 / (inner ℝ (residual N) w) ^ 2) ≤ K) ↔
      ‖residual N‖ ^ 2 / K ≤ ‖residual N‖ ^ 2 - ‖residual M‖ ^ 2 := by
  have he : ‖candidate M - candidate N‖ ^ 2 =
      ‖residual N‖ ^ 2 - ‖residual M‖ ^ 2 := by
    linarith only [residual_energy_completion N M hNM]
  simpa only [projected_residual N M hNM, he] using
    normalized_budget_iff (stage M) (residual N) hr K hK

/-- The note's logarithmic budget, expressed in the actual finite-stage Q energy. -/
theorem logarithmic_correction_budget_iff_gain (N M : ℕ) (hNM : N ≤ M)
    (hr : residual N ≠ 0) (C L : ℝ) (hC : 0 < C) (hL : 1 < L) :
    (∃ w ∈ stage M, inner ℝ (residual N) w ≠ 0 ∧
      ‖residual N‖ ^ 2 * (‖w‖ ^ 2 / (inner ℝ (residual N) w) ^ 2) ≤
        C * Real.log L) ↔
      ‖residual N‖ ^ 2 / (C * Real.log L) ≤
        ‖residual N‖ ^ 2 - ‖residual M‖ ^ 2 :=
  correction_budget_iff_gain N M hNM hr _ (mul_pos hC (Real.log_pos hL))

/-- Conditional research reduction: a stage-independent budget for finite
legal corrections to the actual residual is sufficient for RH. -/
theorem riemannHypothesis_of_uniform_legal_correction_budget
    (K : ℝ) (hK : 0 < K)
    (hbudget : ∀ᶠ N in atTop, residual N ≠ 0 →
      ∃ w ∈ legalSpan, inner ℝ (residual N) w ≠ 0 ∧
        ‖residual N‖ ^ 2 * (‖w‖ ^ 2 / (inner ℝ (residual N) w) ^ 2) ≤ K) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_qOne_mem_full_closure
  apply mem_of_eventual_uniform_budget closure atTop qOne candidate
    (Filter.Eventually.of_forall (fun N =>
      legalSpan.le_topologicalClosure (candidate_mem_legalSpan N)))
    candidate_tendsto_projection K hK
  refine hbudget.mono ?_
  intro N hN hr
  obtain ⟨w, hw, hs, he⟩ := hN hr
  exact ⟨w, legalSpan.le_topologicalClosure hw, hs, he⟩

end RiemannResearch.RH.QFullResidualCorrectionCost
