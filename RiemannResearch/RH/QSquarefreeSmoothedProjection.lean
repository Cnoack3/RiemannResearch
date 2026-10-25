/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QScaledTailPerturbation
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Regularity criteria for the projected smoothed squarefree residual

Source: the user's ProjectionMeasureChangeResearch20261025.md agenda.
Let r be the actual Q residual and b = P_V(B r). The screened vector
B r - b is a squarefree annihilator with mean exactly <r, B r>.
Consequently b is physically bounded iff r = 0; if r is nonzero its
scaled complete tail diverges. Finite moving corrections converge to b.

The RH conclusions are conditional research reductions: their physical
boundedness premises remain open. The existing checked squarefree-capacity
bridge supplies Mathlib's RiemannHypothesis from target membership.
For analytic context only, see Bagchi, Remarks 4 and 8:
https://arxiv.org/abs/math/0607733 . No RH-to-density implication is used.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeSmoothedProjection
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeResidualTail QShiftedReciprocal
open ZetaTwoProbability QAnnihilatorTailEscape QFiniteSupportDualCriterion

def correction : QHilbert := ZetaTwoOptimizerStage.closure.starProjection (B limitingResidual)
def screened : QHilbert := B limitingResidual - correction

theorem screened_mem_orthogonal : screened ∈ ZetaTwoOptimizerStage.closureᗮ :=
  Submodule.sub_starProjection_mem_orthogonal (B limitingResidual)

theorem screened_mean_eq_energy :
    inner ℝ qOne screened = inner ℝ limitingResidual (B limitingResidual) := by
  have hp := Submodule.inner_right_of_mem_orthogonal
    (ZetaTwoOptimizerStage.closure.starProjection_apply_mem qOne) screened_mem_orthogonal
  have hb := Submodule.inner_right_of_mem_orthogonal
    (ZetaTwoOptimizerStage.closure.starProjection_apply_mem (B limitingResidual))
    limitingResidual_mem_squarefree_orthogonal
  have hr : inner ℝ limitingResidual correction = 0 := by
    rw [real_inner_comm]
    exact hb
  have he : inner ℝ limitingResidual screened = inner ℝ qOne screened := by
    change inner ℝ (qOne - ZetaTwoOptimizerStage.closure.starProjection qOne) screened = _
    rw [inner_sub_left, hp, sub_zero]
  rw [← he, screened, inner_sub_right, hr, sub_zero]

theorem correction_bounded_iff_residual_zero :
    (∃ C : ℝ, ∀ k, |qSequence correction k| ≤ C) ↔ limitingResidual = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨D, hD⟩ := B_physical_bounded limitingResidual
    have hb : ∀ k, |qSequence screened k| ≤ D + C := by
      intro k
      have he : qSequence screened k =
          qSequence (B limitingResidual) k - qSequence correction k := by
        change qSequenceLinear (B limitingResidual - correction) k = _
        rw [map_sub]
        rfl
      rw [he]
      calc
        _ ≤ |qSequence (B limitingResidual) k| + |qSequence correction k| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (qSequence (B limitingResidual) k) (-qSequence correction k)
        _ ≤ D + C := add_le_add (hD k) (hC k)
    have hn : 0 ≤ D + C := (abs_nonneg _).trans (hb 0)
    have hm := bounded_annihilator_mean_eq_zero screened screened_mem_orthogonal
      (D+C) hn hb
    apply B_faithful
    rwa [screened_mean_eq_energy] at hm
  · intro hr
    refine ⟨0, ?_⟩
    intro k
    cases k <;> simp [correction, hr, qSequence]

theorem residual_zero_of_correction_bounded
    (C : ℝ) (hC : ∀ k, |qSequence correction k| ≤ C) : limitingResidual = 0 :=
  correction_bounded_iff_residual_zero.mp ⟨C, hC⟩

theorem correction_unbounded_of_residual_ne_zero (hr : limitingResidual ≠ 0)
    (C : ℝ) : ∃ k, C < |qSequence correction k| := by
  by_contra h
  push Not at h
  exact hr (residual_zero_of_correction_bounded C h)

theorem riemannHypothesis_of_correction_bounded
    (C : ℝ) (hC : ∀ k, |qSequence correction k| ≤ C) : RiemannHypothesis := by
  have hr := residual_zero_of_correction_bounded C hC
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

def finiteCorrection (N : ℕ) : QHilbert :=
  (stage N).starProjection (B limitingResidual)

theorem finiteCorrection_tendsto : Tendsto finiteCorrection atTop (𝓝 correction) := by
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkProjection_tendsto
    squarefreeAtom id Function.surjective_id (B limitingResidual)

theorem correction_bounded_of_frequently_finite_bound (C : ℝ)
    (hC : ∀ k, ∃ᶠ N in atTop, |qSequence (finiteCorrection N) k| ≤ C) :
    ∀ k, |qSequence correction k| ≤ C := by
  intro k
  by_contra h
  have ht := (qSequence_tendsto_of_tendsto finiteCorrection_tendsto k).abs
  have hg := ht.eventually (Ioi_mem_nhds (lt_of_not_ge h))
  obtain ⟨N, hN, hgt⟩ := ((hC k).and_eventually hg).exists
  exact (not_lt_of_ge hN) hgt

theorem riemannHypothesis_of_frequently_finite_bound (C : ℝ)
    (hC : ∀ k, ∃ᶠ N in atTop, |qSequence (finiteCorrection N) k| ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_correction_bounded C
    (correction_bounded_of_frequently_finite_bound C hC)


/-- Completely finite input: the residual and projection use the same stage. -/
def movingCorrection (N : ℕ) : QHilbert :=
  (stage N).starProjection (B (residual N))

theorem movingCorrection_error_bound (N : ℕ) :
    ‖movingCorrection N - correction‖ ≤
      ‖residual N - limitingResidual‖ + ‖finiteCorrection N - correction‖ := by
  have hp (x : QHilbert) : ‖(stage N).starProjection x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖(stage N).starProjection‖ * ‖x‖ := (stage N).starProjection.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le (stage N)) (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hd : movingCorrection N - finiteCorrection N =
      (stage N).starProjection (B (residual N - limitingResidual)) := by
    simp only [movingCorrection, finiteCorrection, map_sub]
  calc
    _ ≤ ‖movingCorrection N - finiteCorrection N‖ +
        ‖finiteCorrection N - correction‖ :=
      by simpa only [dist_eq_norm] using
        dist_triangle (movingCorrection N) (finiteCorrection N) correction
    _ ≤ ‖residual N - limitingResidual‖ + ‖finiteCorrection N - correction‖ := by
      rw [hd]
      exact add_le_add
        ((hp (B (residual N - limitingResidual))).trans
          (B_norm_le (residual N - limitingResidual))) le_rfl

theorem movingCorrection_tendsto : Tendsto movingCorrection atTop (𝓝 correction) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr : Tendsto (fun N => ‖residual N - limitingResidual‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp residual_tendsto
  have hf : Tendsto (fun N => ‖finiteCorrection N - correction‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp finiteCorrection_tendsto
  exact squeeze_zero (fun N => norm_nonneg _) movingCorrection_error_bound
    (by simpa using hr.add hf)

/-- A cofinal bound at each physical site, with one common C, is sufficient.
The boundedness hypothesis is an open arithmetic obligation. -/
theorem riemannHypothesis_of_frequently_moving_bound (C : ℝ)
    (hC : ∀ k, ∃ᶠ N in atTop, |qSequence (movingCorrection N) k| ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_correction_bounded C
  intro k
  by_contra h
  have ht := (qSequence_tendsto_of_tendsto movingCorrection_tendsto k).abs
  have hg := ht.eventually (Ioi_mem_nhds (lt_of_not_ge h))
  obtain ⟨N, hN, hgt⟩ := ((hC k).and_eventually hg).exists
  exact (not_lt_of_ge hN) hgt

theorem riemannHypothesis_of_uniform_moving_bound (C : ℝ)
    (hC : ∀ N k, |qSequence (movingCorrection N) k| ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_frequently_moving_bound C
    (fun k => (Eventually.of_forall (fun N => hC N k)).frequently)

/-- Nonzero residual forces divergent normalized tails in its projected
shifted-reciprocal correction, even though the unprojected correction is bounded. -/
theorem correction_scaled_tail_tendsto (hr : limitingResidual ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖tail N correction‖ ^ 2) atTop atTop := by
  apply scaled_tail_transfer_sub (B limitingResidual) correction
    (2 * (Real.sqrt zetaTwo * ‖limitingResidual‖) ^ 2 / zetaTwo)
  · intro N
    exact scaled_tail_energy_le_of_bounded (B limitingResidual) N
      (Real.sqrt zetaTwo * ‖limitingResidual‖) (by positivity)
      (B_physical_bound limitingResidual)
  · exact squarefree_annihilator_scaled_tail_tendsto screened
      screened_mem_orthogonal ((by
        rw [screened_mean_eq_energy]
        exact fun h => hr (B_faithful limitingResidual h)))

/-- A normalized-tail bound along any unbounded subsequence is sufficient. -/
theorem residual_zero_iff_correction_frequently_bounded_scaled_tail :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * ‖tail N correction‖ ^ 2 ≤ C := by
  constructor
  · intro hr
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro N
    simp [correction, hr, tail, finiteHead]
  · rintro ⟨C, hC⟩
    by_contra hr
    have hg := (correction_scaled_tail_tendsto hr).eventually (eventually_gt_atTop C)
    obtain ⟨N, hN, hgt⟩ := (hC.and_eventually hg).exists
    exact (not_lt_of_ge hN) hgt


/-- Only a finite head of each finite-stage correction needs a uniform bound.
No estimate over the full CRT period is assumed. The bound remains open. -/
theorem riemannHypothesis_of_moving_head_bound (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N k : ℕ, 0 < k → k ≤ N →
      |qSequence (movingCorrection N) k| ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_moving_bound C
  intro k
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop k] with N hN
  by_cases hk : k = 0
  · simpa [hk, qSequence] using hC
  · exact hb N k (Nat.pos_of_ne_zero hk) hN

end RiemannResearch.RH.QSquarefreeSmoothedProjection
