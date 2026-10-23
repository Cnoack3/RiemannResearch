/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullHeadControllability
import RiemannResearch.Analysis.FiniteConstraintClosure
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Exact finite-legal repair of every fixed physical head

Source: user-provided RH_Uniform_Dual_Bound_Research_Agenda_Continued,
22 October 2026, equations (34)--(35). The finite right inverse is built
from the existing unconditional `interpolate_head`. The abstract closure
repair theorem is reused. Every bound is for a fixed head; no uniform norm
estimate for the right inverses is assumed or asserted.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFullHeadRepair
open ZetaTwoHilbert
open RiemannResearch.Analysis.FiniteConstraintClosure

private theorem exists_headBasis (M : ℕ) (i : Fin M) :
    ∃ F : QHilbert, F ∈ QFullResidueProjection.legalSpan ∧
      ∀ j : Fin M, F j = if j = i then 1 else 0 := by
  classical
  let u : ℕ → ℝ := fun n => if n = (i : ℕ) + 1 then
    1 / Real.sqrt (qWeight i) else 0
  obtain ⟨F, hF, hh⟩ := QFullHeadControllability.interpolate_head M u
  refine ⟨F, hF, ?_⟩
  intro j
  have he := hh ((j : ℕ) + 1) (Nat.succ_pos _) (by omega)
  have hne : Real.sqrt (qWeight j) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos j))
  by_cases hji : j = i
  · subst j
    simp only [u, if_pos rfl, qSequence_succ] at he
    simpa using (div_left_inj' hne).mp he
  · have hval : (j : ℕ) + 1 ≠ (i : ℕ) + 1 := by
      intro heq
      apply hji
      apply Fin.ext
      omega
    simp only [u, if_neg hval, qSequence_succ] at he
    rw [if_neg hji]
    exact (div_eq_zero_iff).mp he |>.resolve_right hne

def headBasis (M : ℕ) (i : Fin M) : QHilbert :=
  Classical.choose (exists_headBasis M i)

theorem headBasis_mem (M : ℕ) (i : Fin M) :
    headBasis M i ∈ QFullResidueProjection.legalSpan :=
  (Classical.choose_spec (exists_headBasis M i)).1

theorem headBasis_coord (M : ℕ) (i j : Fin M) :
    headBasis M i j = if j = i then 1 else 0 :=
  (Classical.choose_spec (exists_headBasis M i)).2 j

private theorem coordinate_inner (i : ℕ) (f : QHilbert) :
    inner ℝ (lp.single 2 i 1) f = f i := by
  simp only [lp.inner_single_left, RCLike.inner_apply, conj_trivial, mul_one]

/-- Continuous normalized coordinate restriction. -/
def headMap (M : ℕ) : QHilbert →L[ℝ] (Fin M → ℝ) :=
  ContinuousLinearMap.pi fun i => innerSL ℝ (lp.single 2 (i : ℕ) 1)

theorem headMap_apply (M : ℕ) (f : QHilbert) (i : Fin M) :
    headMap M f i = f i := by
  change inner ℝ (lp.single 2 (i : ℕ) 1) f = f i
  exact coordinate_inner i f

/-- A fixed finite head has a continuous linear right inverse taking values
in the algebraic legal span. -/
def headRepair (M : ℕ) : (Fin M → ℝ) →L[ℝ] QHilbert :=
  (Fintype.linearCombination ℝ (headBasis M)).toContinuousLinearMap

theorem headRepair_apply (M : ℕ) (a : Fin M → ℝ) :
    headRepair M a = ∑ i : Fin M, a i • headBasis M i := by
  change Fintype.linearCombination ℝ (headBasis M) a = _
  rw [Fintype.linearCombination_apply]

theorem headRepair_mem (M : ℕ) (a : Fin M → ℝ) :
    headRepair M a ∈ QFullResidueProjection.legalSpan := by
  classical
  rw [headRepair_apply]
  exact QFullResidueProjection.legalSpan.sum_mem fun i _ =>
    QFullResidueProjection.legalSpan.smul_mem _ (headBasis_mem M i)

theorem headRepair_rightInverse (M : ℕ) :
    Function.RightInverse (headRepair M) (headMap M) := by
  classical
  intro a
  ext i
  rw [headMap_apply, ← coordinate_inner (i : ℕ) (headRepair M a),
    headRepair_apply, inner_sum]
  simp only [real_inner_smul_right, coordinate_inner, headBasis_coord]
  simp

/-- Every fixed head of a vector in the actual closure is approximated by
finite legal vectors with that head exactly preserved. -/
theorem exists_exact_head_approximants (M : ℕ) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure) :
    ∃ u : ℕ → QHilbert,
      (∀ j, u j ∈ QFullResidueProjection.legalSpan ∧
        ∀ n, n < M → u j n = f n) ∧ Tendsto u atTop (𝓝 f) := by
  obtain ⟨u, hu, ht⟩ := exists_exact_approximants
    QFullResidueProjection.legalSpan (headMap M) (headRepair M)
    (headRepair_rightInverse M) (headRepair_mem M) (headMap M f) f hf rfl
  refine ⟨u, ?_, ht⟩
  intro j
  refine ⟨(hu j).1, ?_⟩
  intro n hn
  have h := congrFun (hu j).2 (⟨n, hn⟩ : Fin M)
  simpa only [headMap_apply] using h

/-- Exact affine constraints commute with closure for each fixed head. -/
theorem closure_exact_head (M : ℕ) (a : Fin M → ℝ) :
    _root_.closure {f : QHilbert | f ∈ QFullResidueProjection.legalSpan ∧
      headMap M f = a} =
      {f : QHilbert | f ∈ QFullResidueProjection.closure ∧ headMap M f = a} :=
  closure_exact_constraints QFullResidueProjection.legalSpan
    (headMap M) (headRepair M) (headRepair_rightInverse M) (headRepair_mem M) a

/-- Quantitative control of the full norm, including the infinite tail. -/
theorem headRepair_norm_error_le (M : ℕ) (f y : QHilbert) :
    ‖y + headRepair M (headMap M f - headMap M y) - f‖ ≤
      (1 + ‖headRepair M‖ * ‖headMap M‖) * ‖y - f‖ :=
  repair_norm_error_le (headMap M) (headRepair M) (headMap M f) f y rfl

/-- A useful infimum formulation: finite legal vectors preserving the head
have squared norms arbitrarily close from above to any closed feasible vector. -/
theorem exists_exact_head_norm_sq_lt (M : ℕ) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : QHilbert, y ∈ QFullResidueProjection.legalSpan ∧
      (∀ n, n < M → y n = f n) ∧ ‖y‖ ^ 2 < ‖f‖ ^ 2 + ε := by
  obtain ⟨u, hu, ht⟩ := exists_exact_head_approximants M f hf
  have hnorm : Tendsto (fun j => ‖u j‖ ^ 2) atTop (𝓝 (‖f‖ ^ 2)) :=
    ht.norm.pow 2
  obtain ⟨j, hj⟩ := ((tendsto_order.1 hnorm).2 _
    (lt_add_of_pos_right (‖f‖ ^ 2) hε)).exists
  exact ⟨u j, (hu j).1, (hu j).2, hj⟩

end RiemannResearch.RH.QFullHeadRepair
