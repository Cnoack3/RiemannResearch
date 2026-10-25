/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.HilbertWeakCompactness
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Weak compactness and canonical squarefree approximants

Source: user-provided compactness and canonical projection argument,
25 October 2026. The finite approximants are the existing `optimizer M`.
Their strong limit is already proved by `ZetaTwoOptimizerStage.optimizer_tendsto`.
Here their bounds, exact energy identities, and actual weak convergence are
assembled with weak compactness of Hilbert balls. Identifying the limit with
`qOne` remains precisely the unresolved squarefree target-membership question.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeWeakCompactness
open ZetaTwoHilbert ZetaTwoOptimizerStage
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.HilbertWeakCompactness

instance closure_completeSpace : CompleteSpace closure :=
  (show IsClosed (closure : Set QHilbert) from
    (Submodule.span ℝ (Set.range squarefreeAtom)).isClosed_topologicalClosure).completeSpace_coe

instance closure_separableSpace : TopologicalSpace.SeparableSpace closure := by
  apply TopologicalSpace.IsSeparable.separableSpace
  change TopologicalSpace.IsSeparable
    ((Submodule.span ℝ (Set.range squarefreeAtom)).topologicalClosure : Set QHilbert)
  rw [Submodule.topologicalClosure_coe]
  exact ((Set.countable_range squarefreeAtom).isSeparable.span (R := ℝ)).closure

/-- The radius-r ball in the closed squarefree space, as an ambient set. -/
def normBall (r : ℝ) : Set QHilbert := {f | f ∈ closure ∧ ‖f‖ ≤ r}

/-- The same ball with the actual ambient weak topology. -/
def weakBall (r : ℝ) : Set (WeakSpace ℝ QHilbert) :=
  toWeakSpace ℝ QHilbert '' normBall r

theorem weakBall_eq_subtype_image (r : ℝ) :
    weakBall r = (WeakSpace.map closure.subtypeL) ''
      (toWeakSpace ℝ closure '' Metric.closedBall (0 : closure) r) := by
  ext x
  constructor
  · rintro ⟨f, ⟨hf, hn⟩, rfl⟩
    refine ⟨toWeakSpace ℝ closure ⟨f, hf⟩, ?_, rfl⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hn
  · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨(f : QHilbert), ⟨f.property, ?_⟩, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hf

theorem weakBall_isCompact (r : ℝ) : IsCompact (weakBall r) := by
  rw [weakBall_eq_subtype_image]
  exact (isCompact_closedBall_weak (H := closure) r).image
    (WeakSpace.map closure.subtypeL).continuous

theorem weakBall_isSeqCompact (r : ℝ) : IsSeqCompact (weakBall r) := by
  rw [weakBall_eq_subtype_image]
  exact IsSeqCompact.image (WeakSpace.map closure.subtypeL).continuous.seqContinuous
    (isSeqCompact_closedBall_weak (H := closure) r)

theorem normBall_of_neg {r : ℝ} (hr : r < 0) : normBall r = ∅ := by
  ext f
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hf
  exact (not_le_of_gt hr) ((norm_nonneg f).trans hf.2)

theorem normBall_zero : normBall 0 = {0} := by
  ext f
  change (f ∈ closure ∧ ‖f‖ ≤ 0) ↔ f = 0
  constructor
  · intro hf
    exact norm_eq_zero.mp (le_antisymm hf.2 (norm_nonneg f))
  · rintro rfl
    exact ⟨closure.zero_mem, by simp⟩

theorem bounded_legal_sequence_has_weak_subsequence (r : ℝ) (F : ℕ → QHilbert)
    (hF : ∀ n, F n ∈ normBall r) :
    ∃ f ∈ normBall r, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ QHilbert (F (φ n))) atTop
        (𝓝 (toWeakSpace ℝ QHilbert f)) := by
  have hmem (n : ℕ) : toWeakSpace ℝ QHilbert (F n) ∈ weakBall r :=
    ⟨F n, hF n, rfl⟩
  obtain ⟨x, hx, φ, hφ, ht⟩ := weakBall_isSeqCompact r hmem
  obtain ⟨f, hf, rfl⟩ := hx
  exact ⟨f, hf, φ, hφ, by simpa only [Function.comp_def] using ht⟩

theorem optimizer_mem_closure (M : ℕ) : optimizer M ∈ closure := by
  exact ((walkSpan_le squarefreeAtom id M).trans
    (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure)
    ((stage M).starProjection_apply_mem qOne)

theorem optimizer_norm_le_one (M : ℕ) : ‖optimizer M‖ ≤ 1 := by
  simpa only [optimizer, qOne_norm] using
    Submodule.norm_starProjection_apply_le (stage M) qOne

theorem optimizer_residual_pythagoras (M : ℕ) :
    ‖optimizer M‖^2 + ‖residual M‖^2 = 1 := by
  have ho : inner ℝ (optimizer M) (residual M) = 0 :=
    ((stage M).mem_orthogonal _).mp (residual_mem_orthogonal M) _
      ((stage M).starProjection_apply_mem qOne)
  have he : optimizer M + residual M = qOne := by
    unfold ZetaTwoOptimizerStage.residual
    abel
  have hn := norm_add_sq_real (optimizer M) (residual M)
  rw [he, qOne_norm_sq, ho] at hn
  linarith

/-- Exact least-squares identity, retaining the competitor displacement square. -/
theorem optimizer_error_decomposition (M : ℕ) (f : QHilbert) (hf : f ∈ stage M) :
    ‖qOne - f‖^2 = ‖residual M‖^2 + ‖optimizer M - f‖^2 := by
  have ho : inner ℝ (residual M) (optimizer M - f) = 0 := by
    rw [real_inner_comm]
    exact ((stage M).mem_orthogonal _).mp (residual_mem_orthogonal M) _
      ((stage M).sub_mem ((stage M).starProjection_apply_mem qOne) hf)
  have he : qOne - f = residual M + (optimizer M - f) := by
    unfold ZetaTwoOptimizerStage.residual
    abel
  rw [he, norm_add_sq_real, ho]
  ring

theorem optimizer_mem_unitBall (M : ℕ) : optimizer M ∈ normBall 1 :=
  ⟨optimizer_mem_closure M, optimizer_norm_le_one M⟩

theorem optimizer_weak_tendsto :
    Tendsto (fun M => toWeakSpace ℝ QHilbert (optimizer M)) atTop
      (𝓝 (toWeakSpace ℝ QHilbert (closure.starProjection qOne))) := by
  exact ((toWeakSpaceCLM ℝ QHilbert).continuous.tendsto _).comp optimizer_tendsto

theorem limiting_optimizer_mem_unitBall : closure.starProjection qOne ∈ normBall 1 :=
  ⟨closure.starProjection_apply_mem qOne, by
    simpa only [qOne_norm] using Submodule.norm_starProjection_apply_le closure qOne⟩

theorem optimizer_weak_limit_unique (f : QHilbert)
    (hf : Tendsto (fun M => toWeakSpace ℝ QHilbert (optimizer M)) atTop
      (𝓝 (toWeakSpace ℝ QHilbert f))) : f = closure.starProjection qOne := by
  exact (toWeakSpace ℝ QHilbert).injective
    (tendsto_nhds_unique hf optimizer_weak_tendsto)

/-- Weak compactness leaves precisely the target-membership obligation. -/
theorem optimizer_weak_tendsto_one_iff :
    Tendsto (fun M => toWeakSpace ℝ QHilbert (optimizer M)) atTop
      (𝓝 (toWeakSpace ℝ QHilbert qOne)) ↔ qOne ∈ closure := by
  constructor
  · intro h
    exact Submodule.starProjection_eq_self_iff.mp
      (optimizer_weak_limit_unique qOne h).symm
  · intro h
    have hp : closure.starProjection qOne = qOne :=
      Submodule.starProjection_eq_self_iff.mpr h
    simpa only [hp] using optimizer_weak_tendsto

end RiemannResearch.RH.QSquarefreeWeakCompactness
