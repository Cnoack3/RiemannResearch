/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Topology.Sequences

/-!
# Weak compactness of Hilbert balls

Source: the user's weak compactness discussion, 25 October 2026.
The proof strategy uses Mathlib's `WeakDual.isCompact_closedBall` and
`WeakDual.isSeqCompact_closedBall` with `InnerProductSpace.toDual`.
The proof transports Mathlib's Banach--Alaoglu theorem through the
Frechet--Riesz representation. Compactness holds for every real radius,
including the empty balls at negative radii. Sequential extraction additionally
uses separability; no first-countability assumption on the entire weak space
is made.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.HilbertWeakCompactness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Riesz inversion, with weak-star topology on the dual and weak topology on H. -/
def dualToWeak (f : WeakDual ℝ H) : WeakSpace ℝ H :=
  toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm f.toStrongDual)

theorem continuous_dualToWeak : Continuous (dualToWeak (H := H)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro ℓ
  change Continuous (fun f : WeakDual ℝ H =>
    ℓ ((InnerProductSpace.toDual ℝ H).symm f.toStrongDual))
  have heq (f : StrongDual ℝ H) :
      ℓ ((InnerProductSpace.toDual ℝ H).symm f) =
        f ((InnerProductSpace.toDual ℝ H).symm ℓ) := by
    calc
      _ = inner ℝ ((InnerProductSpace.toDual ℝ H).symm ℓ)
          ((InnerProductSpace.toDual ℝ H).symm f) :=
        InnerProductSpace.toDual_symm_apply.symm
      _ = inner ℝ ((InnerProductSpace.toDual ℝ H).symm f)
          ((InnerProductSpace.toDual ℝ H).symm ℓ) := real_inner_comm _ _
      _ = _ := InnerProductSpace.toDual_symm_apply
  simp_rw [heq]
  exact WeakDual.eval_continuous _

/-- Exact identification of the weak-star dual ball with the weak Hilbert ball. -/
theorem dualToWeak_ball_image (r : ℝ) :
    dualToWeak (H := H) ''
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) r) =
      toWeakSpace ℝ H '' Metric.closedBall (0 : H) r := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(InnerProductSpace.toDual ℝ H).symm f.toStrongDual, ?_, rfl⟩
    have hf' : ‖f.toStrongDual‖ ≤ r := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hf
    rw [Metric.mem_closedBall, dist_zero_right,
      (InnerProductSpace.toDual ℝ H).symm.norm_map]
    exact hf'
  · rintro ⟨y, hy, rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y), ?_, ?_⟩
    · change InnerProductSpace.toDual ℝ H y ∈
        Metric.closedBall (0 : StrongDual ℝ H) r
      rw [Metric.mem_closedBall, dist_zero_right,
        (InnerProductSpace.toDual ℝ H).norm_map]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    · simp [dualToWeak]

/-- Every closed ball in a Hilbert space is weakly compact. -/
theorem isCompact_closedBall_weak (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' Metric.closedBall (0 : H) r) := by
  rw [← dualToWeak_ball_image (H := H) r]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) r).image
    continuous_dualToWeak

/-- In a separable Hilbert space, the same weak ball is sequentially compact. -/
theorem isSeqCompact_closedBall_weak [TopologicalSpace.SeparableSpace H] (r : ℝ) :
    IsSeqCompact (toWeakSpace ℝ H '' Metric.closedBall (0 : H) r) := by
  rw [← dualToWeak_ball_image (H := H) r]
  exact IsSeqCompact.image continuous_dualToWeak.seqContinuous
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) r)

/-- Explicit sequential form of weak compactness, retaining the same norm bound. -/
theorem exists_weak_subsequence_of_norm_le [TopologicalSpace.SeparableSpace H]
    (r : ℝ) (F : ℕ → H) (hF : ∀ n, ‖F n‖ ≤ r) :
    ∃ f : H, ‖f‖ ≤ r ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ H (F (φ n))) atTop
        (𝓝 (toWeakSpace ℝ H f)) := by
  have hmem (n : ℕ) : toWeakSpace ℝ H (F n) ∈
      toWeakSpace ℝ H '' Metric.closedBall (0 : H) r := by
    refine ⟨F n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hF n
  obtain ⟨x, hx, φ, hφ, hlim⟩ := isSeqCompact_closedBall_weak (H := H) r hmem
  obtain ⟨f, hf, rfl⟩ := hx
  refine ⟨f, ?_, φ, hφ, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hf
  · simpa only [Function.comp_def] using hlim

end RiemannResearch.Analysis.HilbertWeakCompactness
