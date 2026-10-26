/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeTailResponse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Exact signed prediction from the actual squarefree response head

Source: user-provided head-boundary and weighted-Bessel handoff, R2,
25 October 2026; direct Hilbert-space argument. Every norm and projection
uses the complete Q-Hilbert space. No positivity or bounded row-sum
assertion for prediction coefficients is made.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeHeadPrediction
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QSquarefreeTailResponse QSquarefreeCorrectionKernel
open RiemannResearch.Analysis.ResidualizedProjectionKernel

/-- All actual evaluation kernels on the first H physical sites. -/
def headKernelSpace (N H : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun i : Fin H => kernel N (i.val + 1)))

theorem kernel_mem_headKernelSpace (N H : ℕ) (i : Fin H) :
    kernel N (i.val + 1) ∈ headKernelSpace N H :=
  Submodule.subset_span ⟨i, rfl⟩

theorem headKernelSpace_le_stage (N H : ℕ) : headKernelSpace N H ≤ stage N := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact (stage N).starProjection_apply_mem _

instance headKernelSpace_finiteDimensional (N H : ℕ) :
    FiniteDimensional ℝ (headKernelSpace N H) :=
  Submodule.finiteDimensional_of_le (headKernelSpace_le_stage N H)

theorem tail_mem_headKernelSpace_orthogonal (N H : ℕ) (f : QHilbert)
    (hf : f ∈ tailStage N H) : f ∈ (headKernelSpace N H)ᗮ := by
  apply ((headKernelSpace N H).mem_orthogonal f).mpr
  intro x hx
  change x ∈ Submodule.span ℝ (Set.range (fun i : Fin H => kernel N (i.val + 1))) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [real_inner_comm, inner_kernel_of_stage N _ f hf.1]
      exact physical_zero_of_mem hf.2 _ (by omega)
  | zero => simp
  | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
  | smul a x hx ih => rw [real_inner_smul_left, ih, mul_zero]

theorem tail_mem_of_stage_headKernelSpace_orthogonal (N H : ℕ) (f : QHilbert)
    (hf : f ∈ stage N) (ho : f ∈ (headKernelSpace N H)ᗮ) :
    f ∈ tailStage N H := by
  refine ⟨hf, ?_⟩
  apply mem_headNull_of_physical_zero
  intro n hn
  cases n with
  | zero => rfl
  | succ i =>
      have hi : i < H := by omega
      have hz := Submodule.inner_right_of_mem_orthogonal
        (kernel_mem_headKernelSpace N H ⟨i, hi⟩) ho
      rw [real_inner_comm, inner_kernel_of_stage N (i + 1) f hf] at hz
      exact hz

/-- The head kernel span is exactly the legal minimum-norm extension space. -/
theorem headKernelSpace_eq (N H : ℕ) :
    headKernelSpace N H = stage N ⊓ (tailStage N H)ᗮ := by
  apply le_antisymm
  · intro f hf
    refine ⟨headKernelSpace_le_stage N H hf, ?_⟩
    apply ((tailStage N H).mem_orthogonal f).mpr
    intro t ht
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hf
      (tail_mem_headKernelSpace_orthogonal N H t ht)
  · intro f hf
    let p := (headKernelSpace N H).starProjection f
    let d := f - p
    have hp : p ∈ headKernelSpace N H := (headKernelSpace N H).starProjection_apply_mem f
    have hdS : d ∈ stage N :=
      (stage N).sub_mem hf.1 (headKernelSpace_le_stage N H hp)
    have hdO : d ∈ (headKernelSpace N H)ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal (K := headKernelSpace N H) f
    have hdT := tail_mem_of_stage_headKernelSpace_orthogonal N H d hdS hdO
    have hdf : inner ℝ d f = 0 := Submodule.inner_right_of_mem_orthogonal hdT hf.2
    have hdp : inner ℝ d p = 0 := by
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal hp hdO
    have hdd' : inner ℝ d d = 0 := calc
      _ = inner ℝ d (f - p) := rfl
      _ = 0 := by rw [inner_sub_right, hdf, hdp, sub_zero]
    have hdd : ‖d‖ ^ 2 = 0 := by
      simpa only [real_inner_self_eq_norm_sq] using hdd'
    have hd0 : d = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg d])
    have hfp : f = p := sub_eq_zero.mp hd0
    rw [hfp]
    exact hp

theorem headResponse_mem_headKernelSpace (N H : ℕ) :
    headResponse N H ∈ headKernelSpace N H := by
  rw [headKernelSpace_eq]
  exact ⟨headResponse_mem_stage N H, headResponse_mem_orthogonal N H⟩

/-- The pre-existing response split is exactly the low-head projection split. -/
theorem headResponse_eq_projection (N H : ℕ) :
    headResponse N H =
      (headKernelSpace N H).starProjection (movingCorrection N) := by
  rw [response_split N H, map_add,
    Submodule.starProjection_eq_self_iff.mpr (headResponse_mem_headKernelSpace N H),
    (headKernelSpace N H).starProjection_apply_eq_zero_iff.mpr
      (tail_mem_headKernelSpace_orthogonal N H _ (tailResponse_mem N H)), add_zero]

/-- Exact signed prediction for any representation of the projected evaluation
vector; redundant head kernels and nonunique coefficients are permitted. -/
theorem headResponse_prediction (N H n : ℕ) (α : Fin H → ℝ)
    (hα : (headKernelSpace N H).starProjection (evaluation n) =
      ∑ i : Fin H, α i • kernel N (i.val + 1)) :
    qSequence (headResponse N H) n =
      ∑ i : Fin H, α i * qSequence (movingCorrection N) (i.val + 1) := by
  rw [← inner_evaluation,
    RiemannResearch.Analysis.DenseProjectionTesting.inner_eq_projected_test
      (headKernelSpace N H) (headResponse_mem_headKernelSpace N H), hα]
  simp only [inner_sum, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_kernel_of_stage N _ _ (headResponse_mem_stage N H),
    headResponse_agrees N H _ (by omega)]

/-- The prediction coefficients solve the complete signed head Gram system. -/
theorem prediction_normal (N H n : ℕ) (α : Fin H → ℝ)
    (hα : (headKernelSpace N H).starProjection (evaluation n) =
      ∑ i : Fin H, α i • kernel N (i.val + 1)) (j : Fin H) :
    (∑ i : Fin H,
      inner ℝ (kernel N (j.val + 1)) (kernel N (i.val + 1)) * α i) =
      inner ℝ (kernel N (j.val + 1)) (kernel N n) := by
  have he := RiemannResearch.Analysis.DenseProjectionTesting.inner_eq_projected_test
    (headKernelSpace N H) (kernel_mem_headKernelSpace N H j) (evaluation n)
  rw [hα] at he
  rw [inner_kernel_of_stage N n (kernel N (j.val + 1))
    ((stage N).starProjection_apply_mem (evaluation (j.val + 1)))]
  rw [← inner_evaluation, he]
  simp only [inner_sum, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

/-- Such a signed prediction exists for every target site, without an
invertibility hypothesis on the head Gram matrix. -/
theorem exists_headResponse_prediction (N H n : ℕ) :
    ∃ α : Fin H → ℝ,
      (headKernelSpace N H).starProjection (evaluation n) =
        (∑ i : Fin H, α i • kernel N (i.val + 1)) ∧
      qSequence (headResponse N H) n =
        ∑ i : Fin H, α i * qSequence (movingCorrection N) (i.val + 1) := by
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((headKernelSpace N H).starProjection_apply_mem (evaluation n))
  exact ⟨α, hα.symm, headResponse_prediction N H n α hα.symm⟩

/-- Full response prediction retains the actual complete tail response. -/
theorem response_prediction (N H n : ℕ) (α : Fin H → ℝ)
    (hα : (headKernelSpace N H).starProjection (evaluation n) =
      ∑ i : Fin H, α i • kernel N (i.val + 1)) :
    qSequence (movingCorrection N) n =
      (∑ i : Fin H, α i * qSequence (movingCorrection N) (i.val + 1)) +
        qSequence (tailResponse N H) n := by
  conv_lhs => rw [response_split N H]
  change qSequenceLinear (headResponse N H + tailResponse N H) n = _
  rw [map_add]
  change qSequence (headResponse N H) n + qSequence (tailResponse N H) n = _
  rw [headResponse_prediction N H n α hα]

/-- The signed prediction error is controlled by the complete residual tail. -/
theorem response_prediction_error_bound (N H n : ℕ) (α : Fin H → ℝ)
    (hα : (headKernelSpace N H).starProjection (evaluation n) =
      ∑ i : Fin H, α i • kernel N (i.val + 1)) :
    |qSequence (movingCorrection N) n -
      (∑ i : Fin H, α i * qSequence (movingCorrection N) (i.val + 1))| ≤
      Real.sqrt ZetaTwoProbability.zetaTwo * (n : ℝ) /
        (2 * ((H : ℝ) + 2)) *
          ‖QAnnihilatorTailEscape.tail H (residual N)‖ := by
  rw [response_prediction N H n α hα, add_sub_cancel_left]
  exact tailResponse_physical_bound N H n

end RiemannResearch.RH.QSquarefreeHeadPrediction
