/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.HilbertWeakCompactness
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Tactic.Choose
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Bounded interpolation from weak-star compactness

Source: the user's weak-star compactness request, 6 November 2026.
This specializes Banach--Alaoglu and Riesz representation via Mathlib;
no mathematical priority claim is made.
The proof transports Banach--Alaoglu through the existing Hilbert-space Riesz
representation theorem. Interpolation uses a compact image in the product of
all scalar tests, with no separability hypothesis. The separate subsequence
extraction theorem retains its explicit separability assumption.
No strong convergence or vanishing infinite-tail error is assumed.
-/

noncomputable section
open Filter
open scoped Topology

namespace WeakSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weak convergence determines the limit of every continuous linear scalar test. -/
theorem tendsto_eval_of_tendsto {ι : Type*} {l : Filter ι}
    {F : ι → H} {f : H}
    (hF : Tendsto (fun i => toWeakSpace ℝ H (F i)) l (𝓝 (toWeakSpace ℝ H f)))
    (L : H →L[ℝ] ℝ) : Tendsto (fun i => L (F i)) l (𝓝 (L f)) := by
  exact ((WeakBilin.eval_continuous (topDualPairing ℝ H).flip L).tendsto
    (toWeakSpace ℝ H f)).comp hF

end WeakSpace

namespace Submodule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A bounded sequence in a complete separable subspace has an ambient weak
subsequence whose limit remains in that same subspace and norm ball. -/
theorem exists_ambient_weak_subsequence_of_norm_le (S : Submodule ℝ H)
    [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (C : ℝ) (F : ℕ → H) (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F n‖ ≤ C) :
    ∃ f ∈ S, ‖f‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ H (F (φ n))) atTop
        (𝓝 (toWeakSpace ℝ H f)) := by
  let G : ℕ → S := fun n => ⟨F n, hmem n⟩
  have hG : ∀ n, ‖G n‖ ≤ C := hbound
  obtain ⟨g, hg, φ, hφ, hlim⟩ :=
    RiemannResearch.Analysis.HilbertWeakCompactness.exists_weak_subsequence_of_norm_le
      C G hG
  refine ⟨(g : H), g.property, hg, φ, hφ, ?_⟩
  exact ((WeakSpace.map S.subtypeL).continuous.tendsto _).comp hlim

/-- Bounded approximate interpolation of arbitrary continuous linear tests
produces an exact simultaneous interpolant in the same complete norm ball.
The compact product image proof needs no separability or subsequence extraction. -/
theorem exists_mem_of_bounded_test_limits (S : Submodule ℝ H)
    [CompleteSpace S]
    {ι : Type*} (C : ℝ) (F : ℕ → H)
    (hmem : ∀ n, F n ∈ S) (hbound : ∀ n, ‖F n‖ ≤ C)
    (L : ι → H →L[ℝ] ℝ) (b : ι → ℝ)
    (hlim : ∀ i, Tendsto (fun n => L i (F n)) atTop (𝓝 (b i))) :
    ∃ f ∈ S, ‖f‖ ≤ C ∧ ∀ i, L i f = b i := by
  let test : WeakSpace ℝ S → (ι → ℝ) := fun w i =>
    ((L i).comp S.subtypeL) ((toWeakSpace ℝ S).symm w)
  have ht : Continuous test := by
    apply continuous_pi
    intro i
    exact WeakBilin.eval_continuous (topDualPairing ℝ S).flip
      ((L i).comp S.subtypeL)
  have hc := (RiemannResearch.Analysis.HilbertWeakCompactness.isCompact_closedBall_weak
    (H := S) C).image ht
  have hb : b ∈ test '' (toWeakSpace ℝ S '' Metric.closedBall (0 : S) C) := by
    apply hc.isClosed.mem_of_tendsto (tendsto_pi_nhds.mpr hlim)
    apply Eventually.of_forall
    intro n
    refine ⟨toWeakSpace ℝ S ⟨F n, hmem n⟩, ?_, ?_⟩
    · exact ⟨⟨F n, hmem n⟩, by simpa using hbound n, rfl⟩
    · rfl
  obtain ⟨w, ⟨f, hf, rfl⟩, hfb⟩ := hb
  refine ⟨f, f.property, ?_, ?_⟩
  · simpa using hf
  · intro i
    exact congrFun hfb i

/-- Uniformly bounded feasibility of every finite test head is equivalent to
one bounded exact solution of all countably many tests. -/
theorem bounded_finite_test_feasibility_iff (S : Submodule ℝ H)
    [CompleteSpace S]
    (C : ℝ) (L : ℕ → H →L[ℝ] ℝ) (b : ℕ → ℝ) :
    (∀ N, ∃ f ∈ S, ‖f‖ ≤ C ∧ ∀ n < N, L n f = b n) ↔
      ∃ f ∈ S, ‖f‖ ≤ C ∧ ∀ n, L n f = b n := by
  constructor
  · intro h
    choose F hmem hbound hhead using h
    apply S.exists_mem_of_bounded_test_limits C F hmem hbound L b
    intro n
    apply (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => b n) atTop (𝓝 (b n))).congr'
    filter_upwards [eventually_gt_atTop n] with M hM
    exact (hhead M n hM).symm
  · rintro ⟨f, hf, hn, ht⟩ N
    exact ⟨f, hf, hn, fun n _ => ht n⟩

/-- Exact coordinate feasibility for images of bounded vectors. The image
need not be separately declared closed: the source weak limit supplies a preimage. -/
theorem bounded_lp_head_image_feasibility_iff (S : Submodule ℝ H)
    [CompleteSpace S]
    (C : ℝ) (L : H →L[ℝ] lp (fun _ : ℕ => ℝ) 2) (x : lp (fun _ : ℕ => ℝ) 2) :
    (∀ N, ∃ f ∈ S, ‖f‖ ≤ C ∧ ∀ n < N, L f n = x n) ↔
      ∃ f ∈ S, ‖f‖ ≤ C ∧ L f = x := by
  constructor
  · intro h
    obtain ⟨f, hf, hn, ht⟩ :=
      (S.bounded_finite_test_feasibility_iff C
        (fun n => (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).comp L)
        (fun n => x n)).mp h
    refine ⟨f, hf, hn, ?_⟩
    apply lp.ext
    funext n
    exact ht n
  · rintro ⟨f, hf, hn, ht⟩ N
    refine ⟨f, hf, hn, fun n _ => ?_⟩
    rw [ht]

end Submodule
