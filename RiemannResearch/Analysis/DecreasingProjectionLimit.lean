/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Strong convergence of decreasing orthogonal projections

This is the orthogonal-complement form of Mathlib's
`Submodule.starProjection_tendsto_closure_iSup`. The source theorem and
orthogonal-complement identities supply the proof strategy:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.html
The concrete consumer is countable prime resampling in the Q Hilbert space.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.DecreasingProjectionLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem starProjection_tendsto_iInf
    (K : ℕ → Submodule ℝ H) [∀ n, (K n).HasOrthogonalProjection]
    [(⨅ n, K n).HasOrthogonalProjection] (hK : Antitone K) (x : H) :
    Tendsto (fun n => (K n).starProjection x) atTop
      (𝓝 ((⨅ n, K n).starProjection x)) := by
  have hmono : Monotone (fun n => (K n)ᗮ) :=
    fun i j hij => Submodule.orthogonal_le (hK hij)
  have he : (⨆ n, (K n)ᗮ).topologicalClosure = (⨅ n, K n)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    congr 1
    rw [← Submodule.iInf_orthogonal]
    simp only [Submodule.orthogonal_orthogonal]
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun n => (K n)ᗮ) hmono x
  have heproj : (⨆ n, (K n)ᗮ).topologicalClosure.starProjection =
      ((⨅ n, K n)ᗮ).starProjection := by
    congr 1
  rw [heproj] at ht
  have hsub : Tendsto (fun n => x - ((K n)ᗮ).starProjection x) atTop
      (𝓝 (x - ((⨅ n, K n)ᗮ).starProjection x)) := tendsto_const_nhds.sub ht
  simpa only [Submodule.starProjection_orthogonal_val, sub_sub_cancel] using hsub

end RiemannResearch.Analysis.DecreasingProjectionLimit
