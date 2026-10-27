/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CommutingProjectionEnergy
import RiemannResearch.Analysis.DecreasingProjectionLimit
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ENNReal.BigOperators

/-!
# Countable gap-one inequality for commuting orthogonal projections

Finite tensorization is passed to the strong limit on the intersection of
all fixed spaces. The right side is ENNReal-valued, so no summability premise
or artificial value for a divergent real tsum enters the theorem.
Source: the user-provided countable resampling Poincare agenda; the projection
limit uses Mathlib's monotone orthogonal projection theorem.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.Analysis.CountableProjectionPoincare
open CommutingProjectionEnergy DecreasingProjectionLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem projection_poincare (K : ℕ → Submodule ℝ H)
    [∀ i, (K i).HasOrthogonalProjection] [(⨅ i, K i).HasOrthogonalProjection]
    (hcomm : ∀ i j x, (K i).starProjection ((K j).starProjection x) =
      (K j).starProjection ((K i).starProjection x)) (x : H) :
    ENNReal.ofReal (‖x‖ ^ 2 - ‖(⨅ i, K i).starProjection x‖ ^ 2) ≤
      ∑' i : ℕ, ENNReal.ofReal (‖x - (K i).starProjection x‖ ^ 2) := by
  letI : ∀ n, (prefixSpace K n).HasOrthogonalProjection :=
    fun n => prefixSpace_hasOrthogonalProjection K hcomm n
  letI : (⨅ n, prefixSpace K n).HasOrthogonalProjection := by
    rw [iInf_prefixSpace_eq_iInf]
    infer_instance
  have hlim : Tendsto (fun n => (prefixSpace K n).starProjection x) atTop
      (𝓝 ((⨅ i, K i).starProjection x)) := by
    simpa only [iInf_prefixSpace_eq_iInf] using
      starProjection_tendsto_iInf (prefixSpace K) (prefixSpace_antitone K) x
  have hreal : Tendsto (fun n => ‖x‖ ^ 2 - ‖(prefixSpace K n).starProjection x‖ ^ 2)
      atTop (𝓝 (‖x‖ ^ 2 - ‖(⨅ i, K i).starProjection x‖ ^ 2)) :=
    tendsto_const_nhds.sub (hlim.norm.pow 2)
  have hext : Tendsto
      (fun n => ENNReal.ofReal (‖x‖ ^ 2 - ‖(prefixSpace K n).starProjection x‖ ^ 2))
      atTop (𝓝 (ENNReal.ofReal (‖x‖ ^ 2 - ‖(⨅ i, K i).starProjection x‖ ^ 2))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply le_of_tendsto hext
  apply Eventually.of_forall
  intro n
  calc
    _ ≤ ENNReal.ofReal (∑ i ∈ Finset.range n, ‖x - (K i).starProjection x‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (norm_sq_sub_prefixSpace_projection_norm_sq_le K hcomm n x)
    _ = ∑ i ∈ Finset.range n, ENNReal.ofReal (‖x - (K i).starProjection x‖ ^ 2) :=
      ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)
    _ ≤ _ := ENNReal.sum_le_tsum (Finset.range n)

end RiemannResearch.Analysis.CountableProjectionPoincare
