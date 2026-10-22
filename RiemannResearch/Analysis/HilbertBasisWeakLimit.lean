import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Bounded Hilbert-basis coordinates determine weak pairings

Source: independently developed standard finite-approximation argument,
using Mathlib's HilbertBasis.hasSum_repr and Cauchy-Schwarz inequality.
RH consumer: DyadicRemainderConvexRepair applies this result to the actual
complete dyadic boundary basis and the actual arithmetic remainder.
-/

open Filter
open scoped BigOperators Topology

namespace HilbertBasis

theorem inner_tendsto_zero_of_bounded_coordinates
    {ι E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : HilbertBasis ι ℝ E) {l : Filter α} (u : α → E)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᶠ a in l, ‖u a‖ ≤ C)
    (hcoord : ∀ i, Tendsto (fun a => inner ℝ (b i) (u a)) l (𝓝 0))
    (x : E) : Tendsto (fun a => inner ℝ x (u a)) l (𝓝 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hsmall : 0 < η / (2 * (C + 1)) := by positivity
  have hs := (b.hasSum_repr x).eventually
    (Metric.ball_mem_nhds x hsmall)
  obtain ⟨s, hs⟩ := hs.exists
  let v : E := ∑ i ∈ s, (b.repr x) i • b i
  have hv : ‖x - v‖ < η / (2 * (C + 1)) := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, v] using hs
  have hlim : Tendsto (fun a => inner ℝ v (u a)) l (𝓝 0) := by
    have hh := tendsto_finsetSum s (fun i _ => (hcoord i).const_mul ((b.repr x) i))
    simpa only [v, sum_inner, real_inner_smul_left, mul_zero, Finset.sum_const_zero] using hh
  have he := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ)
    (show 0 < η / 2 by positivity))
  filter_upwards [hbound, he] with a ha hea
  have hea' : ‖inner ℝ v (u a)‖ < η / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hea
  have hxv : ‖x - v‖ * C < η / 2 := by
    have hmul := (lt_div_iff₀ (show 0 < 2 * (C+1) by positivity)).mp hv
    nlinarith [norm_nonneg (x-v)]
  have hsplit : inner ℝ x (u a) = inner ℝ (x-v) (u a) + inner ℝ v (u a) := by
    rw [inner_sub_left]
    ring
  rw [dist_zero_right, hsplit]
  calc
    _ ≤ ‖inner ℝ (x-v) (u a)‖ + ‖inner ℝ v (u a)‖ := norm_add_le _ _
    _ ≤ ‖x-v‖ * C + ‖inner ℝ v (u a)‖ := by
      exact add_le_add ((norm_inner_le_norm (𝕜 := ℝ) (x-v) (u a)).trans
        (mul_le_mul_of_nonneg_left ha (norm_nonneg _))) le_rfl
    _ < η := by linarith

end HilbertBasis
