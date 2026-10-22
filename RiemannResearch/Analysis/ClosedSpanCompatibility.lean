import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith

/-!
# Compatibility of a strong limit with a closed dictionary span

For a sequence whose strong limit belongs to the closed dictionary span,
vanishing of each fixed dictionary pairing forces the strong limit to vanish.
No dimension-dependent inverse Gram estimate is required. The strong-limit
and closed-span hypotheses are essential and remain explicit.
-/

namespace RiemannResearch.Analysis.ClosedSpanCompatibility

open Filter
open scoped Topology

variable {ι α H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem eq_zero_of_mem_closedSpan_of_inner_eq_zero (u : ι → H) (z : H)
    (hz : z ∈ (Submodule.span ℝ (Set.range u)).topologicalClosure)
    (hi : ∀ i, inner ℝ (u i) z = 0) : z = 0 := by
  have hs : Submodule.span ℝ (Set.range u) ≤ (innerSL ℝ z).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ z (u i) = 0
    rw [real_inner_comm]
    exact hi i
  have hc := Submodule.topologicalClosure_minimal _ hs (innerSL ℝ z).isClosed_ker
  have he : inner ℝ z z = 0 := hc hz
  rw [real_inner_self_eq_norm_sq] at he
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg z]

/-- Strong convergence turns fixed dictionary pairings into a complete
zero-limit criterion when the limit lies in their closed span. -/
theorem strongLimit_eq_zero_iff (u : ι → H) {l : Filter α} [l.NeBot]
    (f : α → H) (z : H) (hf : Tendsto f l (𝓝 z))
    (hz : z ∈ (Submodule.span ℝ (Set.range u)).topologicalClosure) :
    z = 0 ↔ ∀ i, Tendsto (fun n => inner ℝ (u i) (f n)) l (𝓝 0) := by
  constructor
  · rintro rfl i
    have h := (((innerSL ℝ (u i)).continuous.tendsto 0).comp hf)
    change Tendsto (fun n => inner ℝ (u i) (f n)) l
      (𝓝 (inner ℝ (u i) 0)) at h
    simpa only [inner_zero_right] using h
  · intro hi
    apply eq_zero_of_mem_closedSpan_of_inner_eq_zero u z hz
    intro i
    exact tendsto_nhds_unique
      (((innerSL ℝ (u i)).continuous.tendsto z).comp hf) (hi i)

end RiemannResearch.Analysis.ClosedSpanCompatibility
