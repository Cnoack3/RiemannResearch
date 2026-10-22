import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Convex repair from weak convergence

Source: Mathlib.Analysis.LocallyConvex.WeakSpace,
Convex.toWeakSpace_closure (the closure theorem and proof strategy), and
Mathlib.Analysis.InnerProductSpace.Dual (Riesz representation).
RH consumer: DyadicRemainderConvexRepair.

The weak and norm closures of a convex set agree. Consequently weak convergence
gives norm-small finite convex combinations drawn from each filter-large set.
This is the convex-closure argument behind Mazur's lemma. It does not imply
norm convergence of the original family or membership in any legal subspace.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Riesz representation identifies weak convergence with the convergence
of all fixed-vector pairings in a real Hilbert space. -/
theorem weak_tendsto_zero_of_inner_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {l : Filter I} {u : I → H}
    (hinner : ∀ x, Tendsto (fun i => inner ℝ x (u i)) l (𝓝 0)) :
    Tendsto (fun i => toWeakSpace ℝ H (u i)) l (𝓝 0) := by
  have hinj : Function.Injective (topDualPairing ℝ H).flip := by
    intro x y h
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro φ
    exact congrArg (fun f : (StrongDual ℝ H) →ₗ[ℝ] ℝ => f φ) h
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
  intro φ
  change Tendsto (fun i => φ (u i)) l (𝓝 (φ 0))
  simpa only [InnerProductSpace.toDual_symm_apply, map_zero] using
    hinner ((InnerProductSpace.toDual ℝ H).symm φ)

/-- Every tail of a weakly null family has zero in its norm closed convex hull. -/
theorem zero_mem_closure_convexHull_image_of_weak_tendsto
    {l : Filter I} [l.NeBot] {u : I → E}
    (hweak : Tendsto (fun i => toWeakSpace ℝ E (u i)) l (𝓝 0))
    {A : Set I} (hA : A ∈ l) :
    (0 : E) ∈ closure (convexHull ℝ (u '' A)) := by
  have hmem : (0 : WeakSpace ℝ E) ∈
      closure (toWeakSpace ℝ E '' convexHull ℝ (u '' A)) := by
    apply mem_closure_of_tendsto hweak
    filter_upwards [hA] with i hi
    exact ⟨u i, subset_convexHull ℝ _ ⟨i, hi, rfl⟩, rfl⟩
  rw [← (convex_convexHull ℝ (u '' A)).toWeakSpace_closure ℝ] at hmem
  obtain ⟨x, hx, hx0⟩ := hmem
  have hxzero : x = 0 := (toWeakSpace ℝ E).injective (by simpa using hx0)
  simpa only [hxzero] using hx

/-- Arbitrarily small norm is achieved by a finite convex combination of
actual members in any filter-large parameter set. -/
theorem exists_norm_lt_mem_convexHull_image_of_weak_tendsto
    {l : Filter I} [l.NeBot] {u : I → E}
    (hweak : Tendsto (fun i => toWeakSpace ℝ E (u i)) l (𝓝 0))
    {A : Set I} (hA : A ∈ l) {η : ℝ} (hη : 0 < η) :
    ∃ v ∈ convexHull ℝ (u '' A), ‖v‖ < η := by
  obtain ⟨v, hv, hvdist⟩ := Metric.mem_closure_iff.mp
    (zero_mem_closure_convexHull_image_of_weak_tendsto hweak hA) η hη
  exact ⟨v, hv, by simpa only [dist_zero_left] using hvdist⟩

end RiemannResearch.Analysis
