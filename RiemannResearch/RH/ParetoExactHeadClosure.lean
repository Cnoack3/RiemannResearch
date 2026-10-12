import RiemannResearch.Analysis.WeakConvergenceDenseTests
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ThresholdHilbertMean

/-!
# Bounded exact heads imply membership in the actual Pareto closure

Source: user-provided argument, `RH_Minimal_Seeds_Continuation_20260916.md`,
Section 13. This proof uses dense physical-coordinate tests to pass to the
closed subspace, without an abstract compactness-provider hypothesis.
The RH implication from bounded exact-subspace heads is assembled in
`BalancedExactHeadEnergy`; this module contains the general closure facts.
-/

open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem paretoPoint_span_dense :
    (Submodule.span ℝ (Set.range paretoPointHilbert)).topologicalClosure = ⊤ := by
  have ho : (Submodule.span ℝ (Set.range paretoPointHilbert))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext n
    have h : inner ℝ (paretoPointHilbert n) f = 0 :=
      hf _ (Submodule.subset_span ⟨n, rfl⟩)
    rw [real_inner_comm, inner_paretoPoint] at h
    have hp : hilbertGibbsPhysical f n = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt (paretoWeight_pos n))
    unfold hilbertGibbsPhysical at hp
    have hs : Real.sqrt (paretoWeight n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos n))
    change f n = 0
    exact (div_eq_zero_iff.mp hp).resolve_right hs
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ho]
  simp

theorem hilbertOne_mem_closure_of_bounded_exact_heads
    (S : Submodule ℝ ThresholdHilbert) (f : ℕ → ThresholdHilbert)
    (hmem : ∀ N, f N ∈ S)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = 1)
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ≤ C) :
    hilbertOne ∈ S.topologicalClosure := by
  let u : ℕ → ThresholdHilbert := fun N => f N - hilbertOne
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hbounded 0)
  have hb : ∀ᶠ N in atTop, ‖u N‖ ≤ C + ‖hilbertOne‖ :=
    Filter.Eventually.of_forall fun N =>
      (norm_sub_le _ _).trans (add_le_add (hbounded N) le_rfl)
  have hp : ∀ y ∈ Set.range paretoPointHilbert,
      Tendsto (fun N => inner ℝ y (u N)) atTop (𝓝 0) := by
    rintro y ⟨n, rfl⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n+1)] with N hN
    rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq]
    change 0 = paretoWeight n * hilbertSequenceLinear (f N - hilbertOne) (n+1)
    rw [map_sub]
    change 0 = paretoWeight n * (hilbertSequence (f N) (n+1) -
      hilbertSequence hilbertOne (n+1))
    rw [hhead N (n+1) (by omega) hN, hilbertOne_sequence]
    simp [zeroAnchor]
  have hw (x : ThresholdHilbert) :
      Tendsto (fun N => inner ℝ x (u N)) atTop (𝓝 0) :=
    RiemannResearch.Analysis.tendsto_inner_zero_of_mem_closure_span
      (by positivity) hb hp (by rw [paretoPoint_span_dense]; trivial)
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  intro x hx
  have hz (N : ℕ) : inner ℝ x (f N) = 0 := by
    rw [real_inner_comm]
    exact hx _ (hmem N)
  have ht := hw x
  have he : (fun N => inner ℝ x (u N)) = fun _ : ℕ => -inner ℝ x hilbertOne := by
    funext N
    simp [u, inner_sub_right, hz]
  rw [he] at ht
  have hh : -inner ℝ x hilbertOne = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  linarith


theorem hilbertOne_mem_closure_of_bounded_exact_head_energy
    (S : Submodule ℝ ThresholdHilbert) (f : ℕ → ThresholdHilbert)
    (hmem : ∀ N, f N ∈ S)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = 1)
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ^ 2 ≤ C) :
    hilbertOne ∈ S.topologicalClosure := by
  have hC : 0 ≤ C := (sq_nonneg ‖f 0‖).trans (hbounded 0)
  apply hilbertOne_mem_closure_of_bounded_exact_heads S f hmem hhead
    (C := C + 1)
  intro N
  have := hbounded N
  nlinarith [sq_nonneg (‖f N‖ - 1)]


end
end RiemannResearch.RH.Pareto
