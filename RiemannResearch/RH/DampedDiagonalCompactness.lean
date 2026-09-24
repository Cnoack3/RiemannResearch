import RiemannResearch.RH.ParetoBoundedCoordinateClosure

/-!
A countable diagonal compactness criterion. The norm
bound is in one fixed Hilbert norm, uniformly across damping and cutoff.

Source: user-proposed Cantor/weak-compactness approach. This formalization
uses the existing `mem_closure_of_bounded_coordinate_limits` theorem.
The arithmetic provider of the uniform bound is still open for the RH target;
see `HardyEndpointCompactness20260924.md`.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

/-- Finite coordinate control suffices if one fixed Hilbert norm stays bounded. -/
theorem mem_closure_of_bounded_finite_coordinate_approximants
    {ι : Type*} (S : Submodule ℝ ThresholdHilbert) (f : ι → ThresholdHilbert)
    (x : ThresholdHilbert) (hmem : ∀ a, f a ∈ S) {C : ℝ}
    (happrox : ∀ j : ℕ, ∃ a : ι, ‖f a‖ ≤ C ∧
      ∀ k, 0 < k → k ≤ j →
        |hilbertSequence (f a) k - hilbertSequence x k| ≤
          (((j + 1 : ℕ) : ℝ))⁻¹) :
    x ∈ S.topologicalClosure := by
  choose a ha hcoord using happrox
  apply mem_closure_of_bounded_coordinate_limits S (fun j => f (a j)) x
    (fun j => hmem (a j)) _ ha
  intro k hk
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hinv : Tendsto (fun j : ℕ => (((j + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  apply squeeze_zero'
    (Eventually.of_forall (fun j => norm_nonneg _)) _ hinv
  filter_upwards [eventually_ge_atTop k] with j hj
  simpa only [Real.norm_eq_abs] using hcoord j k hk hj

/-- The explicit alpha/cutoff diagonal: shrinking alpha and growing cutoffs
are permitted, but the common-norm bound is an independent substantive premise. -/
theorem mem_closure_of_bounded_damping_diagonal
    (S : Submodule ℝ ThresholdHilbert) (f : ℝ → ℕ → ThresholdHilbert)
    (x : ThresholdHilbert) (hmem : ∀ α N, f α N ∈ S) {C : ℝ}
    (hdiag : ∀ j : ℕ, ∃ α : ℝ, ∃ N : ℕ,
      0 < α ∧ α ≤ (((j + 1 : ℕ) : ℝ))⁻¹ ∧ j ≤ N ∧
      ‖f α N‖ ≤ C ∧
      ∀ k, 0 < k → k ≤ j →
        |hilbertSequence (f α N) k - hilbertSequence x k| ≤
          (((j + 1 : ℕ) : ℝ))⁻¹) :
    x ∈ S.topologicalClosure := by
  apply mem_closure_of_bounded_finite_coordinate_approximants
    S (fun p : ℝ × ℕ => f p.1 p.2) x
    (fun p => hmem p.1 p.2)
  intro j
  obtain ⟨α, N, hα0, hαj, hNj, hbound, hhead⟩ := hdiag j
  exact ⟨(α, N), hbound, hhead⟩

end RiemannResearch.RH.Pareto
