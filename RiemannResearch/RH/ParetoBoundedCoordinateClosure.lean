import RiemannResearch.RH.ParetoExactHeadClosure
import RiemannResearch.RH.MobiusResidualFirstCoordinate

/-!
# Bounded coordinatewise approximation to the first-point target

Source: user-provided `ParetoCapacityFormalization20260921_Continued_ParityClosure (1).md`,
supplement "A bounded-family route remains possible". The convergence theorem
uses actual physical coordinates and the entire Hilbert norm. The RH endpoint
is a conditional research reduction: existence of the uniformly bounded legal
family remains an explicit open hypothesis.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

/-- Boundedness and convergence of every physical coordinate place the limit
in the norm-closed span; strong convergence of the family is not required. -/
theorem mem_closure_of_bounded_coordinate_limits
    (S : Submodule ℝ ThresholdHilbert) (f : ℕ → ThresholdHilbert)
    (x : ThresholdHilbert) (hmem : ∀ N, f N ∈ S)
    (hcoord : ∀ k, 0 < k → Tendsto (fun N => hilbertSequence (f N) k) atTop
      (𝓝 (hilbertSequence x k)))
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ≤ C) :
    x ∈ S.topologicalClosure := by
  let u : ℕ → ThresholdHilbert := fun N => f N - x
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hbounded 0)
  have hb : ∀ᶠ N in atTop, ‖u N‖ ≤ C + ‖x‖ :=
    Filter.Eventually.of_forall fun N =>
      (norm_sub_le _ _).trans (add_le_add (hbounded N) le_rfl)
  have hp : ∀ y ∈ Set.range paretoPointHilbert,
      Tendsto (fun N => inner ℝ y (u N)) atTop (𝓝 0) := by
    rintro y ⟨n, rfl⟩
    have he (N : ℕ) : inner ℝ (paretoPointHilbert n) (u N) =
        paretoWeight n * (hilbertSequence (f N) (n + 1) - hilbertSequence x (n + 1)) := by
      rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq]
      change paretoWeight n * hilbertSequenceLinear (f N - x) (n + 1) = _
      rw [map_sub]
      rfl
    simpa only [he, sub_self, mul_zero] using
      ((hcoord (n + 1) (by omega)).sub
        (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => hilbertSequence x (n + 1)) atTop
          (𝓝 (hilbertSequence x (n + 1))))).const_mul (paretoWeight n)
  have hw (y : ThresholdHilbert) :
      Tendsto (fun N => inner ℝ y (u N)) atTop (𝓝 0) :=
    RiemannResearch.Analysis.tendsto_inner_zero_of_mem_closure_span
      (by positivity) hb hp (by rw [paretoPoint_span_dense]; trivial)
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  intro y hy
  have hz (N : ℕ) : inner ℝ y (f N) = 0 := by
    rw [real_inner_comm]
    exact hy _ (hmem N)
  have ht := hw y
  have he : (fun N => inner ℝ y (u N)) = fun _ : ℕ => -inner ℝ y x := by
    funext N
    simp [u, inner_sub_right, hz]
  rw [he] at ht
  have hh : -inner ℝ y x = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  linarith

/-- Exact agreement on successively larger heads is a concrete sufficient
coordinatewise convergence hypothesis for any target. -/
theorem mem_closure_of_bounded_matching_heads
    (S : Submodule ℝ ThresholdHilbert) (f : ℕ → ThresholdHilbert)
    (x : ThresholdHilbert) (hmem : ∀ N, f N ∈ S)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = hilbertSequence x k)
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ^ 2 ≤ C) :
    x ∈ S.topologicalClosure := by
  apply mem_closure_of_bounded_coordinate_limits S f x hmem (C := C + 1)
  · intro k hk
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with N hN
    exact (hhead N k hk hN).symm
  · intro N
    have := hbounded N
    nlinarith [sq_nonneg (‖f N‖ - 1)]

namespace CoefficientStabilization

/-- A bounded family of actual legal vectors approaching a nonzero multiple
of the first point in each coordinate suffices for Mathlib RH. -/
theorem riemannHypothesis_of_bounded_firstPoint_coordinate_limits
    (f : ℕ → ThresholdHilbert) (hmem : ∀ N, f N ∈ closedSpace)
    {a : ℝ} (ha : a ≠ 0)
    (hcoord : ∀ k, 0 < k → Tendsto (fun N => hilbertSequence (f N) k) atTop
      (𝓝 (hilbertSequence (a • paretoPointHilbert 0) k)))
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ≤ C) : RiemannHypothesis := by
  have hm := mem_closure_of_bounded_coordinate_limits closedSpace f
    (a • paretoPointHilbert 0) hmem hcoord hbounded
  have hc : IsClosed (closedSpace : Set ThresholdHilbert) :=
    Submodule.isClosed_topologicalClosure _
  have ht : a • paretoPointHilbert 0 ∈ closedSpace :=
    closedSpace.topologicalClosure_minimal le_rfl hc hm
  have hp : paretoPointHilbert 0 ∈ closedSpace := by
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using
      closedSpace.smul_mem a⁻¹ ht
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (firstPoint_mem_iff_one_mem.mp hp))

/-- The exact-head family proposed in the source supplement only needs a
uniform bound on its full norm; a zero full-energy limit is unnecessary.
The bound is an unresolved substantive arithmetic premise. -/
theorem riemannHypothesis_of_bounded_firstPoint_heads
    (f : ℕ → ThresholdHilbert) (hmem : ∀ N, f N ∈ closedSpace)
    {a : ℝ} (ha : a ≠ 0)
    (hhead : ∀ N k, 0 < k → k ≤ N →
      hilbertSequence (f N) k = hilbertSequence (a • paretoPointHilbert 0) k)
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ^ 2 ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_firstPoint_coordinate_limits f hmem ha (C := C + 1)
  · intro k hk
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with N hN
    exact (hhead N k hk hN).symm
  · intro N
    have := hbounded N
    nlinarith [sq_nonneg (‖f N‖ - 1)]

end CoefficientStabilization
end RiemannResearch.RH.Pareto
