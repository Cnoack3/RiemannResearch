/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ProjectedObservationTests
import RiemannResearch.RH.ParetoGibbsTailBasis

/-!
# Pareto exact heads and internal projected-coordinate tests

Source: user-requested Ramanujan/Pareto weak-star closure argument,
28 October 2026. The only convergence
premise beyond exact heads concerns explicit projected point observations.
It can be supplied by genuine weak-star convergence on the whole closed
legal space. Convergence merely on its algebraic generators does not supply it.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.ParetoProjectedHeadTests
open Pareto
open RiemannResearch.Analysis.ProjectedObservationTests

theorem paretoPoint_pairing (n : ℕ) (f : ThresholdHilbert) :
    inner ℝ (paretoPointHilbert n) f =
      paretoWeight n * hilbertSequence f (n + 1) := by
  rw [real_inner_comm, inner_paretoPoint, hilbertGibbsPhysical_eq]

theorem paretoPoints_separate (f : ThresholdHilbert)
    (h : ∀ n, inner ℝ (paretoPointHilbert n) f = 0) : f = 0 := by
  apply Subtype.ext
  funext n
  have hn := h n
  rw [real_inner_comm, inner_paretoPoint] at hn
  have hf : hilbertGibbsPhysical f n = 0 :=
    (mul_eq_zero.mp hn).resolve_left (ne_of_gt (paretoWeight_pos n))
  unfold hilbertGibbsPhysical at hf
  have hs : Real.sqrt (paretoWeight n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos n))
  change f n = 0
  exact (div_eq_zero_iff.mp hf).resolve_right hs

variable {I : Type*} {l : Filter I} [NeBot l]
variable (L : Submodule ℝ ThresholdHilbert) [CompleteSpace L]

theorem projection_eq_of_eventually_exact_heads
    (F : I → ThresholdHilbert) (x : ThresholdHilbert)
    (hF : ∀ᶠ i in l, F i ∈ L)
    (hhead : ∀ k : ℕ, 0 < k → ∀ᶠ i in l,
      hilbertSequence (F i) k = hilbertSequence x k)
    (hint : ∀ n : ℕ, Tendsto
      (fun i => inner ℝ (L.starProjection (paretoPointHilbert n)) (F i - x))
      l (𝓝 0)) : L.starProjection x = x := by
  apply projection_eq_of_projected_exact_tests L F x paretoPointHilbert
    paretoPoints_separate hF
  · intro n
    filter_upwards [hhead (n + 1) (Nat.succ_pos n)] with i hi
    rw [paretoPoint_pairing, paretoPoint_pairing, hi]
  · exact hint

theorem projection_eq_of_internal_tests_and_exact_heads
    (F : I → ThresholdHilbert) (x : ThresholdHilbert)
    (hF : ∀ᶠ i in l, F i ∈ L)
    (hhead : ∀ k : ℕ, 0 < k → ∀ᶠ i in l,
      hilbertSequence (F i) k = hilbertSequence x k)
    (hint : ∀ v : ThresholdHilbert, v ∈ L →
      Tendsto (fun i => inner ℝ v (F i)) l (𝓝 (inner ℝ v x))) :
    L.starProjection x = x := by
  apply projection_eq_of_eventually_exact_heads L F x hF hhead
  intro n
  have ht := hint (L.starProjection (paretoPointHilbert n))
    (L.starProjection_apply_mem (paretoPointHilbert n))
  have hs := ht.sub_const (inner ℝ (L.starProjection (paretoPointHilbert n)) x)
  simpa only [inner_sub_right, sub_self] using hs

theorem projection_eq_of_cofinal_exact_heads
    (F : ℕ → ThresholdHilbert) (x : ThresholdHilbert) (H : ℕ → ℕ)
    (hF : ∀ n, F n ∈ L) (hH : Tendsto H atTop atTop)
    (hhead : ∀ i k, 0 < k → k ≤ H i →
      hilbertSequence (F i) k = hilbertSequence x k)
    (hint : ∀ v : ThresholdHilbert, v ∈ L →
      Tendsto (fun i => inner ℝ v (F i)) atTop (𝓝 (inner ℝ v x))) :
    L.starProjection x = x := by
  apply projection_eq_of_internal_tests_and_exact_heads L F x
    (Eventually.of_forall hF) ?_ hint
  intro k hk
  filter_upwards [hH.eventually (eventually_ge_atTop k)] with i hi
  exact hhead i k hk hi


/-- An actual WeakDual limit for the same cofinal exact-head family suffices;
there is no separate boundedness premise. Existence of this limit is not asserted. -/
theorem projection_eq_of_weakStar_cofinal_exact_heads
    (F : ℕ → ThresholdHilbert) (x : ThresholdHilbert) (H : ℕ → ℕ)
    (hF : ∀ n, F n ∈ L) (hH : Tendsto H atTop atTop)
    (hhead : ∀ i k, 0 < k → k ≤ H i →
      hilbertSequence (F i) k = hilbertSequence x k)
    (ht : Tendsto (fun i => restrictedDual L (F i)) atTop (𝓝 (restrictedDual L x))) :
    L.starProjection x = x :=
  projection_eq_of_cofinal_exact_heads L F x H hF hH hhead
    (internal_tests_of_restricted_weakStar L F x ht)


/-- Explicit all-epsilon formulation of the projected-point convergence premise.
This does not assert the existence of the required eventual estimates. -/
theorem projection_eq_of_epsilon_projected_tests
    (F : I → ThresholdHilbert) (x : ThresholdHilbert)
    (hF : ∀ᶠ i in l, F i ∈ L)
    (hhead : ∀ k : ℕ, 0 < k → ∀ᶠ i in l,
      hilbertSequence (F i) k = hilbertSequence x k)
    (hint : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      |inner ℝ (L.starProjection (paretoPointHilbert n)) (F i - x)| < ε) :
    L.starProjection x = x := by
  apply projection_eq_of_eventually_exact_heads L F x hF hhead
  intro n
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  simpa only [Real.dist_eq, sub_zero] using hint n ε hε

end RiemannResearch.RH.ParetoProjectedHeadTests
