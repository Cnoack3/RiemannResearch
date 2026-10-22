import RiemannResearch.Analysis.WeakConvergenceDenseTests
import RiemannResearch.Analysis.WeakConvexRepair
import Mathlib.Analysis.Convex.Combination

/-!
# Bounded progressively matched moments give finite convex repair

Source: user-provided Ramanujan–Laguerre discussion of September 11, 2026.
The proof uses the standard dense-test weak convergence argument and Mazur's
convex closure theorem. The tests here are explicitly assumed to have dense
linear span. No actual Laguerre realization or arithmetic norm bound is
asserted. This formulation also applies to projected continuous tests, which
need not be an orthogonal basis of the discrete Pareto Hilbert space.
-/

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Uniformly bounded errors whose first `n + 1` moments vanish are weakly
null, provided the fixed testing family has dense linear span. -/
theorem weak_tendsto_zero_of_bounded_matched_moments
    (b : ℕ → E)
    (htotal : (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤)
    (u : ℕ → E) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, ‖u n‖ ^ 2 ≤ B)
    (hmatch : ∀ n k, k ≤ n → inner ℝ (b k) (u n) = 0) :
    Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop (𝓝 0) := by
  have hcoord (k : ℕ) :
      Tendsto (fun n => inner ℝ (b k) (u n)) atTop (𝓝 0) := by
    have he : (fun n => inner ℝ (b k) (u n)) =ᶠ[atTop]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop k] with n hn
      exact hmatch n k hn
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  apply weak_tendsto_zero_of_inner_tendsto
  intro x
  apply tendsto_inner_zero_of_mem_closure_span (S := Set.range b)
    (show 0 ≤ B + 1 by linarith)
    (Filter.Eventually.of_forall (fun n => show ‖u n‖ ≤ B + 1 by
      nlinarith [hbound n, norm_nonneg (u n), sq_nonneg (‖u n‖ - 1)]))
  · rintro y ⟨k, rfl⟩
    exact hcoord k
  · rw [htotal]
    trivial

/-- The repair uses finitely many original errors from any prescribed tail,
with nonnegative weights summing to one. Mixed terms remain in the full norm. -/
theorem exists_convex_weights_small_of_bounded_matched_moments
    (b : ℕ → E)
    (htotal : (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤)
    (u : ℕ → E) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, ‖u n‖ ^ 2 ≤ B)
    (hmatch : ∀ n k, k ≤ n → inner ℝ (b k) (u n) = 0)
    (N : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → ℝ) (j : κ → ℕ),
      (∀ k, 0 ≤ a k) ∧ (∑ k, a k) = 1 ∧
      (∀ k, N ≤ j k) ∧ ‖∑ k, a k • u (j k)‖ < η := by
  classical
  have hw := weak_tendsto_zero_of_bounded_matched_moments b htotal u hB hbound hmatch
  obtain ⟨v, hv, hvnorm⟩ :=
    exists_norm_lt_mem_convexHull_image_of_weak_tendsto
      hw (show Set.Ici N ∈ (atTop : Filter ℕ) from eventually_ge_atTop N) hη
  obtain ⟨κ, hκ, a, z, ha, haone, hz, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hv
  let := hκ
  choose j hj hzj using hz
  refine ⟨κ, hκ, a, j, ha, haone, hj, ?_⟩
  have he : (∑ k, a k • u (j k)) = v := by
    simpa only [hzj] using hsum
  rwa [he]

end RiemannResearch.Analysis
