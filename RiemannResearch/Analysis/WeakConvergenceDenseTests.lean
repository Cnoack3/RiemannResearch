import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weak convergence from complete boundary coordinates

Source: `FourierBridgeUniformSignedEnergy20260910.md`, Section 11,
September 10, 2026. These are conditional topological assembly results:
the arithmetic coefficient limits and uniform norm bound remain hypotheses.
The conclusion tests every continuous linear functional, hence expresses
the full weak convergence assertion without introducing a substitute topology.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform boundedness extends convergence of pairings to the closure of a set. -/
theorem tendsto_inner_zero_of_mem_closure
    {l : Filter I} {u : I → E} {S : Set E} {C : ℝ}
    (hC : 0 ≤ C) (hbounded : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hconv : ∀ y ∈ S, Tendsto (fun i => inner ℝ y (u i)) l (𝓝 0))
    {x : E} (hx : x ∈ closure S) :
    Tendsto (fun i => inner ℝ x (u i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx
    (δ / (2 * (C + 1))) (by positivity)
  have hnear : ‖x - y‖ < δ / (2 * (C + 1)) := by
    simpa only [dist_eq_norm] using hxy
  have hmul : ‖x - y‖ * (2 * (C + 1)) < δ :=
    (lt_div_iff₀ (by positivity)).mp hnear
  have hevent := Metric.tendsto_nhds.mp (hconv y hy) (δ / 2) (by positivity)
  filter_upwards [hbounded, hevent] with i hi hiy
  have hsmall : ‖inner ℝ y (u i)‖ < δ / 2 := by
    simpa only [dist_zero_right] using hiy
  have hdiff : ‖inner ℝ (x - y) (u i)‖ < δ / 2 := by
    have hbound : ‖inner ℝ (x - y) (u i)‖ ≤ ‖x - y‖ * C :=
      (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hi (norm_nonneg _))
    nlinarith [norm_nonneg (x - y)]
  have heq : inner ℝ x (u i) = inner ℝ (x - y) (u i) + inner ℝ y (u i) := by
    rw [inner_sub_left]
    ring
  rw [dist_zero_right, heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

/-- Pairings with generators suffice once their linear span is dense at the test vector. -/
theorem tendsto_inner_zero_of_mem_closure_span
    {l : Filter I} {u : I → E} {S : Set E} {C : ℝ}
    (hC : 0 ≤ C) (hbounded : ∀ᶠ i in l, ‖u i‖ ≤ C)
    (hconv : ∀ y ∈ S, Tendsto (fun i => inner ℝ y (u i)) l (𝓝 0))
    {x : E} (hx : x ∈ (Submodule.span ℝ S).topologicalClosure) :
    Tendsto (fun i => inner ℝ x (u i)) l (𝓝 0) := by
  apply tendsto_inner_zero_of_mem_closure hC hbounded _ hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hconv y hy
  | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℝ)) l (𝓝 0))
  | add y z hy hz hty htz =>
      simpa only [inner_add_left, zero_add] using hty.add htz
  | smul c y hy hty =>
      simpa only [real_inner_smul_left, mul_zero] using hty.const_mul c

/-- In a real Hilbert space, convergence of all pairings is convergence
against every continuous linear functional, by the Frechet-Riesz theorem. -/
theorem tendsto_dual_zero_of_inner [CompleteSpace E]
    {l : Filter I} {u : I → E}
    (hconv : ∀ x : E, Tendsto (fun i => inner ℝ x (u i)) l (𝓝 0))
    (φ : E →L[ℝ] ℝ) : Tendsto (fun i => φ (u i)) l (𝓝 0) := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    hconv ((InnerProductSpace.toDual ℝ E).symm φ)

end RiemannResearch.Analysis
