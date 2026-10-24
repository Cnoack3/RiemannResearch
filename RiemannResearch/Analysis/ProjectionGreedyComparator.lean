import RiemannResearch.Analysis.ProjectionCorrelationCompleteness
import RiemannResearch.Analysis.ProjectionInnovationSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Quantitative finite-comparator certificates for adaptive projection walks

Source: sixth Ramanujan transfer program, 24 October 2026. The precise weak
selection hypothesis compares every normalized atom correlation with the
actual orthogonal increment. No universal rate is inferred: the comparator
error and its complete coefficient budget remain in the bound.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ProjectionGreedyComparator
open ExhaustiveWalk ProjectionVariation ProjectionInnovationSeries ProjectionCorrelationCompleteness
variable {H ι β : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Full signed comparator identity; no positivity or legality is needed for the comparator. -/
theorem residual_comparator_exact [Fintype β] (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (x : H) (u : β → H) (a : β → ℝ) :
    ‖x - K.starProjection x‖ ^ 2 =
      inner ℝ (x - K.starProjection x) (x - ∑ i, a i • u i) +
        ∑ i, a i * inner ℝ (x - K.starProjection x) (u i) := by
  have ho := Submodule.starProjection_inner_eq_zero x (K.starProjection x)
    (K.starProjection_apply_mem x)
  have hs : inner ℝ (x - K.starProjection x) (x - K.starProjection x) =
      ‖x - K.starProjection x‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [inner_sub_right, ho, sub_zero] at hs
  simp only [inner_sub_right, inner_sum, real_inner_smul_right]
  linarith

/-- A finite comparator retains both its approximation error and every signed coefficient's cost. -/
theorem residual_comparator_bound [Fintype β] (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (x : H) (u : β → H) (a B : β → ℝ) (η : ℝ)
    (h : ∀ i, |inner ℝ (u i) (x - K.starProjection x)| ≤ B i * η) :
    ‖x - K.starProjection x‖ ^ 2 ≤
      ‖x - K.starProjection x‖ * ‖x - ∑ i, a i • u i‖ +
        (∑ i, |a i| * B i) * η := by
  have hi := real_inner_le_norm (x - K.starProjection x) (x - ∑ i, a i • u i)
  have ht : (∑ i, a i * inner ℝ (x - K.starProjection x) (u i)) ≤
      (∑ i, |a i| * B i) * η := by
    calc
      _ ≤ ∑ i, (|a i| * B i) * η := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ |a i * inner ℝ (x - K.starProjection x) (u i)| := le_abs_self _
          _ = |a i| * |inner ℝ (u i) (x - K.starProjection x)| := by
            rw [abs_mul, real_inner_comm]
          _ ≤ |a i| * (B i * η) := mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
          _ = _ := by ring
      _ = _ := (Finset.sum_mul ..).symm
  rw [residual_comparator_exact K x u a]
  exact add_le_add hi ht

/-- A precise weak greedy condition on the actual orthogonal gain, allowing repetitions. -/
def WeakGreedy (v : ι → H) (draw : ℕ → ι) (x : H) (τ : ℝ) : Prop :=
  0 < τ ∧ ∀ n i,
    τ * |inner ℝ (v i) (x - (walkSpan v draw n).starProjection x)| ≤
      ‖v i‖ * ‖increment v draw x n‖

theorem increment_norm_tendsto_zero (v : ι → H) (draw : ℕ → ι) (x : H) :
    Tendsto (fun n => ‖increment v draw x n‖) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (increment_energy_tendsto_zero v draw x)
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

/-- Atom-dependent eventual constants suffice; no uniform dictionary bound is required. -/
theorem correlations_of_eventual_gain_control (v : ι → H) (draw : ℕ → ι) (x : H)
    (h : ∀ i, ∃ C : ℝ, ∀ᶠ n in atTop,
      |inner ℝ (v i) (x - (walkSpan v draw n).starProjection x)| ≤
        C * ‖increment v draw x n‖) :
    CorrelationsVanish v draw x := by
  intro i
  obtain ⟨C, hC⟩ := h i
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have ht : Tendsto (fun n => C * ‖increment v draw x n‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hconst.mul (increment_norm_tendsto_zero v draw x)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) hC ht

theorem weakGreedy_correlation_bound (v : ι → H) (draw : ℕ → ι) (x : H)
    {τ : ℝ} (h : WeakGreedy v draw x τ) (n : ℕ) (i : ι) :
    |inner ℝ (v i) (x - (walkSpan v draw n).starProjection x)| ≤
      (‖v i‖ / τ) * ‖increment v draw x n‖ := by
  have hi : |inner ℝ (v i) (x - (walkSpan v draw n).starProjection x)| * τ ≤
      ‖v i‖ * ‖increment v draw x n‖ := by
    simpa only [mul_comm] using h.2 n i
  have hd := (le_div_iff₀ h.1).mpr hi
  calc
    _ ≤ (‖v i‖ * ‖increment v draw x n‖) / τ := hd
    _ = (‖v i‖ / τ) * ‖increment v draw x n‖ := by ring

theorem weakGreedy_complete (v : ι → H) (draw : ℕ → ι) (x : H)
    {τ : ℝ} (h : WeakGreedy v draw x τ) :
    visitedProjection v draw x = (ExhaustiveWalk.dictionaryClosure v).starProjection x := by
  apply (visited_eq_full_iff_correlations v draw x).mpr
  apply correlations_of_eventual_gain_control
  intro i
  exact ⟨‖v i‖ / τ, Eventually.of_forall (fun n => weakGreedy_correlation_bound v draw x h n i)⟩

/-- The quantitative conclusion keeps the comparator error and weighted l1 budget explicit. -/
theorem weakGreedy_comparator_bound [Fintype β]
    (v : ι → H) (draw : ℕ → ι) (x : H) {τ : ℝ} (h : WeakGreedy v draw x τ)
    (n : ℕ) (index : β → ι) (a : β → ℝ) :
    walkError v draw x n ≤
      ‖x - (walkSpan v draw n).starProjection x‖ * ‖x - ∑ i, a i • v (index i)‖ +
        (∑ i, |a i| * (‖v (index i)‖ / τ)) * ‖increment v draw x n‖ :=
  residual_comparator_bound (walkSpan v draw n) x (fun i => v (index i)) a
    (fun i => ‖v (index i)‖ / τ) _ (fun i => weakGreedy_correlation_bound v draw x h n (index i))

end RiemannResearch.Analysis.ProjectionGreedyComparator
