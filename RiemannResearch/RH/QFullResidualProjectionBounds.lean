import RiemannResearch.Analysis.ResidualLossBounds
import RiemannResearch.RH.QFullResidualCorrectionCost
import RiemannResearch.RH.QOptimizerParityRH
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Quantitative exhaustion from gains of the actual full-Q residual

Source: user-requested logarithmic residual-projection estimate, 14 November 2026.
The exact energy decrease is the projection of the actual old residual into
the actual later legal stage. Its lower bound is an explicit hypothesis.
The logarithmic consumer additionally states the indispensable divergence
condition on the chosen scales; an arbitrarily fast cofinal scale does not
automatically satisfy that condition. No arithmetic gain provider is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QFullResidualCorrectionCost
open ZetaTwoHilbert QFullResidueProjection
open RiemannResearch.Analysis.ResidualGain

theorem projected_residual_energy_eq_difference (N M : ℕ) (hNM : N ≤ M) :
    ‖(stage M).starProjection (residual N)‖ ^ 2 =
      ‖residual N‖ ^ 2 - ‖residual M‖ ^ 2 := by
  rw [projected_residual N M hNM]
  linarith only [residual_energy_completion N M hNM]

/-- Any sequence of actual legal fits with vanishing error suffices; cofinality
is unnecessary once vanishing has been supplied. -/
theorem riemannHypothesis_of_residual_energy_tendsto_zero (N : ℕ → ℕ)
    (h : Tendsto (fun j => ‖residual (N j)‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hn : Tendsto (fun j => ‖residual (N j)‖) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hs
  have hp : Tendsto (fun j => candidate (N j)) atTop (𝓝 qOne) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [residual, norm_sub_rev] using hn
  apply riemannHypothesis_of_qOne_mem_full_closure
  exact legalSpan.isClosed_topologicalClosure.mem_of_tendsto hp
    (Filter.Eventually.of_forall (fun j =>
      legalSpan.le_topologicalClosure (candidate_mem_legalSpan (N j))))

/-- Finite exponential bound on the actual error, conditional only on the stated
lower projection gains. The scalar accounting theorem retains the exact slack. -/
theorem residual_energy_le_exp_neg_projection_loss
    (N : ℕ → ℕ) (hN : Monotone N) (a : ℕ → ℝ)
    (hgain : ∀ j, a j * ‖residual (N j)‖ ^ 2 ≤
      ‖(stage (N (j + 1))).starProjection (residual (N j))‖ ^ 2) (n : ℕ) :
    ‖residual (N n)‖ ^ 2 ≤
      ‖residual (N 0)‖ ^ 2 * Real.exp (-(∑ j ∈ Finset.range n, a j)) := by
  apply residual_le_exp_neg_cumulative_loss (fun j => sq_nonneg _) _ n
  intro j
  simpa only [projected_residual_energy_eq_difference _ _ (hN (Nat.le_succ j))]
    using hgain j

/-- Conditional RH criterion with eventual gains, allowing finite termination. -/
theorem riemannHypothesis_of_eventual_nonsummable_projection_gain
    (N : ℕ → ℕ) (hN : Monotone N) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hdiv : ¬Summable a)
    (hgain : ∀ᶠ j in atTop, a j * ‖residual (N j)‖ ^ 2 ≤
      ‖(stage (N (j + 1))).starProjection (residual (N j))‖ ^ 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_residual_energy_tendsto_zero N
  apply tendsto_zero_of_eventually_not_summable_loss (fun j => sq_nonneg _) ha _ hdiv
  exact hgain.mono (fun j hj => by
    simpa only [projected_residual_energy_eq_difference _ _ (hN (Nat.le_succ j))]
      using hj)

/-- The logarithmic projection bound implies RH when the reciprocal logarithmic
losses are nonsummable. Both the actual gain and scale condition are explicit. -/
theorem riemannHypothesis_of_logarithmic_projection_gain
    (N : ℕ → ℕ) (hN : Monotone N) (L : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C) (hL : ∀ j, 1 < L j)
    (hdiv : ¬Summable (fun j => 1 / (C * Real.log (L j))))
    (hgain : ∀ᶠ j in atTop, ‖residual (N j)‖ ^ 2 / (C * Real.log (L j)) ≤
      ‖(stage (N (j + 1))).starProjection (residual (N j))‖ ^ 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eventual_nonsummable_projection_gain N hN
    (fun j => 1 / (C * Real.log (L j)))
    (fun j => (one_div_pos.mpr (mul_pos hC (Real.log_pos (hL j)))).le) hdiv
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hgain

/-- If RH is false, every nonsummable proposed logarithmic schedule must fail
at arbitrarily late stages of these actual projections. -/
theorem frequently_logarithmic_projection_bound_fails_of_not_RH
    (N : ℕ → ℕ) (hN : Monotone N) (L : ℕ → ℝ) (C : ℝ)
    (hC : 0 < C) (hL : ∀ j, 1 < L j)
    (hdiv : ¬Summable (fun j => 1 / (C * Real.log (L j))))
    (hRH : ¬RiemannHypothesis) :
    ∃ᶠ j in atTop, ‖(stage (N (j + 1))).starProjection (residual (N j))‖ ^ 2 <
      ‖residual (N j)‖ ^ 2 / (C * Real.log (L j)) := by
  by_contra h
  apply hRH (riemannHypothesis_of_logarithmic_projection_gain N hN L C hC hL hdiv ?_)
  simpa only [Filter.Frequently, not_not, not_lt] using h

end RiemannResearch.RH.QFullResidualCorrectionCost
