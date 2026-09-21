import RiemannResearch.RH.ParetoReflectionConvergence

/-!
# Failed RH and the two exact reflection objectives

Source: user-provided stringent not-RH conditions, 2026-09-21, group 32.
The underlying reflection criterion is already proved on actual legal
packets. The alternative below preserves every legality, mean, period and
reflection hypothesis, and asserts failure of at least one convergence
condition rather than claiming each condition must fail individually.
-/

open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
open FinitePairVariance

theorem not_RH_reflection_objective_alternative
    (hRH : ¬ RiemannHypothesis)
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (Q : ℕ → ℕ) (F : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hlegal : ∀ n, F n ∈ legalSeedSpan A)
    (hmean : ∀ n, paretoMean (F n) = 1)
    (hQ : ∀ n, 0 < Q n) (heven : ∀ n, Even (Q n))
    (hp : ∀ n k, F n (k + Q n) = F n k)
    (href : ∀ n k, k < Q n → F n k + F n (Q n - 1 - k) = C n) :
    (¬ Tendsto (fun n => reflectionCalibration (Q n) (F n) 1) atTop (𝓝 0)) ∨
      ¬ Tendsto (fun n => uniformReflectionVariance (Q n) (F n) (C n) / Q n)
        atTop (𝓝 0) := by
  classical
  by_cases hJ : Tendsto (fun n => reflectionCalibration (Q n) (F n) 1) atTop (𝓝 0)
  · exact Or.inr (fun hU => hRH
      (riemannHypothesis_of_legal_reflection_split_tendsto
        A hA Q F C hlegal hmean hQ heven hp href hJ hU))
  · exact Or.inl hJ

end RiemannResearch.RH.Pareto
