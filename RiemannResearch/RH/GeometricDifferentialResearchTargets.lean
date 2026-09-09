import RiemannResearch.RH.ParetoGeometricTransform
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Differential variance and Meixner expansion proof targets

Source: analytic_gibbs_method.md and the contracting-evolution research report.
The exact total-variance identities are already proved in ParetoGeometricTransform.
The derivative and complete orthogonal expansion below remain proof obligations.
They are definitions of propositions, not axioms or claimed theorems.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open scoped BigOperators

def geometricVariance (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, geometricProbability n t * (f n - geometricTransform f t)^2

/-- Actual centered geometric covariance, including convergence of its series
and its identification with the derivative. This is a proof target only. -/
def GeometricCovarianceDerivativeTarget : Prop :=
  ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) → ∀ t : ℝ, 0 < t → t < 1 →
    Summable (fun n => geometricProbability n t * (f n - geometricTransform f t) *
      ((n : ℝ) - t / (1-t))) ∧
    deriv (geometricTransform f) t =
      (∑' n, geometricProbability n t * (f n - geometricTransform f t) *
        ((n : ℝ) - t / (1-t))) / t

def geometricRegressionResidual (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, geometricProbability n t *
    (f n - geometricTransform f t - (1-t)^2 * deriv (geometricTransform f) t *
      ((n : ℝ) - t / (1-t)))^2

def GeometricDifferentialVarianceTarget : Prop :=
  ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) → ∀ t : ℝ, 0 < t → t < 1 →
    geometricVariance f t = t * (1-t)^2 * (deriv (geometricTransform f) t)^2 +
      geometricRegressionResidual f t

def geometricHigherDerivative (r : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  ((fun g : ℝ → ℝ => deriv g)^[r]) f

def geometricMeixnerCoefficient (r : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 r, (-1 : ℝ)^j * (Nat.choose (r-1) (j-1) : ℝ) *
    (1-t)^j * geometricHigherDerivative j f t / (Nat.factorial j : ℝ)

def GeometricMeixnerParsevalTarget : Prop :=
  ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ n, |f n| ≤ C) → ∀ t : ℝ, 0 < t → t < 1 →
    HasSum (fun r : ℕ => t^(r+1) *
      (geometricMeixnerCoefficient (r+1) (geometricTransform f) t)^2)
      (geometricVariance f t)

end
end RiemannResearch.RH.Pareto
