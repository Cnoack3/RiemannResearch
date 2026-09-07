import RiemannResearch.RH.ParetoSmoothing
import RiemannResearch.NumberTheory.ArithmeticLogWeight

/-! Source: user-provided smoothing note §3.1. Exact quadratic taper specialization. -/
open scoped BigOperators
noncomputable section

namespace RiemannResearch.RH.Pareto

/-- The quadratic taper's exact arithmetic signal, with all mixed products. -/
theorem smoothingTheta_two (k : ℕ) :
    smoothingTheta 2 k = ∑ m ∈ Finset.Ioc 0 k,
      (ArithmeticFunction.vonMangoldt m * Real.log (m : ℝ) -
        (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) m) := by
  unfold smoothingTheta
  simp_rw [ArithmeticFunction.sum_moebius_mul_log_sq]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- The quadratic taper's complete head error. -/
theorem smoothingSeed_quadratic_head_error (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    1 - smoothingSeed N 2 k = (k : ℝ) * smoothingB N 2 -
      (∑ m ∈ Finset.Ioc 0 k,
        (ArithmeticFunction.vonMangoldt m * Real.log (m : ℝ) -
          (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) m)) /
            Real.log (N : ℝ) ^ 2 := by
  rw [smoothingSeed_head N 2 k hk hkN, smoothingTheta_two]
  ring

end RiemannResearch.RH.Pareto

end
