/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.ParetoResidueDuality

/-!
# Continuous Möbius-difference functionals on the Pareto Hilbert space

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Sections 4 and 5. These functionals are finite sums of continuous physical
coordinate evaluations, independent of the balanced arithmetic dictionary.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators

noncomputable section

def anchoredEvaluationCLM (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  match n with
  | 0 => 0
  | k + 1 => physicalEvaluationCLM k

@[simp] theorem anchoredEvaluationCLM_apply (n : ℕ) (f : ThresholdHilbert) :
    anchoredEvaluationCLM n f = hilbertSequence f n := by
  cases n <;> simp [anchoredEvaluationCLM]

def mobiusDifferenceCLM (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) •
    (anchoredEvaluationCLM d - anchoredEvaluationCLM (d - 1))

@[simp] theorem mobiusDifferenceCLM_apply (n : ℕ) (f : ThresholdHilbert) :
    mobiusDifferenceCLM n f = mobiusDifference n (hilbertSequence f) := by
  simp [mobiusDifferenceCLM, mobiusDifference, smul_eq_mul]

end
end RiemannResearch.RH.Pareto
