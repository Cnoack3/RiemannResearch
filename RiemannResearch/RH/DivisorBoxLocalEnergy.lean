/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.FiniteDilationMobiusKernel

/-!
# Exact normalized local energy for divisor-box certificates

The finite geometric identity used by the all-dilation continuation is valid
as a polynomial identity, without any primality or nonvanishing assumption.
The specialization to a prime square is the local arithmetic summation step;
the global Euler product and the physical certificate identification are not
claimed by these declarations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

/-- The numerator identity for a divisor-box local factor. -/
theorem divisorBox_local_energy_numerator (q : ℝ) (L : ℕ) :
    q + (q - 1) ^ 2 * (∑ j ∈ Finset.range L, q ^ j) + q ^ L =
      q ^ (L + 1) + 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Finset.sum_range_succ, pow_succ] at *
    linear_combination ih

/-- The local factor after dividing by its natural prime-power scale. -/
theorem divisorBox_local_energy_normalized (q : ℝ) (hq : q ≠ 0) (L : ℕ) :
    (q + (q - 1) ^ 2 * (∑ j ∈ Finset.range L, q ^ j) + q ^ L) /
        q ^ (L + 1) = 1 + 1 / q ^ (L + 1) := by
  rw [divisorBox_local_energy_numerator, add_div,
    div_self (pow_ne_zero _ hq)]

/-- Inverse-square coordinates give the same exact local factor polynomially. -/
theorem divisorBox_local_energy_inverse (x : ℝ) (L : ℕ) :
    x ^ L + (1 - x) ^ 2 * (∑ j ∈ Finset.range L, x ^ j) + x =
      1 + x ^ (L + 1) := by
  have h := divisorBox_local_energy_numerator x L
  nlinarith [h]

/-- The actual prime-square specialization, with the exponent retained exactly. -/
theorem divisorBox_prime_local_energy (p : ℕ) (hp : p.Prime) (L : ℕ) :
    ((p : ℝ) ^ 2 + ((p : ℝ) ^ 2 - 1) ^ 2 *
        (∑ j ∈ Finset.range L, ((p : ℝ) ^ 2) ^ j) + ((p : ℝ) ^ 2) ^ L) /
        ((p : ℝ) ^ 2) ^ (L + 1) =
      1 + 1 / (p : ℝ) ^ (2 * (L + 1)) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simpa only [pow_mul] using
    divisorBox_local_energy_normalized ((p : ℝ) ^ 2) (pow_ne_zero _ hpR) L

end RiemannResearch.RH.Pareto
