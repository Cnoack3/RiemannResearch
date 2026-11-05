/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MertensEntropyOptimum
import RiemannResearch.RH.QMobiusStretchedEnergy

/-!
# Complete Möbius-head energy from an exponential Mertens bound

Source: the finite-energy argument in the user-supplied Mertens displacement
archive. The first estimate keeps the original rate and its linear prefactor.
The second uses the optimal scalar multiplicative constant for a lower rate.
-/
noncomputable section

namespace RiemannResearch.RH.QMobiusMertensProfileEnergy
open ZetaTwoHilbert ZetaTwoProbability QMobiusStretchedEnergy RiemannResearch.Analysis
open RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem exactHead_energy_of_exponential_mertens_same_rate
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 6 ≤ t)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ Real.exp (-t) * y) :
    ‖QMobiusExactHead.exactHead N‖ ^ 2 ≤ 6 / zetaTwo +
      (520 / zetaTwo) * (N : ℝ) * (Real.exp (-t) * (1+t)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he := exactHead_energy_of_uniform_mertens_log N hN (Real.exp (-t))
    (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith))
    (exponential_entropy_small t ht) hM
  have hh := (div_le_iff₀ hn).mp he
  rw [exponential_entropy_eq] at hh
  apply hh.trans_eq
  field_simp [zetaTwo_pos.ne', hn.ne']
  ring

theorem exactHead_energy_of_exponential_mertens
    (N : ℕ) (hN : 0 < N) (b c u : ℝ) (hb : 0 < b) (hcb : c < b)
    (hlarge : 6 ≤ b * u)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ Real.exp (-(b*u)) * y) :
    ‖QMobiusExactHead.exactHead N‖ ^ 2 ≤ 6 / zetaTwo +
      ((520 / zetaTwo) * (N : ℝ)) *
        (((b/(b-c))*Real.exp (-(c/b))) * Real.exp (-c*u)) := by
  apply (exactHead_energy_of_exponential_mertens_same_rate N hN (b*u) hlarge hM).trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (div_nonneg (by norm_num) zetaTwo_pos.le) (Nat.cast_nonneg N))
  have h := exponential_entropy_le_optimal_rate b c u hb hcb
  rw [neg_mul, exponential_entropy_eq] at h
  exact h

end RiemannResearch.RH.QMobiusMertensProfileEnergy
