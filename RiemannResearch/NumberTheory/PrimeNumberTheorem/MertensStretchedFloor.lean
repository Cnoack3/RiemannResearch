/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensSumVK
import RiemannResearch.Analysis.StretchedLogProductIncrement
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensStretchedDecay

/-!
# Integer and real cutoffs for stretched Mertens bounds

Source: the user-provided Mertens displacement archive.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.Analysis

/-- For `0 ≤ β < 1/2`, including `β=1/11`, floor interpolation in the
stretched logarithmic-product Mertens estimate preserves *both* constants
for eventual bounds. -/
theorem M_stretched_loglog_eventually_nat_iff_real (β a C : ℝ)
    (hβ : 0 ≤ β) (hβ2 : 2 * β < 1) (ha : 0 ≤ a) (hC : 0 ≤ C) :
    (∀ᶠ N : ℕ in atTop, |M (N : ℝ)| ≤ C * (N : ℝ) * Real.exp
      (-a * logProductPower β (6 + Real.log (N : ℝ)))) ↔
      (∀ᶠ x : ℝ in atTop, |M x| ≤ C * x * Real.exp
        (-a * logProductPower β (6 + Real.log x))) := by
  exact floor_exponential_bound_eventually_iff M
    (fun x => logProductPower β (6 + Real.log x)) a C hC (fun x => by simp [M])
    (shifted_logProductPower_eventual_log_increment β a hβ hβ2 ha)

theorem M_stretched_loglog_eventually_of_tail_bound
    (d B : ℝ) (hd : 0 < d) (hB : 0 ≤ B)
    (hTail : ∀ T : ℝ, 0 ≤ T → mertensTailEnvelope T ≤ B * Real.exp
      (-d * ((6 + T) * Real.log (6 + T)) ^ ((1 : ℝ) / 11))) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ B * x * Real.exp
      (-d * ((6 + Real.log x) * Real.log (6 + Real.log x)) ^ ((1 : ℝ) / 11)) := by
  apply (M_stretched_loglog_eventually_nat_iff_real (1/11 : ℝ) d B
    (by norm_num) (by norm_num) hd.le hB).1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hE := mertensTailEnvelope_nat_bound (Real.log (N : ℝ)) N
    (by rw [Real.exp_log hN0])
  have hm := (div_le_iff₀ hN0).mp (hE.trans (hTail _ (Real.log_nonneg hN1)))
  simpa only [RiemannResearch.Analysis.logProductPower, mul_assoc, mul_left_comm, mul_comm] using hm

end RiemannResearch.NumberTheory.PrimeNumberTheorem
