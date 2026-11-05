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


/-- At exponents admitted by the stretched Mertens bootstrap, converting
integer cutoffs to real cutoffs preserves the exponent and the prefactor. -/
theorem M_stretched_loglog_real_of_nat_preserve (β c B : ℝ)
    (hβ : 0 ≤ β) (hβ₂ : 2 * β ≤ 1) (hc : c ≤ 1) (hB : 0 ≤ B)
    (hNat : ∀ N : ℕ, 1 ≤ N → |M (N : ℝ)| ≤ B * N *
      Real.exp (-c * logProductPower β (6 + Real.log (N : ℝ)))) :
    ∀ x : ℝ, 1 ≤ x → |M x| ≤ B * x *
      Real.exp (-c * logProductPower β (6 + Real.log x)) := by
  intro x hx
  let N : ℕ := ⌊x⌋₊
  have hN : 1 ≤ N := by simpa [N] using Nat.floor_mono hx
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx0 : 0 < x := by linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  let s := 6 + Real.log (N : ℝ)
  let t := 6 + Real.log x
  have hs : 6 ≤ s := by dsimp [s]; linarith [Real.log_nonneg hNr]
  have hs0 : 0 < s := by linarith
  have hst : s ≤ t := by dsimp [s,t]; linarith [Real.log_le_log hN0 hNx]
  have ht0 := hs0.trans_le hst
  have hps : logProductPower β s ≤ s := by
    calc
      _ ≤ s ^ (2 * β) := logProductPower_upper β hβ hs
      _ ≤ s ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ₂
      _ = s := Real.rpow_one _
  have hr := (div_le_div_iff₀ ht0 hs0).mp (logProductPower_div_antitone β hβ hβ₂ hs hst)
  have hinc : logProductPower β t - logProductPower β s ≤ t - s := by
    apply (mul_le_mul_iff_of_pos_right hs0).mp
    nlinarith only [hr, mul_le_mul_of_nonneg_right hps (sub_nonneg.mpr hst)]
  have hnonneg := sub_nonneg.mpr (logProductPower_mono β hβ (by linarith : 1 ≤ s) hst)
  have hcinc := (mul_le_of_le_one_left hnonneg hc).trans hinc
  have hcomp : (N : ℝ) * Real.exp (-c * logProductPower β s) ≤
      x * Real.exp (-c * logProductPower β t) := by
    calc
      _ = Real.exp (Real.log (N : ℝ) + (-c * logProductPower β s)) := by
        rw [Real.exp_add, Real.exp_log hN0]
      _ ≤ Real.exp (Real.log x + (-c * logProductPower β t)) := by
        apply Real.exp_le_exp.mpr
        change c * (logProductPower β t - logProductPower β s) ≤
            (6 + Real.log x) - (6 + Real.log (N : ℝ)) at hcinc
        linarith only [hcinc]
      _ = _ := by rw [Real.exp_add, Real.exp_log hx0]
  have he : M x = M (N : ℝ) := by simp [N, M]
  rw [he]
  calc
    |M (N : ℝ)| ≤ B * N * Real.exp (-c * logProductPower β s) := hNat N hN
    _ ≤ B * x * Real.exp (-c * logProductPower β t) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcomp hB


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
