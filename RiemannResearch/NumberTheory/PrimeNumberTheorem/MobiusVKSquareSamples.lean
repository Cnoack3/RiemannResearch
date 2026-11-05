/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.VinogradovKorobovProfile
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapFinite

/-! A bound for the ordinary Mertens function at square integer cutoffs retains
its Vinogradov–Korobov coefficient on all real cutoffs. The cost of filling
a square gap is at most twice the square root of its right endpoint plus one. -/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

open RiemannResearch.Analysis

private theorem M_step_bound (m h : ℕ) :
    |M ((m + h : ℕ) : ℝ)| ≤ |M (m : ℝ)| + (h : ℝ) := by
  have hstep (k : ℕ) : M ((k+1 : ℕ) : ℝ) = M (k : ℝ) +
      (ArithmeticFunction.moebius (k+1) : ℝ) := by
    rw [M_nat_eq_sum_range, M_nat_eq_sum_range, Finset.sum_range_succ]
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show m + h.succ = (m+h)+1 by omega, hstep]
    have hmu : |(ArithmeticFunction.moebius ((m+h)+1) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (m+h)+1)
    exact (abs_add_le _ _).trans (by rw [Nat.cast_succ]; linarith)

private theorem vk_scale_eventually_mono (a : ℝ) (ha : 0 < a) :
    ∀ᶠ u : ℝ in atTop, ∀ v : ℝ, u ≤ v →
      Real.exp (-a * vkProfile u) * u ≤ Real.exp (-a * vkProfile v) * v := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    vkProfile_eventual_log_increment (1 / a) (by positivity)] with u hu h v huv
  have hv := hu.trans_le huv
  have hb := mul_le_mul_of_nonneg_left (h v huv) ha.le
  rw [← mul_assoc, show a * (1 / a) = 1 by field_simp, one_mul] at hb
  calc
    _ = Real.exp (-a * vkProfile u + Real.log u) := by rw [Real.exp_add, Real.exp_log hu]
    _ ≤ Real.exp (-a * vkProfile v + Real.log v) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log hv]

private theorem sqrt_le_vk_scale (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x ≤ Real.exp (-a * vkProfile x) * x := by
  obtain ⟨u, hu⟩ := (vkProfile_eventual_log_increment (1/(4*a)) (by positivity)).exists
  filter_upwards [eventually_ge_atTop u, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop
      (4*a*vkProfile u - Real.log u))] with x hux hx hlog
  have hb := mul_le_mul_of_nonneg_left (hu x hux) ha.le
  rw [← mul_assoc, show a * (1/(4*a)) = 1/4 by field_simp <;> ring] at hb
  calc
    Real.sqrt x = Real.exp (Real.log x * (1/2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    _ ≤ Real.exp (-a * vkProfile x + Real.log x) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log hx]

/-- Only square integer cutoffs are needed for an ordinary VK bound. -/
theorem mertens_vk_of_square_samples (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hM : ∀ᶠ k : ℕ in atTop, |M ((k : ℝ)^2)| ≤
      C * (Real.exp (-a * vkProfile ((k : ℝ)^2)) * (k : ℝ)^2)) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ ((C+3) * Real.exp (-a * vkProfile x)) * x := by
  let k (x : ℝ) : ℕ := ⌊Real.sqrt x⌋₊
  have hk : Tendsto k atTop atTop := tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop
  have hcast : Tendsto (fun x : ℝ => (k x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  have hk2 : Tendsto (fun x : ℝ => (k x : ℝ)^2) atTop atTop := by
    simpa only [pow_two] using hcast.atTop_mul_atTop₀ hcast
  filter_upwards [hk.eventually hM, hk2.eventually (vk_scale_eventually_mono a ha),
    sqrt_le_vk_scale a ha, eventually_ge_atTop (1 : ℝ)] with x hm hmono hdom hx
  have hx0 : 0 ≤ x := by linarith
  have hs := Real.sq_sqrt hx0
  have hlow : (k x : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hhigh : Real.sqrt x < (k x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsq : (k x : ℝ)^2 ≤ x := (pow_le_pow_left₀ (Nat.cast_nonneg _) hlow 2).trans hs.le
  have hkn : (k x)^2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hsq)
  have hnext := mul_self_lt_mul_self (Real.sqrt_nonneg x) hhigh
  have hgap : ((⌊x⌋₊ - (k x)^2 : ℕ) : ℝ) ≤ 2 * Real.sqrt x + 1 := by
    rw [Nat.cast_sub hkn, Nat.cast_pow]
    nlinarith only [hnext, hs, Nat.floor_le hx0, hlow]
  have hfill := M_step_bound ((k x)^2) (⌊x⌋₊ - (k x)^2)
  rw [Nat.add_sub_of_le hkn, Nat.cast_pow] at hfill
  have he : M x = M (⌊x⌋₊ : ℝ) := by simp [M]
  have hs1 : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have hmain := hm.trans (mul_le_mul_of_nonneg_left (hmono x hsq) hC)
  calc
    |M x| = |M (⌊x⌋₊ : ℝ)| := congrArg abs he
    _ ≤ _ := hfill
    _ ≤ C * (Real.exp (-a * vkProfile x) * x) + (2 * Real.sqrt x + 1) :=
      add_le_add hmain hgap
    _ ≤ C * (Real.exp (-a * vkProfile x) * x) +
        3 * (Real.exp (-a * vkProfile x) * x) := by linarith only [hdom, hs1]
    _ = _ := by ring

end RiemannResearch.NumberTheory.PrimeNumberTheorem
