/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.HingeKernelIntegral
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Locally finite arithmetic prime-power contribution

The von Mangoldt weighted hinge series is locally a finite sum and continuous.
Each double cell integral has an exact four-corner expression, including cells
that cross a prime-power threshold. Integrability for finite sums is proved.

Source: Suzuki, Aspects of the screw function corresponding to the Riemann
zeta-function (2023), equation (1.1), https://arxiv.org/abs/2206.03682,
supports the prime-power expression for g=-Psi. The elementary expression is
defined here; equality with a Weil distribution or zero sum is not asserted.
-/

namespace RiemannResearch.RH
open RiemannResearch.Analysis MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

def primePowerWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n

def primePowerHingeTerm (n : ℕ) (t : ℝ) : ℝ :=
  primePowerWeight n * hingeKernel (Real.log n) t

def screwPrimePart (t : ℝ) : ℝ := ∑' n : ℕ, primePowerHingeTerm n t

theorem primePowerWeight_nonneg (n : ℕ) : 0 ≤ primePowerWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem continuous_primePowerHingeTerm (n : ℕ) : Continuous (primePowerHingeTerm n) :=
  continuous_const.mul (continuous_hingeKernel _)

theorem primePowerHingeTerm_eq_zero_of_abs_le (n : ℕ) {t : ℝ}
    (ht : |t| ≤ Real.log n) : primePowerHingeTerm n t = 0 := by
  simp [primePowerHingeTerm, hingeKernel, max_eq_right (sub_nonpos.mpr ht)]

theorem screwPrimePart_eq_sum_of_bound {R t : ℝ} (ht : |t| ≤ R)
    (N : ℕ) (hN : Real.exp R < N) :
    screwPrimePart t = ∑ n ∈ Finset.range N, primePowerHingeTerm n t := by
  apply tsum_eq_sum
  intro n hn
  have hnN : N ≤ n := Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn)
  have hne : Real.exp R < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hnN)
  have hnp : 0 < (n : ℝ) := lt_trans (Real.exp_pos R) hne
  apply primePowerHingeTerm_eq_zero_of_abs_le
  exact ht.trans ((Real.le_log_iff_exp_le hnp).2 hne.le)

theorem summable_primePowerHingeTerm (t : ℝ) :
    Summable (fun n : ℕ => primePowerHingeTerm n t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp |t|)
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hnN : N ≤ n := Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn)
  have hne : Real.exp |t| < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hnN)
  exact primePowerHingeTerm_eq_zero_of_abs_le n
    ((Real.le_log_iff_exp_le (lt_trans (Real.exp_pos _) hne)).2 hne.le)

theorem continuous_screwPrimePart : Continuous screwPrimePart := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (|t|+1))
  have hc : Continuous (fun y => ∑ n ∈ Finset.range N, primePowerHingeTerm n y) :=
    continuous_finsetSum _ (fun n _ => continuous_primePowerHingeTerm n)
  apply hc.continuousAt.congr_of_eventuallyEq
  have he : ∀ᶠ y in 𝓝 t, |y| < |t|+1 :=
    continuous_abs.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (by linarith : |t| < |t|+1))
  filter_upwards [he] with y hy
  exact screwPrimePart_eq_sum_of_bound hy.le N hN

theorem screwPrimePart_neg (t : ℝ) : screwPrimePart (-t) = screwPrimePart t := by
  simp [screwPrimePart, primePowerHingeTerm, hingeKernel, abs_neg]

theorem screwPrimePart_zero : screwPrimePart 0 = 0 := by
  have hz (n : ℕ) : primePowerHingeTerm n 0 = 0 :=
    primePowerHingeTerm_eq_zero_of_abs_le n (by simpa using Real.log_natCast_nonneg n)
  simp [screwPrimePart, hz]

def primePowerHingeCell (n : ℕ) (b₁ d₁ b₂ d₂ : ℝ) : ℝ :=
  primePowerWeight n *
    (hingeKernelSecondPrimitive (Real.log n) (d₁-b₂)
    - hingeKernelSecondPrimitive (Real.log n) (b₁-b₂)
    - hingeKernelSecondPrimitive (Real.log n) (d₁-d₂)
    + hingeKernelSecondPrimitive (Real.log n) (b₁-d₂))

theorem integral_integral_primePowerHingeTerm (n : ℕ) (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂, primePowerHingeTerm n (x-y)) =
      primePowerHingeCell n b₁ d₁ b₂ d₂ := by
  simp_rw [primePowerHingeTerm, intervalIntegral.integral_const_mul]
  rw [integral_integral_hingeKernel (Real.log_natCast_nonneg n)]
  rfl

end
end RiemannResearch.RH


namespace RiemannResearch.RH
open MeasureTheory Set
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

theorem integral_integral_sum_primePowerHingeTerm (N : ℕ) (b₁ d₁ b₂ d₂ : ℝ) :
    (∫ x in b₁..d₁, ∫ y in b₂..d₂,
      ∑ n ∈ Finset.range N, primePowerHingeTerm n (x-y)) =
      ∑ n ∈ Finset.range N, primePowerHingeCell n b₁ d₁ b₂ d₂ := by
  have hi (x : ℝ) (n : ℕ) : IntervalIntegrable
      (fun y => primePowerHingeTerm n (x-y)) volume b₂ d₂ :=
    ((continuous_primePowerHingeTerm n).comp
      (continuous_const.sub continuous_id)).intervalIntegrable b₂ d₂
  have hj (n : ℕ) : Continuous (Function.uncurry
      (fun x y : ℝ => primePowerHingeTerm n (x-y))) :=
    (continuous_primePowerHingeTerm n).comp (continuous_fst.sub continuous_snd)
  have ho (n : ℕ) : IntervalIntegrable
      (fun x => ∫ y in b₂..d₂, primePowerHingeTerm n (x-y)) volume b₁ d₁ :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (hj n) b₂ d₂).intervalIntegrable b₁ d₁
  simp_rw [intervalIntegral.integral_finsetSum (fun n _ => hi _ n)]
  rw [intervalIntegral.integral_finsetSum (fun n _ => ho n)]
  simp_rw [integral_integral_primePowerHingeTerm]
end
end RiemannResearch.RH
