/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy
import RiemannResearch.Analysis.MontgomeryPrimeProbe
import RiemannResearch.Probability.DPPIntervalSpectrum

/-! # The empirical law of literal consecutive-prime frequency steps

The two logarithms used to encode neighboring zeta-ordinate gaps in Compact
Orbit, “Three consecutive primes, neighboring zero gaps and Parseval”, can
also be read literally along the ordered primes. Under that sampling their
joint unscaled empirical law is a point mass at the origin. The input is the
repository's prime number theorem for the nth prime. This tests the numeric
prime ratios; the torus-angle law uses a different sampling variable.
https://riemann-compact-orbit.dreamymeter1.chatgpt.site/current-proofs.html#three-prime-gap-tests
-/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RiemannResearch.Analysis.PrimeOrbitPairLawDistinction
open RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem successivePrimeRatio_tendsto_one :
    Tendsto (fun n : ℕ => (nth_prime (n+1) : ℝ) / nth_prime n) atTop (𝓝 1) := by
  have hn : (fun n : ℕ => (n : ℝ) + 1) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
    apply IsEquivalent.add_isLittleO (by rfl)
    exact (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop
  have hlog := hn.log tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hpn :
      (fun n : ℕ => (nth_prime (n+1) : ℝ)) ~[atTop] (fun n : ℕ => (nth_prime n : ℝ)) := by
    apply (nth_prime_asymp.comp_tendsto hshift).trans
    apply IsEquivalent.trans _ nth_prime_asymp.symm
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, Pi.mul_def] using hn.mul hlog
  apply (isEquivalent_iff_tendsto_one _).mp hpn
  exact Eventually.of_forall fun n => by exact_mod_cast (Nat.prime_nth_prime n).ne_zero

/-- Successive literal prime log-ratios. The chronology here indexes primes. -/
def primeLogStep (n : ℕ) : ℝ := Real.log ((nth_prime (n+1) : ℝ) / nth_prime n)

theorem consecutivePrimeLogSteps_tendsto :
    Tendsto (fun n => (primeLogStep n, primeLogStep (n+1))) atTop (𝓝 (0,0)) := by
  have hs : Tendsto primeLogStep atTop (𝓝 0) := by
    change Tendsto (Real.log ∘ fun n : ℕ => (nth_prime (n+1) : ℝ) / nth_prime n) atTop (𝓝 0)
    simpa only [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
        successivePrimeRatio_tendsto_one
  exact hs.prodMk_nhds (hs.comp (tendsto_add_atTop_nat 1))

/-- The joint empirical prime-step averages converge to evaluation at (0,0).
Every bounded continuous weak-convergence test is covered. -/
theorem empiricalConsecutivePrimeLogSteps_tendsto (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun N : ℕ => (N⁻¹ : ℝ) * ∑ n ∈ Finset.range N,
      f (primeLogStep n, primeLogStep (n+1))) atTop (𝓝 (f (0,0))) :=
  ((hf.tendsto _).comp consecutivePrimeLogSteps_tendsto).cesaro

open MontgomeryPrimeTrace MontgomeryFormFactor ZeroOrdinate MeasureTheory
open RiemannResearch.DPPSpectral
open scoped FourierTransform

/-- Fourier transform of the unnormalized product of the two prime-power
logarithmic measures, pushed forward by taking their signed difference. -/
def primeLogPairTransform (T u : ℝ) : ℂ :=
  let s := Finset.Ioc 0 ⌊T⌋₊
  let w := fun n : s => ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T
  let f := fun n : s => 2 * Real.pi * Real.log n / Real.log T
  ∑ n : s, ∑ m : s, ((w n * w m : ℝ) : ℂ) * phase (f n - f m) u

theorem primeLogPairTransform_eq_probe_sq (T u : ℝ) :
    primeLogPairTransform T u = ((‖primeFourierProbe T u‖ ^ 2 : ℝ) : ℂ) := by
  let s := Finset.Ioc 0 ⌊T⌋₊
  let w := fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T
  let f := fun n : ℕ => 2 * Real.pi * Real.log n / Real.log T
  have hprobe : primeFourierProbe T u = probeKernel (fun n : s => f n) (fun n => w n) u := by
    rw [probeKernel, Finset.sum_coe_sort s (fun n : ℕ => (w n : ℂ) * phase (f n) u)]
    unfold primeFourierProbe
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    unfold phase
    congr 1
    dsimp only [f]
    push_cast
    ring
  rw [hprobe]
  exact (probe_energy_expansion (fun n : s => f n) (fun n => w n) u).symm

private theorem primeProbe_tendsto (u : ℝ) :
    Tendsto (fun T => primeFourierProbe T u) atTop (𝓝 (primeContinuumProbe u)) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  have he := (Real.tendsto_log_atTop.const_div_atTop (Real.log 4 + 4)).mul_const
    (1 + 2 * Real.pi * |u|)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa only [zero_mul] using he)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact primeFourierProbe_error hT u

theorem primeLogPairTransform_tendsto_sinc_sq (u : ℝ) :
    Tendsto (fun T => primeLogPairTransform T u) atTop (𝓝 ((Real.sinc (Real.pi*u)^2 : ℝ) : ℂ)) := by
  simpa only [Function.comp_def, primeLogPairTransform_eq_probe_sq, norm_primeContinuumProbe_eq,
    sq_abs] using
    (Complex.continuous_ofReal.tendsto _).comp ((primeProbe_tendsto u).norm.pow 2)

/-- Dividing by the product mass gives the characteristic function of the
normalized pair measure. It tends to the Fourier transform of the triangular
probability density. Here the physical difference is in [-1,1]. -/
theorem normalizedPrimeLogPairTransform_tendsto_tent (u : ℝ) :
    Tendsto (fun T => primeLogPairTransform T u / primeLogPairTransform T 0) atTop
      (𝓝 (𝓕 (fun x : ℝ => ((max (1 - |x|) 0 : ℝ) : ℂ)) (-u))) := by
  have h0 : Tendsto (fun T => primeLogPairTransform T 0) atTop (𝓝 1) := by
    simpa using primeLogPairTransform_tendsto_sinc_sq 0
  have ht := (primeLogPairTransform_tendsto_sinc_sq u).div h0 (by norm_num)
  rw [div_one] at ht
  have he := fourier_overlap (intervalMultiplier 0) (intervalMultiplier_integrable 0) (-u)
  simp only [intervalMultiplier_overlap, fourier_intervalMultiplier] at he
  rw [interval_fourier_phase, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at he
  rw [he]
  exact ht

end RiemannResearch.Analysis.PrimeOrbitPairLawDistinction
