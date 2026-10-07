/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DigammaBernoulliSignedRemainder

/-!
# Cancellation-preserving Bernoulli bounds for actual digamma differences

The complete signed endpoint-defect series is subtracted before estimating.
The exact common Bernoulli factor and inverse-power kernel difference remain
inside each actual interval integral. Strict positivity and the next-order
identity give a sharp bound by the difference of first-omitted powers.

Source: the user's request to salvage the interrupted Mellin/zeta/digamma
formalization. The proof extends the verified endpoint-defect method in
`DigammaBernoulliSignedRemainder`; its Fourier input is the actual Bernoulli
series documented at https://dlmf.nist.gov/24.8.E1 (proof strategy).
-/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators Topology

namespace RiemannResearch.RH.DigammaBernoulliDifferences

open RiemannResearch.Analysis
open RiemannResearch.RH.DigammaBernoulliCells
open RiemannResearch.RH.DigammaBernoulliRemainderEstimates
open RiemannResearch.RH.DigammaBernoulliSignedRemainder

/-- Integrability of the literal endpoint-defect cell integrand. -/
theorem endpointDefectCell_integrand_intervalIntegrable {x : ℝ}
    (hx : 0 < x) (N : ℕ) :
    IntervalIntegrable (fun u : ℝ =>
      (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) *
        ((x + u)⁻¹) ^ (2 * N + 3)) volume 0 1 :=
  (((continuous_bernoulliFun (2 * N + 2)).continuousOn.sub continuousOn_const).mul
    ((continuousOn_inverse_shift hx).pow (2 * N + 3))).intervalIntegrable

/-- The actual difference retains its common Bernoulli factor and kernel
cancellation inside one integral. -/
theorem endpointDefectCell_sub_eq_integral {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (N : ℕ) :
    endpointDefectCell N x - endpointDefectCell N y =
      ∫ u in (0 : ℝ)..1,
        (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) *
          (((x + u)⁻¹) ^ (2 * N + 3) - ((y + u)⁻¹) ^ (2 * N + 3)) := by
  unfold endpointDefectCell
  rw [← intervalIntegral.integral_sub
    (endpointDefectCell_integrand_intervalIntegrable hx N)
    (endpointDefectCell_integrand_intervalIntegrable hy N)]
  congr 1
  funext u
  ring

/-- Every positive inverse-power kernel strictly decreases with the positive
base argument, even after a nonnegative cell shift. -/
private theorem inverse_power_kernel_sub_pos {x y u : ℝ}
    (hx : 0 < x) (hxy : x < y) (hu : 0 ≤ u)
    (k : ℕ) (hk : 0 < k) :
    0 < ((x + u)⁻¹) ^ k - ((y + u)⁻¹) ^ k := by
  have hxu : 0 < x + u := by linarith
  have hyu : 0 < y + u := by linarith
  have hxyu : x + u < y + u := by linarith
  have hinv : (y + u)⁻¹ < (x + u)⁻¹ :=
    (inv_lt_inv₀ hyu hxu).mpr hxyu
  have hpow : ((y + u)⁻¹) ^ k < ((x + u)⁻¹) ^ k :=
    pow_lt_pow_left₀ hinv (inv_nonneg.mpr hyu.le) (ne_of_gt hk)
  exact sub_pos.mpr hpow

/-- Strict signed monotonicity of the actual finite endpoint-defect cell. -/
theorem endpointDefectCell_signed_sub_pos {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (endpointDefectCell N x - endpointDefectCell N y) := by
  have hy : 0 < y := lt_trans hx hxy
  let f : ℝ → ℝ := fun u => (-1 : ℝ) ^ (N + 1) *
    ((bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) *
      (((x + u)⁻¹) ^ (2 * N + 3) - ((y + u)⁻¹) ^ (2 * N + 3)))
  have hdegree : 2 * (N + 1) = 2 * N + 2 := by omega
  have hsignEq (u : ℝ) : (-1 : ℝ) ^ (N + 1) *
      (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) =
      (-1 : ℝ) ^ ((N + 1) + 1) *
        (bernoulliFun (2 * N + 2) 0 - bernoulliFun (2 * N + 2) u) := by
    rw [pow_succ (-1 : ℝ) (N + 1)]
    ring
  have hcontX : ContinuousOn (fun u : ℝ => (x + u)⁻¹) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      continuousOn_inverse_shift hx
  have hcontY : ContinuousOn (fun u : ℝ => (y + u)⁻¹) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      continuousOn_inverse_shift hy
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (((continuous_bernoulliFun (2 * N + 2)).continuousOn.sub continuousOn_const).mul
      ((hcontX.pow (2 * N + 3)).sub (hcontY.pow (2 * N + 3)))).const_mul
        ((-1 : ℝ) ^ (N + 1))
  have hnonneg (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) : 0 ≤ f u := by
    have hdef := bernoulli_even_endpoint_defect_nonneg (N + 1) (by omega)
      (show u ∈ Icc (0 : ℝ) 1 from ⟨hu.1.le, hu.2⟩)
    rw [hdegree] at hdef
    have hsign : 0 ≤ (-1 : ℝ) ^ (N + 1) *
        (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) := by
      rw [hsignEq]
      exact hdef
    have hp := inverse_power_kernel_sub_pos hx hxy hu.1.le (2 * N + 3) (by omega)
    dsimp [f]
    simpa only [mul_assoc] using mul_nonneg hsign hp.le
  have hhalf : 0 < f (1 / 2) := by
    have hdef := bernoulli_even_endpoint_defect_half_pos (N + 1) (by omega)
    rw [hdegree] at hdef
    have hsign : 0 < (-1 : ℝ) ^ (N + 1) *
        (bernoulliFun (2 * N + 2) (1 / 2) - bernoulliFun (2 * N + 2) 0) := by
      rw [hsignEq]
      exact hdef
    have hp := inverse_power_kernel_sub_pos hx hxy
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (2 * N + 3) (by omega)
    dsimp [f]
    simpa only [mul_assoc] using mul_pos hsign hp
  have hint : 0 < ∫ u in (0 : ℝ)..1, f u :=
    intervalIntegral.integral_pos (by norm_num) hcont hnonneg
      ⟨1 / 2, by constructor <;> norm_num, hhalf⟩
  dsimp [f] at hint
  rw [intervalIntegral.integral_const_mul,
    ← endpointDefectCell_sub_eq_integral hx hy N] at hint
  exact hint

/-- Weak signed monotonicity, also covering equality of the base arguments. -/
theorem endpointDefectCell_signed_sub_nonneg {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ (N + 1) *
      (endpointDefectCell N x - endpointDefectCell N y) := by
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · exact (endpointDefectCell_signed_sub_pos hx hlt N).le
  · simp

/-- The complete cell series is subtracted without discarding cancellation. -/
theorem hasSum_endpointDefectCell_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (N : ℕ) :
    HasSum (fun n : ℕ => endpointDefectCell N ((n : ℝ) + x) -
      endpointDefectCell N ((n : ℝ) + y))
      (evenDigammaError N x - evenDigammaError N y) :=
  (hasSum_endpointDefectCell hx N).sub (hasSum_endpointDefectCell hy N)

theorem evenDigammaError_sub_eq_tsum {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (N : ℕ) :
    evenDigammaError N x - evenDigammaError N y =
      ∑' n : ℕ, (endpointDefectCell N ((n : ℝ) + x) -
        endpointDefectCell N ((n : ℝ) + y)) :=
  (hasSum_endpointDefectCell_sub hx hy N).tsum_eq.symm

/-- Every signed complete digamma error is strictly decreasing on the
positive axis; the actual cell difference is strictly positive. -/
theorem evenDigammaError_signed_sub_pos {x y : ℝ} (hx : 0 < x)
    (hxy : x < y) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (evenDigammaError N x - evenDigammaError N y) := by
  have hy : 0 < y := lt_trans hx hxy
  have hs := (hasSum_endpointDefectCell_sub hx hy N).mul_left
    ((-1 : ℝ) ^ (N + 1))
  rw [← hs.tsum_eq]
  apply hs.summable.tsum_pos
    (fun n => (endpointDefectCell_signed_sub_pos (by positivity)
      (by linarith : (n : ℝ) + x < (n : ℝ) + y) N).le) 0
  simpa only [Nat.cast_zero, zero_add] using endpointDefectCell_signed_sub_pos hx hxy N

theorem signed_evenDigammaError_strictAntiOn (N : ℕ) :
    StrictAntiOn (fun x : ℝ => (-1 : ℝ) ^ (N + 1) * evenDigammaError N x)
      (Ioi 0) := by
  intro x hx y hy hxy
  have h := evenDigammaError_signed_sub_pos hx hxy N
  linarith

/-- The exact first omitted inverse-power difference is retained together
with the complete next error difference. -/
theorem evenDigammaError_sub_succ (N : ℕ) (x y : ℝ) :
    evenDigammaError N x - evenDigammaError N y =
      -(bernoulliCoefficient (2 * N + 2) *
        ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2))) +
      (evenDigammaError (N + 1) x - evenDigammaError (N + 1) y) := by
  rw [evenDigammaError_succ N x, evenDigammaError_succ N y]
  ring

/-- The strict all-order remainder bound for differences keeps the
first-omitted powers inside a single difference. -/
theorem evenDigammaError_sub_strict_signed_bound {x y : ℝ} (hx : 0 < x)
    (hxy : x < y) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (evenDigammaError N x - evenDigammaError N y) ∧
    (-1 : ℝ) ^ (N + 1) *
      (evenDigammaError N x - evenDigammaError N y) <
      |bernoulliCoefficient (2 * N + 2)| *
        ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2)) := by
  refine ⟨evenDigammaError_signed_sub_pos hx hxy N, ?_⟩
  have hnext := evenDigammaError_signed_sub_pos hx hxy (N + 1)
  have hopp : (-1 : ℝ) ^ ((N + 1) + 1) = -((-1 : ℝ) ^ (N + 1)) := by
    rw [pow_succ]
    ring
  rw [hopp] at hnext
  have hnextNeg : (-1 : ℝ) ^ (N + 1) *
      (evenDigammaError (N + 1) x - evenDigammaError (N + 1) y) < 0 := by
    nlinarith
  rw [evenDigammaError_sub_succ]
  calc
    (-1 : ℝ) ^ (N + 1) *
        (-(bernoulliCoefficient (2 * N + 2) *
          ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2))) +
            (evenDigammaError (N + 1) x - evenDigammaError (N + 1) y)) =
        (-((-1 : ℝ) ^ (N + 1)) * bernoulliCoefficient (2 * N + 2)) *
          ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2)) +
          (-1 : ℝ) ^ (N + 1) *
            (evenDigammaError (N + 1) x - evenDigammaError (N + 1) y) := by ring
    _ = |bernoulliCoefficient (2 * N + 2)| *
          ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2)) +
          (-1 : ℝ) ^ (N + 1) *
            (evenDigammaError (N + 1) x - evenDigammaError (N + 1) y) := by
      rw [signed_bernoulliCoefficient_eq_abs]
    _ < |bernoulliCoefficient (2 * N + 2)| *
          ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2)) := by linarith

/-- An absolute bound is taken only after the actual difference's alternating
sign and cancellation have been established. -/
theorem evenDigammaError_sub_strict_absolute_bound {x y : ℝ} (hx : 0 < x)
    (hxy : x < y) (N : ℕ) :
    0 < |evenDigammaError N x - evenDigammaError N y| ∧
    |evenDigammaError N x - evenDigammaError N y| <
      |bernoulliCoefficient (2 * N + 2)| *
        ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2)) := by
  have hb := evenDigammaError_sub_strict_signed_bound hx hxy N
  have hsabs : |(-1 : ℝ) ^ (N + 1)| = 1 := by simp
  have he : |evenDigammaError N x - evenDigammaError N y| =
      (-1 : ℝ) ^ (N + 1) *
        (evenDigammaError N x - evenDigammaError N y) := by
    calc
      _ = |(-1 : ℝ) ^ (N + 1) *
        (evenDigammaError N x - evenDigammaError N y)| := by
          rw [abs_mul, hsabs, one_mul]
      _ = _ := abs_of_nonneg hb.1.le
  rw [he]
  exact hb

/-- The finite Bernoulli correction also keeps the inverse-power
differences inside the same finite sum. -/
theorem evenBernoulliPowerSum_sub_eq (N : ℕ) (x y : ℝ) :
    evenBernoulliPowerSum N x - evenBernoulliPowerSum N y =
      ∑ j ∈ Finset.range N, bernoulliCoefficient (2 * j + 2) *
        ((x⁻¹) ^ (2 * j + 2) - (y⁻¹) ^ (2 * j + 2)) := by
  unfold evenBernoulliPowerSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact actual digamma difference, with the complete error difference
and every signed inverse-power difference retained. -/
theorem re_digamma_difference_exact {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (N : ℕ) :
    (Complex.digamma (y : ℂ)).re - (Complex.digamma (x : ℂ)).re =
      Real.log (y / x) + (1 / (2 * x) - 1 / (2 * y)) +
      (∑ j ∈ Finset.range N, bernoulliCoefficient (2 * j + 2) *
        ((x⁻¹) ^ (2 * j + 2) - (y⁻¹) ^ (2 * j + 2))) -
      (evenDigammaError N x - evenDigammaError N y) := by
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx), ← evenBernoulliPowerSum_sub_eq]
  unfold evenDigammaError
  ring

/-- Sharp actual digamma difference enclosure at every even Bernoulli
truncation order, with the complete first-omitted power difference. -/
theorem re_digamma_difference_strict_signed_bound {x y : ℝ} (hx : 0 < x)
    (hxy : x < y) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (Real.log (y / x) + (1 / (2 * x) - 1 / (2 * y)) +
        (∑ j ∈ Finset.range N, bernoulliCoefficient (2 * j + 2) *
          ((x⁻¹) ^ (2 * j + 2) - (y⁻¹) ^ (2 * j + 2))) -
        ((Complex.digamma (y : ℂ)).re - (Complex.digamma (x : ℂ)).re)) ∧
    (-1 : ℝ) ^ (N + 1) *
      (Real.log (y / x) + (1 / (2 * x) - 1 / (2 * y)) +
        (∑ j ∈ Finset.range N, bernoulliCoefficient (2 * j + 2) *
          ((x⁻¹) ^ (2 * j + 2) - (y⁻¹) ^ (2 * j + 2))) -
        ((Complex.digamma (y : ℂ)).re - (Complex.digamma (x : ℂ)).re)) <
      |bernoulliCoefficient (2 * N + 2)| *
        ((x⁻¹) ^ (2 * N + 2) - (y⁻¹) ^ (2 * N + 2)) := by
  have he : Real.log (y / x) + (1 / (2 * x) - 1 / (2 * y)) +
      (∑ j ∈ Finset.range N, bernoulliCoefficient (2 * j + 2) *
        ((x⁻¹) ^ (2 * j + 2) - (y⁻¹) ^ (2 * j + 2))) -
      ((Complex.digamma (y : ℂ)).re - (Complex.digamma (x : ℂ)).re) =
      evenDigammaError N x - evenDigammaError N y := by
    rw [re_digamma_difference_exact hx (lt_trans hx hxy) N]
    ring
  rw [he]
  exact evenDigammaError_sub_strict_signed_bound hx hxy N

end RiemannResearch.RH.DigammaBernoulliDifferences
