import RiemannResearch.RH.DigammaBernoulliRemainderEstimates
import RiemannResearch.Analysis.BernoulliEndpointDefect
import Mathlib.Tactic

/-!
# Sharp signed Bernoulli remainder for literal positive-real digamma

The exact remainder is a complete sum of endpoint-defect cell integrals.
The endpoint-defect sign is proved by the Bernoulli Fourier series. No Binet
formula, interchange of an infinite sum with an integral, or assumed digamma
asymptotic is used.

Strict positivity follows from the midpoint defect and continuity of the
actual cell integrand. The complete HasSum gives the strict global sign,
and the next-order sign makes the first-omitted-term upper bound strict.
-/

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped BigOperators Topology

namespace RiemannResearch.RH.DigammaBernoulliSignedRemainder

open RiemannResearch.Analysis
open RiemannResearch.RH.DigammaAsymptotic
open RiemannResearch.RH.DigammaBernoulliCells
open RiemannResearch.RH.DigammaBernoulliRemainderBounds
open RiemannResearch.RH.DigammaBernoulliRemainderEstimates

/-- Literal error after the first `N` even Bernoulli terms. -/
def evenDigammaError (N : ℕ) (x : ℝ) : ℝ :=
  (Complex.digamma (x : ℂ)).re -
    (Real.log x - 1 / (2 * x) - evenBernoulliPowerSum N x)

/-- Actual complete cell endpoint defect; both endpoint and polynomial terms
remain inside the signed integral. -/
def endpointDefectCell (N : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) *
      ((x + u)⁻¹) ^ (2 * N + 3)

/-- The exact cell defect is the actual Bernoulli cell minus its endpoint
contribution. The positive kernel integral is evaluated by the proved FTC. -/
theorem endpointDefectCell_eq {x : ℝ} (hx : 0 < x) (N : ℕ) :
    endpointDefectCell N x = bernoulliCell (2 * N + 2) x -
      bernoulliCoefficient (2 * N + 2) *
        inversePowerDifference x (2 * N + 2) := by
  have hpolyint : IntervalIntegrable
      (fun u : ℝ => bernoulliFun (2 * N + 2) u *
        ((x + u)⁻¹) ^ (2 * N + 3)) volume 0 1 :=
    ((continuous_bernoulliFun (2 * N + 2)).continuousOn.mul
      ((continuousOn_inverse_shift hx).pow (2 * N + 3))).intervalIntegrable
  have hconstint : IntervalIntegrable
      (fun u : ℝ => bernoulliFun (2 * N + 2) 0 *
        ((x + u)⁻¹) ^ (2 * N + 3)) volume 0 1 :=
    (((continuousOn_inverse_shift hx).pow (2 * N + 3)).const_mul
      (bernoulliFun (2 * N + 2) 0)).intervalIntegrable
  unfold endpointDefectCell
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub hpolyint hconstint,
    intervalIntegral.integral_const_mul,
    inversePower_kernel_integral hx (2 * N + 2) (by omega),
    bernoulliFun_eval_zero]
  change bernoulliCell (2 * N + 2) x -
      (bernoulli (2 * N + 2) : ℝ) *
        (inversePowerDifference x (2 * N + 2) / ((2 * N + 2 : ℕ) : ℝ)) = _
  dsimp [bernoulliCoefficient]
  ring

/-- The complete endpoint-defect series sums to the actual digamma error.
No desired expansion identity is a hypothesis. -/
theorem hasSum_endpointDefectCell {x : ℝ} (hx : 0 < x) (N : ℕ) :
    HasSum (fun n : ℕ => endpointDefectCell N ((n : ℝ) + x))
      (evenDigammaError N x) := by
  have hcell := hasSum_bernoulliCell_remainder hx (2 * N + 1)
  have hendpoint := (hasSum_inversePowerDifference hx (2 * N + 2) (by omega)).mul_left
    (bernoulliCoefficient (2 * N + 2))
  have h := hcell.sub hendpoint
  have hfun : (fun n : ℕ => bernoulliCell (2 * N + 2) ((n : ℝ) + x) -
      bernoulliCoefficient (2 * N + 2) *
        inversePowerDifference ((n : ℝ) + x) (2 * N + 2)) =
      (fun n : ℕ => endpointDefectCell N ((n : ℝ) + x)) := by
    funext n
    exact (endpointDefectCell_eq (by positivity) N).symm
  rw [hfun] at h
  have hvalue : bernoulliPowerSum (2 * N + 1) x -
      (Real.log x - 1 / (2 * x) - (Complex.digamma (x : ℂ)).re) -
        bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2) =
      evenDigammaError N x := by
    rw [bernoulliPowerSum_succ, bernoulliPowerSum_two_mul]
    dsimp [evenDigammaError]
    ring
  rw [hvalue] at h
  exact h

/-- The exact full signed remainder stays visible before inequalities. -/
theorem evenDigammaError_eq_tsum_endpointDefect {x : ℝ} (hx : 0 < x) (N : ℕ) :
    evenDigammaError N x =
      ∑' n : ℕ, endpointDefectCell N ((n : ℝ) + x) :=
  (hasSum_endpointDefectCell hx N).tsum_eq.symm

/-- Pointwise Fourier endpoint sign transfers to the actual weighted cell. -/
theorem endpointDefectCell_signed_nonneg {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ (N + 1) * endpointDefectCell N x := by
  have hpoint (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      0 ≤ (-1 : ℝ) ^ (N + 1) *
        ((bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) *
          ((x + u)⁻¹) ^ (2 * N + 3)) := by
    have hdefect := bernoulli_even_endpoint_defect_nonneg (N + 1) (by omega) hu
    have hdegree : 2 * (N + 1) = 2 * N + 2 := by omega
    rw [hdegree] at hdefect
    have hsignEq : (-1 : ℝ) ^ (N + 1) *
        (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) =
      (-1 : ℝ) ^ ((N + 1) + 1) *
        (bernoulliFun (2 * N + 2) 0 - bernoulliFun (2 * N + 2) u) := by
      rw [pow_succ (-1 : ℝ) (N + 1)]
      ring
    have hs : 0 ≤ (-1 : ℝ) ^ (N + 1) *
        (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) := by
      rw [hsignEq]
      exact hdefect
    have hxu : 0 ≤ x + u := by linarith [hu.1]
    have hp : 0 ≤ ((x + u)⁻¹) ^ (2 * N + 3) :=
      pow_nonneg (inv_nonneg.mpr hxu) _
    simpa only [mul_assoc] using mul_nonneg hs hp
  have hint := intervalIntegral.integral_nonneg (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  exact hint

/-- All finite Bernoulli orders have the actual alternating error sign. -/
theorem evenDigammaError_signed_nonneg {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ (N + 1) * evenDigammaError N x := by
  have hs := (hasSum_endpointDefectCell hx N).mul_left ((-1 : ℝ) ^ (N + 1))
  rw [← hs.tsum_eq]
  exact tsum_nonneg fun n => endpointDefectCell_signed_nonneg (by positivity) N

/-- Consecutive even errors retain the actual first omitted term exactly. -/
theorem evenDigammaError_succ (N : ℕ) (x : ℝ) :
    evenDigammaError N x =
      -(bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2)) +
        evenDigammaError (N + 1) x := by
  dsimp [evenDigammaError, evenBernoulliPowerSum]
  rw [Finset.sum_range_succ]
  ring

/-- The actual Bernoulli sign identifies the signed omitted coefficient with
its absolute value. -/
theorem signed_bernoulliCoefficient_eq_abs (N : ℕ) :
    -((-1 : ℝ) ^ (N + 1)) * bernoulliCoefficient (2 * N + 2) =
      |bernoulliCoefficient (2 * N + 2)| := by
  have hB := bernoulli_even_signed_pos (N + 1) (by omega)
  have hdegree : 2 * (N + 1) = 2 * N + 2 := by omega
  rw [hdegree] at hB
  have hden : 0 < ((2 * N + 2 : ℕ) : ℝ) := by positivity
  have hquot : 0 ≤
      ((-1 : ℝ) ^ ((N + 1) + 1) * (bernoulli (2 * N + 2) : ℝ)) /
        ((2 * N + 2 : ℕ) : ℝ) := (div_pos hB hden).le
  have he : -((-1 : ℝ) ^ (N + 1)) * bernoulliCoefficient (2 * N + 2) =
      ((-1 : ℝ) ^ ((N + 1) + 1) * (bernoulli (2 * N + 2) : ℝ)) /
        ((2 * N + 2 : ℕ) : ℝ) := by
    dsimp [bernoulliCoefficient]
    rw [pow_succ (-1 : ℝ) (N + 1)]
    ring
  have hnonneg : 0 ≤ -((-1 : ℝ) ^ (N + 1)) *
      bernoulliCoefficient (2 * N + 2) := by
    rw [he]
    exact hquot
  have hsabs : |(-1 : ℝ) ^ (N + 1)| = 1 := by simp
  calc
    -((-1 : ℝ) ^ (N + 1)) * bernoulliCoefficient (2 * N + 2) =
        |(-((-1 : ℝ) ^ (N + 1))) * bernoulliCoefficient (2 * N + 2)| :=
      (abs_of_nonneg hnonneg).symm
    _ = |bernoulliCoefficient (2 * N + 2)| := by
      rw [abs_mul, abs_neg, hsabs, one_mul]

/-- Sharp all-order weak enclosure by the first omitted Bernoulli term. -/
theorem re_digamma_sharp_signed_remainder {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ) ^ (N + 1) * evenDigammaError N x ∧
      (-1 : ℝ) ^ (N + 1) * evenDigammaError N x ≤
        |bernoulliCoefficient (2 * N + 2)| / x ^ (2 * N + 2) := by
  refine ⟨evenDigammaError_signed_nonneg hx N, ?_⟩
  have hnext := evenDigammaError_signed_nonneg hx (N + 1)
  have hopp : (-1 : ℝ) ^ ((N + 1) + 1) = -((-1 : ℝ) ^ (N + 1)) := by
    rw [pow_succ]
    ring
  rw [hopp] at hnext
  have hnextNonpos : (-1 : ℝ) ^ (N + 1) * evenDigammaError (N + 1) x ≤ 0 := by
    nlinarith
  rw [evenDigammaError_succ]
  calc
    (-1 : ℝ) ^ (N + 1) *
        (-(bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2)) +
          evenDigammaError (N + 1) x) =
        (-((-1 : ℝ) ^ (N + 1)) * bernoulliCoefficient (2 * N + 2)) *
          (x⁻¹) ^ (2 * N + 2) +
            (-1 : ℝ) ^ (N + 1) * evenDigammaError (N + 1) x := by ring
    _ = |bernoulliCoefficient (2 * N + 2)| * (x⁻¹) ^ (2 * N + 2) +
          (-1 : ℝ) ^ (N + 1) * evenDigammaError (N + 1) x := by
      rw [signed_bernoulliCoefficient_eq_abs]
    _ ≤ |bernoulliCoefficient (2 * N + 2)| * (x⁻¹) ^ (2 * N + 2) := by
      linarith
    _ = |bernoulliCoefficient (2 * N + 2)| / x ^ (2 * N + 2) := by
      simp only [div_eq_mul_inv, inv_pow]

/-- Sharp all-order absolute enclosure follows from the proved alternating sign. -/
theorem re_digamma_sharp_absolute_remainder {x : ℝ} (hx : 0 < x) (N : ℕ) :
    |evenDigammaError N x| ≤
      |bernoulliCoefficient (2 * N + 2)| / x ^ (2 * N + 2) := by
  have hb := re_digamma_sharp_signed_remainder hx N
  have hsabs : |(-1 : ℝ) ^ (N + 1)| = 1 := by simp
  have he : |evenDigammaError N x| =
      (-1 : ℝ) ^ (N + 1) * evenDigammaError N x := by
    calc
      |evenDigammaError N x| = |(-1 : ℝ) ^ (N + 1) * evenDigammaError N x| := by
        rw [abs_mul, hsabs, one_mul]
      _ = _ := abs_of_nonneg hb.1
  rw [he]
  exact hb.2

/-- Strict positivity of the actual signed endpoint-defect cell. -/
theorem endpointDefectCell_signed_pos {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) * endpointDefectCell N x := by
  let f : ℝ → ℝ := fun u => (-1 : ℝ) ^ (N + 1) *
    ((bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) *
      ((x + u)⁻¹) ^ (2 * N + 3))
  have hdegree : 2 * (N + 1) = 2 * N + 2 := by omega
  have hsignEq (u : ℝ) : (-1 : ℝ) ^ (N + 1) *
      (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) =
      (-1 : ℝ) ^ ((N + 1) + 1) *
        (bernoulliFun (2 * N + 2) 0 - bernoulliFun (2 * N + 2) u) := by
    rw [pow_succ (-1 : ℝ) (N + 1)]
    ring
  have hcontInv : ContinuousOn (fun u : ℝ => (x + u)⁻¹) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      continuousOn_inverse_shift hx
  have hcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (((continuous_bernoulliFun (2 * N + 2)).continuousOn.sub continuousOn_const).mul
      (hcontInv.pow (2 * N + 3))).const_mul ((-1 : ℝ) ^ (N + 1))
  have hnonneg (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) : 0 ≤ f u := by
    have hdef := bernoulli_even_endpoint_defect_nonneg (N + 1) (by omega)
      (show u ∈ Icc (0 : ℝ) 1 from ⟨hu.1.le, hu.2⟩)
    rw [hdegree] at hdef
    have hsign : 0 ≤ (-1 : ℝ) ^ (N + 1) *
        (bernoulliFun (2 * N + 2) u - bernoulliFun (2 * N + 2) 0) := by
      rw [hsignEq]
      exact hdef
    have hxu : 0 ≤ x + u := by linarith [hu.1]
    have hp : 0 ≤ ((x + u)⁻¹) ^ (2 * N + 3) :=
      pow_nonneg (inv_nonneg.mpr hxu) _
    dsimp [f]
    simpa only [mul_assoc] using mul_nonneg hsign hp
  have hhalf : 0 < f (1 / 2) := by
    have hdef := bernoulli_even_endpoint_defect_half_pos (N + 1) (by omega)
    rw [hdegree] at hdef
    have hsign : 0 < (-1 : ℝ) ^ (N + 1) *
        (bernoulliFun (2 * N + 2) (1 / 2) - bernoulliFun (2 * N + 2) 0) := by
      rw [hsignEq]
      exact hdef
    have hp : 0 < ((x + 1 / 2)⁻¹) ^ (2 * N + 3) := by positivity
    dsimp [f]
    simpa only [mul_assoc] using mul_pos hsign hp
  have hint : 0 < ∫ u in (0 : ℝ)..1, f u :=
    intervalIntegral.integral_pos (by norm_num) hcont hnonneg
      ⟨1 / 2, by constructor <;> norm_num, hhalf⟩
  dsimp [f] at hint
  rw [intervalIntegral.integral_const_mul] at hint
  exact hint

/-- Strict alternating sign of the literal complete digamma error. -/
theorem evenDigammaError_signed_pos {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) * evenDigammaError N x := by
  have hs := (hasSum_endpointDefectCell hx N).mul_left ((-1 : ℝ) ^ (N + 1))
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos
    (fun n => endpointDefectCell_signed_nonneg (by positivity) N) 0
    (by simpa only [Nat.cast_zero, zero_add] using endpointDefectCell_signed_pos hx N)

/-- Strict sharp enclosure at every finite Bernoulli order and every positive
real argument: the first omitted term bounds the entire signed remainder. -/
theorem re_digamma_strict_signed_remainder {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 < (-1 : ℝ) ^ (N + 1) * evenDigammaError N x ∧
      (-1 : ℝ) ^ (N + 1) * evenDigammaError N x <
        |bernoulliCoefficient (2 * N + 2)| / x ^ (2 * N + 2) := by
  refine ⟨evenDigammaError_signed_pos hx N, ?_⟩
  have hnext := evenDigammaError_signed_pos hx (N + 1)
  have hopp : (-1 : ℝ) ^ ((N + 1) + 1) = -((-1 : ℝ) ^ (N + 1)) := by
    rw [pow_succ]
    ring
  rw [hopp] at hnext
  have hnextNeg : (-1 : ℝ) ^ (N + 1) * evenDigammaError (N + 1) x < 0 := by
    nlinarith
  rw [evenDigammaError_succ]
  calc
    (-1 : ℝ) ^ (N + 1) *
        (-(bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2)) +
          evenDigammaError (N + 1) x) =
        (-((-1 : ℝ) ^ (N + 1)) * bernoulliCoefficient (2 * N + 2)) *
          (x⁻¹) ^ (2 * N + 2) +
            (-1 : ℝ) ^ (N + 1) * evenDigammaError (N + 1) x := by ring
    _ = |bernoulliCoefficient (2 * N + 2)| * (x⁻¹) ^ (2 * N + 2) +
          (-1 : ℝ) ^ (N + 1) * evenDigammaError (N + 1) x := by
      rw [signed_bernoulliCoefficient_eq_abs]
    _ < |bernoulliCoefficient (2 * N + 2)| * (x⁻¹) ^ (2 * N + 2) := by
      linarith
    _ = |bernoulliCoefficient (2 * N + 2)| / x ^ (2 * N + 2) := by
      simp only [div_eq_mul_inv, inv_pow]

/-- The full error has strictly smaller absolute value than the first omitted
term, including `N = 0`. -/
theorem re_digamma_strict_absolute_remainder {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 < |evenDigammaError N x| ∧
      |evenDigammaError N x| <
        |bernoulliCoefficient (2 * N + 2)| / x ^ (2 * N + 2) := by
  have hb := re_digamma_strict_signed_remainder hx N
  have hsabs : |(-1 : ℝ) ^ (N + 1)| = 1 := by simp
  have he : |evenDigammaError N x| =
      (-1 : ℝ) ^ (N + 1) * evenDigammaError N x := by
    calc
      |evenDigammaError N x| = |(-1 : ℝ) ^ (N + 1) * evenDigammaError N x| := by
        rw [abs_mul, hsabs, one_mul]
      _ = _ := abs_of_nonneg hb.1.le
  rw [he]
  exact hb

end RiemannResearch.RH.DigammaBernoulliSignedRemainder
