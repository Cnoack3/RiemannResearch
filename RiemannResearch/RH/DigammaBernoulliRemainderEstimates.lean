import RiemannResearch.RH.DigammaBernoulliRemainderBounds
import Mathlib.Tactic

/-!
# Unconditional arbitrary-order positive-real digamma estimates

The exact complete remainder identity precedes all estimates. The final
Bernoulli bound constant is supplied by a proved compactness argument for the
actual Bernoulli polynomial, not by an asymptotic or Binet hypothesis.

All constants and analytic providers are proved in the imported development.

Source for the classical asymptotic statement: NIST DLMF 5.11.2
(https://dlmf.nist.gov/5.11.E2). The formal proof uses the actual digamma
partial-fraction series and Bernoulli integration by parts.
-/

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped BigOperators Topology

namespace RiemannResearch.RH.DigammaBernoulliRemainderEstimates

open RiemannResearch.RH.DigammaAsymptotic
open RiemannResearch.RH.DigammaBernoulliCells
open RiemannResearch.RH.DigammaBernoulliRemainderBounds

/-- A norm bound for the actual Bernoulli-cell integral, with its telescoping
inverse-power difference retained. -/
theorem bernoulliCell_abs_le {x : ℝ} (hx : 0 < x)
    (k : ℕ) (hk : 0 < k) (M : ℝ)
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, |bernoulliFun k u| ≤ M) :
    |bernoulliCell k x| ≤ (M / (k : ℝ)) * inversePowerDifference x k := by
  have hgint : IntervalIntegrable
      (fun u : ℝ => M * ((x + u)⁻¹) ^ (k + 1)) volume 0 1 :=
    (((continuousOn_inverse_shift hx).pow (k + 1)).const_mul M).intervalIntegrable
  have hdom : ∀ᵐ u : ℝ ∂volume, u ∈ Ioc (0 : ℝ) 1 →
      ‖bernoulliFun k u * ((x + u)⁻¹) ^ (k + 1)‖ ≤
        M * ((x + u)⁻¹) ^ (k + 1) := by
    apply Filter.Eventually.of_forall
    intro u hu
    have hxu : 0 ≤ x + u := by linarith [hu.1]
    have hp : 0 ≤ ((x + u)⁻¹) ^ (k + 1) :=
      pow_nonneg (inv_nonneg.mpr hxu) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (hM u ⟨le_of_lt hu.1, hu.2⟩) hp
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (by norm_num : (0 : ℝ) ≤ 1) hdom hgint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    inversePower_kernel_integral hx k hk] at hnorm
  calc
    |bernoulliCell k x| ≤ M * (inversePowerDifference x k / (k : ℝ)) := hnorm
    _ = (M / (k : ℝ)) * inversePowerDifference x k := by ring

/-- The absolute complete Bernoulli remainder is bounded by the exact endpoint
power. The whole signed series is retained until this norm estimate. -/
theorem bernoulliCell_tsum_abs_le {x : ℝ} (hx : 0 < x)
    (k : ℕ) (hk : 0 < k) (M : ℝ)
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, |bernoulliFun k u| ≤ M) :
    |∑' n : ℕ, bernoulliCell k ((n : ℝ) + x)| ≤
      (M / (k : ℝ)) * (x⁻¹) ^ k := by
  have hkle : 1 ≤ k := hk
  have hcell : Summable (fun n : ℕ => bernoulliCell k ((n : ℝ) + x)) := by
    simpa only [Nat.sub_add_cancel hkle] using
      (hasSum_bernoulliCell_remainder hx (k - 1)).summable
  have hmajor := (hasSum_inversePowerDifference hx k hk).mul_left (M / (k : ℝ))
  have hpoint (n : ℕ) :
      |bernoulliCell k ((n : ℝ) + x)| ≤
        (M / (k : ℝ)) * inversePowerDifference ((n : ℝ) + x) k :=
    bernoulliCell_abs_le (by positivity) k hk M hM
  have hsumle := Summable.tsum_le_tsum hpoint hcell.abs hmajor.summable
  rw [hmajor.tsum_eq] at hsumle
  have hnorm := norm_tsum_le_tsum_norm hcell.norm
  simp only [Real.norm_eq_abs] at hnorm
  exact le_trans hnorm hsumle

/-- A proved arbitrary-order bound for the literal digamma through consecutive
Bernoulli powers, valid on the whole positive real axis. -/
theorem re_digamma_consecutive_remainder_bound {x : ℝ} (hx : 0 < x)
    (m : ℕ) (M : ℝ)
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, |bernoulliFun (m + 1) u| ≤ M) :
    |(Complex.digamma (x : ℂ)).re -
      (Real.log x - 1 / (2 * x) - bernoulliPowerSum m x)| ≤
        (M / ((m + 1 : ℕ) : ℝ)) * (x⁻¹) ^ (m + 1) := by
  have he : (Complex.digamma (x : ℂ)).re -
      (Real.log x - 1 / (2 * x) - bernoulliPowerSum m x) =
        ∑' n : ℕ, bernoulliCell (m + 1) ((n : ℝ) + x) := by
    rw [re_digamma_eq_bernoulli_with_tsum_remainder hx m]
    ring
  rw [he]
  exact bernoulliCell_tsum_abs_le hx (m + 1) (by omega) M hM

/-- The Bernoulli bound provider is discharged from the actual compact cell. -/
theorem exists_re_digamma_consecutive_remainder_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      |(Complex.digamma (x : ℂ)).re -
        (Real.log x - 1 / (2 * x) - bernoulliPowerSum m x)| ≤
          C * (x⁻¹) ^ (m + 1) := by
  obtain ⟨M, hMnonneg, hM⟩ := exists_bernoulliFun_bound (m + 1)
  refine ⟨M / ((m + 1 : ℕ) : ℝ), by positivity, ?_⟩
  intro x hx
  exact re_digamma_consecutive_remainder_bound hx m M hM

/-- The standard even Bernoulli inverse-power sum through degree `2 * N`. -/
def evenBernoulliPowerSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    bernoulliCoefficient (2 * j + 2) * (x⁻¹) ^ (2 * j + 2)

theorem bernoulliPowerSum_succ (m : ℕ) (x : ℝ) :
    bernoulliPowerSum (m + 1) x = bernoulliPowerSum m x +
      bernoulliCoefficient (m + 2) * (x⁻¹) ^ (m + 2) := by
  simp only [bernoulliPowerSum, Finset.sum_range_succ]

theorem bernoulliCoefficient_odd {k : ℕ} (hk : Odd k) (hk1 : 1 < k) :
    bernoulliCoefficient k = 0 := by
  simp [bernoulliCoefficient, bernoulli_eq_zero_of_odd hk hk1]

/-- Odd Bernoulli coefficients vanish inside the finite consecutive sum. -/
theorem bernoulliPowerSum_two_mul (N : ℕ) (x : ℝ) :
    bernoulliPowerSum (2 * N) x = evenBernoulliPowerSum N x := by
  induction N with
  | zero => simp [bernoulliPowerSum, evenBernoulliPowerSum]
  | succ N ih =>
      have hodd : Odd (2 * N + 3) := ⟨N + 1, by omega⟩
      have hcoef : bernoulliCoefficient (2 * N + 3) = 0 :=
        bernoulliCoefficient_odd hodd (by omega)
      calc
        bernoulliPowerSum (2 * (N + 1)) x =
            bernoulliPowerSum ((2 * N + 1) + 1) x := by
          congr 1 <;> omega
        _ = bernoulliPowerSum (2 * N) x +
              bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2) +
              bernoulliCoefficient (2 * N + 3) * (x⁻¹) ^ (2 * N + 3) := by
          rw [bernoulliPowerSum_succ, bernoulliPowerSum_succ]
        _ = evenBernoulliPowerSum (N + 1) x := by
          rw [ih, hcoef]
          simp only [evenBernoulliPowerSum, Finset.sum_range_succ, zero_mul, add_zero]

/-- Exact standard even-order expansion: the first omitted even coefficient
and the complete signed Bernoulli remainder are both retained. -/
theorem re_digamma_even_error_eq {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (Complex.digamma (x : ℂ)).re -
      (Real.log x - 1 / (2 * x) - evenBernoulliPowerSum N x) =
        -(bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2)) +
          ∑' n : ℕ, bernoulliCell (2 * N + 2) ((n : ℝ) + x) := by
  rw [re_digamma_eq_bernoulli_with_tsum_remainder hx (2 * N + 1),
    bernoulliPowerSum_succ, bernoulliPowerSum_two_mul]
  ring

/-- Unconditional arbitrary-order positive-real Poincaré expansion of the
literal digamma, with the actual Bernoulli coefficients and a proved constant. -/
theorem exists_re_digamma_even_remainder_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      |(Complex.digamma (x : ℂ)).re -
        (Real.log x - 1 / (2 * x) - evenBernoulliPowerSum N x)| ≤
          C / x ^ (2 * N + 2) := by
  obtain ⟨M, hMnonneg, hM⟩ := exists_bernoulliFun_bound (2 * N + 2)
  let C : ℝ := |bernoulliCoefficient (2 * N + 2)| +
    M / ((2 * N + 2 : ℕ) : ℝ)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x hx
  have ht := bernoulliCell_tsum_abs_le hx (2 * N + 2) (by omega) M hM
  have hp : 0 ≤ (x⁻¹) ^ (2 * N + 2) := by positivity
  rw [re_digamma_even_error_eq hx N]
  calc
    |-(bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2)) +
        ∑' n : ℕ, bernoulliCell (2 * N + 2) ((n : ℝ) + x)| ≤
        |-(bernoulliCoefficient (2 * N + 2) * (x⁻¹) ^ (2 * N + 2))| +
          |∑' n : ℕ, bernoulliCell (2 * N + 2) ((n : ℝ) + x)| := abs_add_le _ _
    _ ≤ |bernoulliCoefficient (2 * N + 2)| * (x⁻¹) ^ (2 * N + 2) +
        (M / ((2 * N + 2 : ℕ) : ℝ)) * (x⁻¹) ^ (2 * N + 2) := by
      rw [abs_neg, abs_mul, abs_of_nonneg hp]
      exact add_le_add (le_refl _) ht
    _ = C / x ^ (2 * N + 2) := by
      dsimp [C]
      simp only [div_eq_mul_inv, inv_pow]
      ring

end RiemannResearch.RH.DigammaBernoulliRemainderEstimates
