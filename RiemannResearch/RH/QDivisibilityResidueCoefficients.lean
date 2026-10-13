import RiemannResearch.RH.QDilationMoments
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact inclusion-exclusion coefficients of residue atoms under Q

Source: user-provided prime/divisibility reformulation, 13 October 2026.
The inverse-square divisibility scale cancels the squared conductor in
each signed incidence term. The resulting divisor coefficient is a finite
Möbius difference of actual twisted residue expectations. No independence
of ordinary congruence classes is used, and every signed term is retained.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.ArithmeticCumulative

/-- Finite linearity with a separate integrable bound on each summand. -/
theorem inversePowerMean_finsetSum {ι : Type*} (S : Finset ι)
    (f : ι → ℕ → ℝ) (C : ι → ℝ)
    (hf : ∀ i ∈ S, ∀ n, |f i n| ≤ C i) :
    inversePowerMean 0 (fun n => ∑ i ∈ S, f i n) =
      ∑ i ∈ S, inversePowerMean 0 (f i) := by
  unfold inversePowerMean
  simp_rw [Finset.sum_div]
  exact Summable.tsum_finsetSum (fun i hi =>
    inversePowerMean_summable_of_bounded 0 (f i) (hf i hi))

theorem inversePowerMean_const_mul (a : ℝ) (f : ℕ → ℝ) :
    inversePowerMean 0 (fun n => a * f n) = a * inversePowerMean 0 f := by
  unfold inversePowerMean
  simp_rw [mul_div_assoc]
  exact tsum_mul_left

/-- Signed finite combination of scaled divisibility indicators. -/
def qScaledDivisibilitySum (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ S, (a k * (k : ℝ)^2) * (if k ∣ n then (1 : ℝ) else 0)

/-- Exact cancellation of the inverse-square conditioning scale, valid for
every bounded arithmetic observable and all signed coefficients. -/
theorem inversePowerMean_scaled_divisibility_sum
    (f : ℕ → ℝ) {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (S : Finset ℕ) (a : ℕ → ℝ) (hS : ∀ k ∈ S, 0 < k) :
    inversePowerMean 0 (fun n => f n * qScaledDivisibilitySum S a n) =
      ∑ k ∈ S, a k * inversePowerMean 0 (fun n => f (k * n)) := by
  classical
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hf 0)
  have hpoint :
      (fun n => f n * qScaledDivisibilitySum S a n) =
      (fun n => ∑ k ∈ S,
        (a k * (k : ℝ)^2) * (f n * (if k ∣ n then (1 : ℝ) else 0))) := by
    funext n
    unfold qScaledDivisibilitySum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hbound (k n : ℕ) :
      |(a k * (k : ℝ)^2) * (f n * (if k ∣ n then (1 : ℝ) else 0))| ≤
        |a k * (k : ℝ)^2| * C := by
    by_cases hkn : k ∣ n
    · simp only [if_pos hkn, mul_one]
      calc
        |(a k * (k : ℝ)^2) * f n| = |a k * (k : ℝ)^2| * |f n| := abs_mul _ _
        _ ≤ |a k * (k : ℝ)^2| * C :=
          mul_le_mul_of_nonneg_left (hf n) (abs_nonneg (a k * (k : ℝ)^2))
    · simp only [if_neg hkn, mul_zero, abs_zero]
      exact mul_nonneg (abs_nonneg _) hC
  calc
    inversePowerMean 0 (fun n => f n * qScaledDivisibilitySum S a n) =
        ∑ k ∈ S, inversePowerMean 0
          (fun n => (a k * (k : ℝ)^2) *
            (f n * (if k ∣ n then (1 : ℝ) else 0))) := by
      rw [hpoint]
      exact inversePowerMean_finsetSum S _
        (fun k => |a k * (k : ℝ)^2| * C) (fun k _ n => hbound k n)
    _ = ∑ k ∈ S, a k * inversePowerMean 0 (fun n => f (k * n)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [inversePowerMean_const_mul]
      have hi :
          (fun n => f n * (if k ∣ n then (1 : ℝ) else 0)) =
          (fun n => if k ∣ n then f n else 0) := by
        funext n
        split_ifs <;> simp
      rw [hi, inversePowerMean_dvd k (hS k hk)]
      have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hS k hk))
      field_simp [hkR] <;> ring

private theorem residue_bound (d n : ℕ) : |residueFraction d n| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, residueFraction]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hdR).mpr
    simpa only [one_mul] using (show ((n % d : ℕ) : ℝ) ≤ (d : ℝ) by
      exact_mod_cast (Nat.mod_lt n hdpos).le)

/-- Actual residue coefficients of every finite signed incidence combination. -/
theorem residue_scaled_divisibility_sum_mean
    (d : ℕ) (S : Finset ℕ) (a : ℕ → ℝ) (hS : ∀ k ∈ S, 0 < k) :
    inversePowerMean 0
      (fun n => residueFraction d n * qScaledDivisibilitySum S a n) =
      ∑ k ∈ S, a k * qTwistedResidueMean d k := by
  exact inversePowerMean_scaled_divisibility_sum (residueFraction d)
    (residue_bound d) S a hS

/-- The complete arithmetic Möbius wavelet, indexed by all divisors of `r`. -/
def qDivisorWavelet (r n : ℕ) : ℝ :=
  qScaledDivisibilitySum r.divisors
    (fun k => (ArithmeticFunction.moebius (r / k) : ℝ)) n

/-- A finite Möbius difference of the exact twisted Q-means. -/
def qResidueDivisorCoefficient (d r : ℕ) : ℝ :=
  ∑ k ∈ r.divisors,
    (ArithmeticFunction.moebius (r / k) : ℝ) * qTwistedResidueMean d k

/-- The finite divisor formula is the actual mixed moment, including all
physical coordinates. It is not an approximation to the coefficient. -/
theorem residue_divisor_wavelet_mean (d r : ℕ) :
    inversePowerMean 0 (fun n => residueFraction d n * qDivisorWavelet r n) =
      qResidueDivisorCoefficient d r := by
  exact residue_scaled_divisibility_sum_mean d r.divisors
    (fun k => (ArithmeticFunction.moebius (r / k) : ℝ))
    (fun k hk => Nat.pos_of_mem_divisors hk)

end RiemannResearch.RH.ZetaTwoHilbert
