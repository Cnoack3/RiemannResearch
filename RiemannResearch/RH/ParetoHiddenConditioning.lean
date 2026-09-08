import RiemannResearch.RH.ParetoHiddenNoise
import RiemannResearch.RH.ParetoGeometricTransform
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact conditioning of the hidden-noise family

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, §6.
This module evaluates the genuine infinite geometric transform, preserving the
positive-coordinate shift.  No beta-integral or limiting interchange is assumed.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem squareWave_abs_le (n k : ℕ) : |squareWave n k| ≤ 1 := by
  unfold squareWave
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  have h : k / n % 2 ≤ 1 := by omega
  exact_mod_cast h

theorem squareWave_add (n k : ℕ) (hn : 0 < n) :
    squareWave n (k + n) = 1 - squareWave n k := by
  unfold squareWave
  rw [Nat.add_div_right k hn]
  have h : ((k / n + 1) % 2) + (k / n % 2) = 1 := by omega
  have h' : (((k / n + 1) % 2 : ℕ) : ℝ) + ((k / n % 2 : ℕ) : ℝ) = 1 := by
    exact_mod_cast h
  linarith

theorem squareWave_geometricTransform (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1) :
    geometricTransform (squareWave n) t = t ^ n / (1 + t ^ n) := by
  have hs := (geometricTransform_norm_summable (squareWave_abs_le n) ht).of_norm
  have hshift := hs.sum_add_tsum_nat_add n
  have hhead : (∑ k ∈ Finset.range n,
      squareWave n k * geometricProbability k t) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [squareWave, Nat.div_eq_of_lt (Finset.mem_range.mp hk)]
  have htail : (∑' k, squareWave n (k + n) * geometricProbability (k + n) t) =
      t ^ n * (1 - geometricTransform (squareWave n) t) := by
    calc
      _ = ∑' k, t ^ n * ((1 - squareWave n k) * geometricProbability k t) := by
        apply tsum_congr
        intro k
        rw [squareWave_add n k hn]
        simp only [geometricProbability, pow_add]
        ring
      _ = t ^ n * geometricTransform (fun k => 1 - squareWave n k) t := by
        rw [tsum_mul_left]
        rfl
      _ = _ := by rw [geometricTransform_one_sub (squareWave_abs_le n) ht]
  rw [hhead, zero_add, htail] at hshift
  change t ^ n * (1 - geometricTransform (squareWave n) t) =
    geometricTransform (squareWave n) t at hshift
  have ht0 : 0 ≤ t := ht.1
  have hden : 1 + t ^ n ≠ 0 := by positivity
  apply (eq_div_iff hden).2
  change geometricTransform (squareWave n) t * (1 + t ^ n) = t ^ n
  nlinarith [hshift]

theorem squareWave_geometricTransform_positive (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    geometricTransform (fun k => squareWave n (k + 1)) t =
      t ^ (n - 1) / (1 + t ^ n) := by
  have ht' : t ∈ Set.Ico 0 1 := ⟨ht.1.le, ht.2⟩
  have hs := (geometricTransform_norm_summable (squareWave_abs_le n) ht').of_norm
  have hshift := hs.sum_add_tsum_nat_add 1
  have hhead : (∑ k ∈ Finset.range 1,
      squareWave n k * geometricProbability k t) = 0 := by simp [squareWave]
  have htail : (∑' k, squareWave n (k + 1) * geometricProbability (k + 1) t) =
      t * geometricTransform (fun k => squareWave n (k + 1)) t := by
    calc
      _ = ∑' k, t * (squareWave n (k + 1) * geometricProbability k t) := by
        apply tsum_congr
        intro k
        simp only [geometricProbability, pow_succ]
        ring
      _ = _ := by rw [tsum_mul_left]; rfl
  rw [hhead, zero_add, htail] at hshift
  change t * geometricTransform (fun k => squareWave n (k + 1)) t =
    geometricTransform (squareWave n) t at hshift
  rw [squareWave_geometricTransform n hn ht'] at hshift
  have ht0 : 0 ≤ t := ht.1.le
  have hden : 1 + t ^ n ≠ 0 := by positivity
  have hpow : t ^ n = t * t ^ (n - 1) := by
    calc
      t ^ n = t ^ ((n - 1) + 1) := by congr 1; omega
      _ = t * t ^ (n - 1) := by rw [pow_succ]; ring
  apply (mul_left_cancel₀ (ne_of_gt ht.1))
  rw [hshift, hpow]
  ring

theorem hiddenNoise_geometricTransform (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    geometricTransform (fun k => hiddenNoise n (k + 1)) t =
      ((n : ℝ) + 2) * t ^ (n + 1) / (1 + t ^ (n + 2)) -
      (n : ℝ) * t ^ (n - 1) / (1 + t ^ n) := by
  have ht' : t ∈ Set.Ico 0 1 := ⟨ht.1.le, ht.2⟩
  have ha := (geometricTransform_norm_summable
    (fun k => squareWave_abs_le (n + 2) (k + 1)) ht').of_norm
  have hb := (geometricTransform_norm_summable
    (fun k => squareWave_abs_le n (k + 1)) ht').of_norm
  have hterm (k : ℕ) : hiddenNoise n (k + 1) * geometricProbability k t =
      ((n : ℝ) + 2) * (squareWave (n + 2) (k + 1) * geometricProbability k t) -
      (n : ℝ) * (squareWave n (k + 1) * geometricProbability k t) := by
    rw [hiddenNoise_squareWave]
    ring
  unfold geometricTransform
  simp_rw [hterm]
  rw [(ha.mul_left ((n : ℝ) + 2)).tsum_sub (hb.mul_left (n : ℝ)),
    tsum_mul_left, tsum_mul_left]
  change ((n : ℝ) + 2) * geometricTransform (fun k => squareWave (n + 2) (k + 1)) t -
    (n : ℝ) * geometricTransform (fun k => squareWave n (k + 1)) t = _
  rw [squareWave_geometricTransform_positive (n + 2) (by omega) ht,
    squareWave_geometricTransform_positive n hn ht]
  have he : n + 2 - 1 = n + 1 := by omega
  rw [he]
  ring

/-- The Fermi profile controlling the rescaled conditional means. -/
def hiddenConditioningProfile (x : ℝ) : ℝ := x / (Real.exp x + 1)

/-- Exact derivative, before any dominated-convergence estimate. -/
theorem hiddenConditioningProfile_hasDerivAt (x : ℝ) :
    HasDerivAt hiddenConditioningProfile
      ((Real.exp x + 1 - x * Real.exp x) / (Real.exp x + 1)^2) x := by
  unfold hiddenConditioningProfile
  convert (hasDerivAt_id x).div ((Real.hasDerivAt_exp x).add_const 1)
    (show Real.exp x + 1 ≠ 0 by positivity) using 1 <;>
    first | rfl | (simp only [id_eq, one_mul] <;> ring)

end
end RiemannResearch.RH.Pareto
