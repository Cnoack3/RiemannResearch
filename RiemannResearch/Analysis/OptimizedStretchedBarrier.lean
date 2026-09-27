/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DelayedContraction
import RiemannResearch.NumberTheory.PrimeNumberTheorem.OptimizedStretchedShift
import RiemannResearch.NumberTheory.PrimeNumberTheorem.OptimizedStretchedAsymptotics

/-!
# The uniform optimized stretched exponential barrier

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

def optimizedLogProfile (T : ℝ) : ℝ :=
  ((T + 6) * Real.log (T + 6)) ^ ((1 : ℝ) / 11)

theorem optimizedLogProfile_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    optimizedLogProfile u ≤ optimizedLogProfile v := by
  have hu6 : 0 < u + 6 := by linarith
  have hv6 : 0 < v + 6 := by linarith
  have hlu : 0 ≤ Real.log (u + 6) := Real.log_nonneg (by linarith)
  have hlv : 0 ≤ Real.log (v + 6) := Real.log_nonneg (by linarith)
  apply Real.rpow_le_rpow (mul_nonneg hu6.le hlu) _ (by norm_num)
  exact mul_le_mul (by linarith : u + 6 ≤ v + 6)
    (Real.log_le_log hu6 (by linarith)) hlu hv6.le

/-- Uniform delayed-contraction transfer, retaining the optimized
(logarithm times iterated logarithm) scale. All assumptions here are analytic. -/
theorem optimized_stretched_envelope_bound_of_cutoffs
    (E : ℝ → ℝ) (c D K d : ℝ)
    (hE0 : ∀ t : ℝ, 0 ≤ E t) (hE1 : ∀ t : ℝ, E t ≤ 1)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hd : 0 < d) (hdc : d ≤ c) (hd1 : d ≤ 1)
    (hrec : ∀ T L : ℝ, 0 < T → 0 ≤ L → Real.log 2 ≤ T - L →
      E T ≤ ((3 * L + K) * E (T - L - Real.log 2) +
        3 * Real.exp (-L) + 3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) / T)
    (hcut : ∀ᶠ T : ℝ in atTop,
      6 ≤ T ∧ 1 ≤ optimizedLogProfile T ∧
      2 * (Real.log (T + 6) + 1) ≤ optimizedLogProfile T ∧
      (T + 6) / 2 ≤ T + 6 - (optimizedLogProfile T) ^ 10 - Real.log 2 ∧
      ((3 * (optimizedLogProfile T) ^ 10 + K) / T) *
        Real.exp (2 * d * (Real.log (T + 6) + 1)) ≤ 1 / 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      E T ≤ B * Real.exp (-d * optimizedLogProfile T) := by
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hcut
  let T₀ : ℝ := max T₁ 6
  let F : ℝ → ℝ := fun t => E t * Real.exp (d * optimizedLogProfile t)
  let r : ℝ → ℝ := fun t => t - (optimizedLogProfile t) ^ 10 - Real.log 2
  have hF0 (t : ℝ) : 0 ≤ F t := mul_nonneg (hE0 t) (Real.exp_pos _).le
  have hlog20 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hfacts (t : ℝ) (ht : T₀ < t) := hT₁ t ((le_max_left T₁ 6).trans ht.le)
  have hdelay (t : ℝ) (ht : T₀ < t) : 0 ≤ r t ∧ r t ≤ t - 1 := by
    obtain ⟨ht6, hz, _, hv, _⟩ := hfacts t ht
    have hz10 : 1 ≤ (optimizedLogProfile t) ^ 10 := one_le_pow₀ hz
    dsimp [r]
    constructor <;> linarith
  have hstep (t : ℝ) (ht : T₀ < t) : F t ≤ (1 / 2 : ℝ) * F (r t) + (3 + 3 * D) := by
    obtain ⟨ht6, hz, hh, hv, ha⟩ := hfacts t ht
    let z := optimizedLogProfile t
    let L := z ^ 10
    have hz0 : 0 ≤ z := le_trans zero_le_one hz
    have ht0 : 0 < t := by linarith
    have hL0 : 0 ≤ L := pow_nonneg hz0 _
    have hr0 := (hdelay t ht).1
    have hTL : Real.log 2 ≤ t - L := by change 0 ≤ t - L - Real.log 2 at hr0; linarith
    have hshift := (RiemannResearch.NumberTheory.PrimeNumberTheorem.optimized_stretched_shift
      (t + 6) (by linarith) hz hh hv).2
    have hshift' : z - optimizedLogProfile (r t) ≤ 2 * (Real.log (t + 6) + 1) := by
      simpa only [z, optimizedLogProfile, r, sub_add_eq_add_sub, sub_sub] using hshift
    have hweight : E (r t) * Real.exp (d * z) ≤
        F (r t) * Real.exp (2 * d * (Real.log (t + 6) + 1)) := by
      have he : Real.exp (d * z) = Real.exp (d * optimizedLogProfile (r t)) *
          Real.exp (d * (z - optimizedLogProfile (r t))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      dsimp [F]
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hF0 (r t))
      apply Real.exp_le_exp.mpr
      nlinarith
    have hzL : z ≤ L := by
      have hz9 : 1 ≤ z ^ 9 := one_le_pow₀ hz
      have hm := mul_le_mul_of_nonneg_left hz9 hz0
      dsimp [L]
      nlinarith
    have hLroot : L ^ ((1 : ℝ) / 10) = z := by
      dsimp [L]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0]
      norm_num
    have hfirst : Real.exp (-L) * Real.exp (d * z) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.mpr
      have hh := mul_le_mul_of_nonneg_right hd1 hz0
      nlinarith
    have hsecond : Real.exp (-c * L ^ ((1 : ℝ) / 10)) * Real.exp (d * z) ≤ 1 := by
      rw [hLroot, ← Real.exp_add]
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_le_mul_of_nonneg_right hdc hz0]
    have hA0 : 0 ≤ 3 * L + K := by positivity
    have hsource := mul_le_mul_of_nonneg_right (hrec t L ht0 hL0 hTL)
      (Real.exp_pos (d * z)).le
    calc
      F t ≤ (((3 * L + K) * E (r t) + 3 * Real.exp (-L) +
          3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) / t) * Real.exp (d * z) := hsource
      _ = ((3 * L + K) * (E (r t) * Real.exp (d * z)) +
          3 * (Real.exp (-L) * Real.exp (d * z)) +
          3 * D * (Real.exp (-c * L ^ ((1 : ℝ) / 10)) * Real.exp (d * z))) / t := by ring
      _ ≤ ((3 * L + K) * (F (r t) * Real.exp (2 * d * (Real.log (t + 6) + 1))) +
          3 + 3 * D) / t := by
        apply div_le_div_of_nonneg_right _ ht0.le
        have h1 := mul_le_mul_of_nonneg_left hweight hA0
        have h2 := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 3 * D by positivity)
        linarith
      _ = (((3 * L + K) / t) * Real.exp (2 * d * (Real.log (t + 6) + 1))) *
          F (r t) + (3 + 3 * D) / t := by ring
      _ ≤ (1 / 2 : ℝ) * F (r t) + (3 + 3 * D) :=
        add_le_add (mul_le_mul_of_nonneg_right ha (hF0 _))
          (div_le_self (by positivity) (by linarith))
  have hbase (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T₀) :
      F t ≤ Real.exp (d * optimizedLogProfile T₀) := by
    calc
      F t ≤ Real.exp (d * optimizedLogProfile t) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hE1 t) (Real.exp_pos _).le
      _ ≤ _ := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (optimizedLogProfile_mono ht0 htT) hd.le)
  let B := max (Real.exp (d * optimizedLogProfile T₀)) (2 * (3 + 3 * D))
  have hB : 0 ≤ B := (Real.exp_pos _).le.trans (le_max_left _ _)
  refine ⟨B, hB, fun T hT => ?_⟩
  have h := delayed_contraction_bound F r T₀ _ (3 + 3 * D) hbase hdelay hstep T hT
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-d * optimizedLogProfile T)).le
  have he : Real.exp (d * optimizedLogProfile T) * Real.exp (-d * optimizedLogProfile T) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  simpa only [F, mul_assoc, he, mul_one] using hh


/-- The optimized unconditional analytic transfer. Its hypotheses are exactly
positivity, a global envelope bound, and the finite tail-envelope recurrence. -/
theorem optimized_stretched_envelope_bound
    (E : ℝ → ℝ) (c D K : ℝ) (hc : 0 < c) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hE0 : ∀ t : ℝ, 0 ≤ E t) (hE1 : ∀ t : ℝ, E t ≤ 1)
    (hrec : ∀ T L : ℝ, 0 < T → 0 ≤ L → Real.log 2 ≤ T - L →
      E T ≤ ((3 * L + K) * E (T - L - Real.log 2) +
        3 * Real.exp (-L) + 3 * D * Real.exp (-c * L ^ ((1 : ℝ) / 10))) / T) :
    ∃ d : ℝ, 0 < d ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      E T ≤ B * Real.exp (-d * optimizedLogProfile T) := by
  let d := min (c / 2) (1 / 100 : ℝ)
  have hd : 0 < d := lt_min (by linarith) (by norm_num)
  have hdc : d ≤ c := (min_le_left _ _).trans (by linarith)
  have hdsmall : d ≤ (1 / 100 : ℝ) := min_le_right _ _
  have hd1 : d ≤ 1 := by linarith
  refine ⟨d, hd, ?_⟩
  apply optimized_stretched_envelope_bound_of_cutoffs E c D K d hE0 hE1 hD hK hd hdc hd1 hrec
  exact RiemannResearch.NumberTheory.PrimeNumberTheorem.optimized_stretched_cutoff_atTop
    K d hK hd hdsmall

end RiemannResearch.Analysis
