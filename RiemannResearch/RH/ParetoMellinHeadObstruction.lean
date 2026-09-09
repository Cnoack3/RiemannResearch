import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.Tactic.LinearCombination

/-!
# Exact Mellin lower bounds for finite-head interpolation

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2, equation (47). The Mellin functional and Cauchy estimate are
proved for the actual weighted Hilbert space. The only arithmetic premise
of the lower bound is the explicitly stated vanishing of that functional.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
noncomputable section

private theorem physical_head_one {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    {x : ℝ} (hx : x ∈ Ico (1 : ℝ) ((N : ℝ) + 1)) :
    hilbertSequence f ⌊x⌋₊ = 1 := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx.1
  have hlow : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx.1)
  have hhigh : ⌊x⌋₊ < N + 1 := (Nat.floor_lt hx0).2 (by exact_mod_cast hx.2)
  exact hhead _ (by omega) (by omega)

private theorem head_mellin_integral {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∫ x in (1 : ℝ)..((N : ℝ) + 1),
      mellinWeightedStep f x * paretoMellinKernel s x) =
      (1 - ((N : ℂ) + 1)^(-s)) / s := by
  have hab : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hp : -s - 1 ≠ (-1 : ℂ) := by intro h; apply hs0; linear_combination -h
  have hz : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((N : ℝ) + 1) := by
    rw [Set.uIcc_of_le hab]
    intro h
    norm_num at h
  calc
    _ = ∫ x in (1 : ℝ)..((N : ℝ) + 1), (x : ℂ)^(-s-1) := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
        ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
      rw [Complex.cpow_sub (-s) 1 hx0, Complex.cpow_one]
      unfold mellinWeightedStep paretoMellinKernel
      rw [physical_head_one hhead hx]
      norm_num
      ring
    _ = _ := by
      rw [integral_cpow (Or.inr ⟨hp, hz⟩)]
      simp only [sub_add_cancel, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one, Complex.one_cpow]
      ring

private theorem head_energy_integral {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    (∫ x in (1 : ℝ)..((N : ℝ) + 1), ‖mellinWeightedStep f x‖ ^ 2) =
      (N : ℝ) / ((N : ℝ) + 1) := by
  have hab : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hz : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((N : ℝ) + 1) := by
    rw [Set.uIcc_of_le hab]
    intro h
    norm_num at h
  calc
    _ = ∫ x in (1 : ℝ)..((N : ℝ) + 1), x ^ (-2 : ℤ) := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
        ← integral_Ico_eq_integral_Ioc, ← integral_Ico_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      rw [mellinWeightedStep_norm_sq, physical_head_one hhead hx]
      simp
    _ = _ := by
      rw [integral_zpow (Or.inr ⟨by norm_num, hz⟩)]
      norm_num
      field_simp
      ring

/-- Exact split of the full norm: the finite head and complete continuous tail. -/
theorem paretoMellin_head_tail_energy {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    ‖f‖ ^ 2 = (N : ℝ) / ((N : ℝ) + 1) +
      ∫ x in Ioi ((N : ℝ) + 1), ‖mellinWeightedStep f x‖ ^ 2 := by
  have hfull : IntegrableOn (fun x => ‖mellinWeightedStep f x‖ ^ 2) (Ioi (1 : ℝ)) :=
    (mellinWeightedStep_memLp f).norm.integrable_sq
  have htail := hfull.mono_set (Ioi_subset_Ioi
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ (N : ℝ) + 1))
  have h := intervalIntegral.integral_interval_add_Ioi hfull htail
  rw [head_energy_integral hhead, mellinWeightedStep_energy] at h
  exact h.symm

/-- The head signature cannot disappear; nullity forces its exact negative into the tail. -/
theorem paretoMellin_tail_signature {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hnull : paretoMellin f s = 0) :
    (∫ x in Ioi ((N : ℝ) + 1), mellinWeightedStep f x * paretoMellinKernel s x) =
      -((1 - ((N : ℂ) + 1)^(-s)) / s) := by
  have hfull := paretoMellin_integrable f s hs
  have htail := hfull.mono_set (Ioi_subset_Ioi
    (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1 : ℝ) ≤ (N : ℝ) + 1))
  have h := intervalIntegral.integral_interval_add_Ioi hfull htail
  rw [head_mellin_integral hhead s hs] at h
  change (1 - ((N : ℂ) + 1)^(-s)) / s + _ = paretoMellin f s at h
  rw [hnull] at h
  linear_combination h

/-- Equation (47), for the actual complete Pareto norm and actual Mellin nullity. -/
theorem paretoMellin_exact_head_lower_bound {f : ThresholdHilbert} {N : ℕ}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hnull : paretoMellin f s = 0) :
    (N : ℝ) / ((N : ℝ) + 1) +
      ((2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) / ‖s‖ ^ 2) *
        ‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hb : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hb0 : 0 < (N : ℝ) + 1 := by positivity
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hp : 0 < ((N : ℝ) + 1) ^ (2 * s.re - 1) := Real.rpow_pos_of_pos hb0 _
  have h := paretoMellin_tail_norm_sq_le f s hs hb
  rw [paretoMellin_tail_signature hhead s hs hnull, norm_neg] at h
  have hm := mul_le_mul_of_nonneg_left h (mul_nonneg hd.le hp.le)
  have he : (2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) *
      ((∫ x in Ioi ((N : ℝ) + 1), ‖mellinWeightedStep f x‖ ^ 2) *
        (((N : ℝ) + 1) ^ (1 - 2 * s.re) / (2 * s.re - 1))) =
      ∫ x in Ioi ((N : ℝ) + 1), ‖mellinWeightedStep f x‖ ^ 2 := by
    rw [show 1 - 2 * s.re = -(2 * s.re - 1) by ring,
      Real.rpow_neg hb0.le]
    field_simp [hd.ne', hp.ne']
  rw [he, norm_div, div_pow] at hm
  rw [paretoMellin_head_tail_energy hhead]
  have he' : (2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) *
      (‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 / ‖s‖ ^ 2) =
      ((2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) / ‖s‖ ^ 2) *
        ‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 := by ring
  rw [he'] at hm
  exact add_le_add le_rfl hm

/-- On the artificial-zero line Re(s)=1 the complete lower bound entails
an explicit linear cost for every nonempty exact head. -/
theorem paretoMellin_exact_head_linear_lower {f : ThresholdHilbert} {N : ℕ}
    (hN : 0 < N)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (s : ℂ) (hs : s.re = 1) (hnull : paretoMellin f s = 0) :
    ((N : ℝ) + 1) / (4 * ‖s‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have hhalf : (1 / 2 : ℝ) < s.re := by rw [hs]; norm_num
  have hb : 2 ≤ (N : ℝ) + 1 := by exact_mod_cast (show 2 ≤ N + 1 by omega)
  have hb0 : 0 < (N : ℝ) + 1 := by positivity
  have hmode : ‖((N : ℂ) + 1)^(-s)‖ = 1 / ((N : ℝ) + 1) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hb0 (-s)
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Complex.neg_re, hs, Real.rpow_neg_one, one_div] using h
  have hinv : 1 / ((N : ℝ) + 1) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hb0 (by norm_num : (0 : ℝ) < 2)).2
    linarith
  have hrev := norm_sub_norm_le (1 : ℂ) (((N : ℂ) + 1)^(-s))
  rw [norm_one, hmode] at hrev
  have hdiff : (1 / 2 : ℝ) ≤ ‖1 - ((N : ℂ) + 1)^(-s)‖ := by linarith
  have hsq : (1 / 4 : ℝ) ≤ ‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 := by nlinarith
  have h := paretoMellin_exact_head_lower_bound hhead s hhalf hnull
  rw [hs] at h
  norm_num only [show (2 : ℝ) * 1 - 1 = 1 by norm_num, Real.rpow_one, one_mul] at h
  have hmul := mul_le_mul_of_nonneg_left hsq
    (by positivity : 0 ≤ ((N : ℝ) + 1) / ‖s‖ ^ 2)
  have hheadpos : 0 ≤ (N : ℝ) / ((N : ℝ) + 1) := by positivity
  have he : (((N : ℝ) + 1) / ‖s‖ ^ 2) * (1 / 4) =
      ((N : ℝ) + 1) / (4 * ‖s‖ ^ 2) := by ring
  rw [he] at hmul
  linarith

end
end RiemannResearch.RH.Pareto
