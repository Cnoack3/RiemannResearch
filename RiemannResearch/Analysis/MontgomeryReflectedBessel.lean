/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.MontgomeryComplexGram
import RiemannResearch.Analysis.MontgomeryComplexSchur
import RiemannResearch.Analysis.MontgomeryDifferenceGram
import RiemannResearch.Analysis.MontgomeryHorizontalBessel
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.MontgomeryPoisson
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reflection before estimating the Montgomery defect

The complex statistic is the one of Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh, https://doi.org/10.4064/aa230612-20-3. Reflecting
the spectral signal before the Bessel bound makes its phase-frequency
coefficient quadratic in the horizontal displacement. After squaring,
its contribution to the defect is quartic. The two shifted differences
retain the full remaining terms and have one horizontal factor each.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

open ActualZeroOrdinate MontgomeryComplexGram MontgomeryComplexSchur
open MontgomeryDifferenceGram MontgomeryHorizontalTransfer MontgomeryLocalMass MontgomeryPoisson
open ZeroOrdinate

private theorem shifted_exponential (a t s : ℝ) :
    Complex.exp ((s : ℂ) * shiftedExponent a t) = (Real.exp (s * a) : ℂ) * phase s t := by
  rw [shiftedExponent, mul_add, Complex.exp_add, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  congr 1
  unfold phase
  congr 1
  push_cast
  ring

private theorem reflectedSignal_split {ι : Type*} [Fintype ι]
    (a t : ι → ℝ) (c : ι → ℂ) (u s : ℝ) :
    (∑ i, c i * phase s (t i) * ((Real.cosh ((u + s) * a i) - 1 : ℝ) : ℂ)) =
      complexSignal (fun i => shiftedExponent 0 (t i))
        (fun i => c i * ((Real.cosh (u * a i) - 1 : ℝ) : ℂ)) s +
      differenceSignal a t (fun i => c i * ((Real.exp (u * a i) / 2 : ℝ) : ℂ)) s +
      differenceSignal (fun i => -a i) t (fun i => c i * ((Real.exp (u * -a i) / 2 : ℝ) : ℂ)) s := by
  simp only [complexSignal, differenceSignal_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [shifted_exponential, mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
  rw [Real.cosh_eq, Real.cosh_eq, show (u + s) * a i = u * a i + s * a i by ring,
    neg_add, Real.exp_add, Real.exp_add]
  simp only [mul_neg, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- Exact signed split of the actual reflected signal. -/
theorem coshCorrection_eq_reflected_signals (T u s : ℝ) :
    let a := fun i : Copies T => i.1.1.re - 1 / 2
    let t := copyOrdinate T
    let c := fun i => phase u (t i)
    coshCorrection T (u + s) =
      complexSignal (fun i => shiftedExponent 0 (t i))
        (fun i => c i * ((Real.cosh (u * a i) - 1 : ℝ) : ℂ)) s +
      differenceSignal a t (fun i => c i * ((Real.exp (u * a i) / 2 : ℝ) : ℂ)) s +
      differenceSignal (fun i => -a i) t (fun i => c i * ((Real.exp (u * -a i) / 2 : ℝ) : ℂ)) s := by
  dsimp only
  rw [← reflectedSignal_split]
  have hcosh : coshCorrection T (u + s) = landauSum T (u + s) - ordinateSum T (u + s) := by
    rw [exact_signed_correction]
    ring
  rw [hcosh, landauSum_eq_cosh, ordinateSum, ← sum_sub, sum_eq_copies]
  apply Finset.sum_congr rfl
  intro i _
  rw [phase_add]
  simp only [copyOrdinate, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The squared phase-frequency defect and the two remaining shifted terms. -/
def reflectedHorizontalBudget (T u : ℝ) : ℝ :=
  ∑ i : Copies T,
    let x := i.1.1.re - 1 / 2
    (Real.cosh (u * x) - 1) ^ 2 + x ^ 2 * (Real.exp (2 * (u * x)) + Real.exp (2 * (u * -x)))

theorem reflectedHorizontalBudget_nonneg (T u : ℝ) : 0 ≤ reflectedHorizontalBudget T u := by
  unfold reflectedHorizontalBudget
  positivity

private theorem norm_phase_exp_half_sq (u t a : ℝ) :
    ‖phase u t * ((Real.exp a / 2 : ℝ) : ℂ)‖ ^ 2 = Real.exp (2 * a) / 4 := by
  simp only [norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, div_pow]
  rw [pow_two (Real.exp a), ← Real.exp_add, ← two_mul]
  norm_num

/-- The Cauchy row bound applies after reflection. The square of the
quadratic coefficient replaces the unreflected exponential defect. -/
theorem exists_defectIntegral_le_reflected_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ T u : ℝ, 0 ≤ T →
      defectIntegral T u ≤ C * Real.log (T + 3) * reflectedHorizontalBudget T u := by
  obtain ⟨K, hK, hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨8 * K, by positivity, ?_⟩
  intro T u hT
  let a := fun i : Copies T => i.1.1.re - 1 / 2
  let t := copyOrdinate T
  let c := fun i => phase u (t i)
  let z := fun i => shiftedExponent 0 (t i)
  let bp := fun i => c i * ((Real.exp (u * a i) / 2 : ℝ) : ℂ)
  let bm := fun i => c i * ((Real.exp (u * -a i) / 2 : ℝ) : ℂ)
  let b0 := fun i => c i * ((Real.cosh (u * a i) - 1 : ℝ) : ℂ)
  let F0 := weightedSignal z b0
  let Fp := fun s => (Real.exp (-|s|) : ℂ) * differenceSignal a t bp s
  let Fm := fun s => (Real.exp (-|s|) : ℂ) * differenceSignal (fun i => -a i) t bm s
  let D := K * Real.log (T + 3)
  have hlog : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hD : 0 ≤ D := mul_nonneg hK.le hlog
  have ha (i : Copies T) : |a i| ≤ 1 / 2 := (displacement_lt_half i.1.2).le
  have ham (i : Copies T) : |-a i| ≤ 1 / 2 := by rw [abs_neg]; exact ha i
  have hz (i : Copies T) : |(z i).re| ≤ 1 / 2 := by norm_num [z, shiftedExponent]
  have hrows (i : Copies T) : (∑ j, cauchyWeight (t i - t j)) ≤ D := hrow T hT _
  have hF0 : MemLp F0 2 := weightedSignal_memLp z b0 (fun i => (hz i).trans_lt (by norm_num))
  have hFp : MemLp Fp 2 := weightedDifference_memLp a t bp ha
  have hFm : MemLp Fm 2 := weightedDifference_memLp (fun i => -a i) t bm ham
  let A := ∑ i : Copies T, (Real.cosh (u * a i) - 1) ^ 2
  let P := ∑ i : Copies T, (a i) ^ 2 * Real.exp (2 * (u * a i))
  let M := ∑ i : Copies T, (a i) ^ 2 * Real.exp (2 * (u * -a i))
  have h0 : (∫ s : ℝ, ‖F0 s‖ ^ 2) ≤ (4 / 3) * D * A := by
    have h := complex_signal_energy_le_of_rows z b0 D hz (by
      intro i
      simpa only [z, shiftedExponent, Complex.add_im, Complex.ofReal_im, zero_add,
        Complex.I_im, Complex.I_re, Complex.mul_im, Complex.ofReal_re, one_mul, mul_one, mul_zero, add_zero]
        using hrows i)
    have hnorm (i : Copies T) : ‖b0 i‖ ^ 2 = (Real.cosh (u * a i) - 1) ^ 2 := by
      simp only [b0, c, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simpa only [F0, weightedSignal_sq, A, hnorm] using h
  have hp : (∫ s : ℝ, ‖Fp s‖ ^ 2) ≤ D * P := by
    have h := difference_energy_le_of_rows a t bp D ha hrows
    simp only [bp, c, norm_phase_exp_half_sq] at h
    rw [show D * P = 4 * D * ∑ i : Copies T, (Real.exp (2 * (u * a i)) / 4) * (a i) ^ 2 by
      dsimp only [P]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    simpa only [Fp, weighted_mul_sq] using h
  have hm : (∫ s : ℝ, ‖Fm s‖ ^ 2) ≤ D * M := by
    have h := difference_energy_le_of_rows (fun i => -a i) t bm D ham hrows
    simp only [bm, c, norm_phase_exp_half_sq, neg_sq] at h
    rw [show D * M =
        4 * D * ∑ i : Copies T, (Real.exp (2 * (u * -a i)) / 4) * (a i) ^ 2 by
      dsimp only [M]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    simpa only [Fm, weighted_mul_sq] using h
  have hsplit : defectIntegral T u = ∫ s : ℝ, ‖(F0 s + Fp s) + Fm s‖ ^ 2 := by
    unfold defectIntegral
    apply integral_congr_ae
    filter_upwards with s
    rw [← weighted_mul_sq, coshCorrection_eq_reflected_signals]
    simp only [F0, Fp, Fm, weightedSignal, a, t, z, c, b0, bp, bm, mul_add]
  have houter := energy_add_le_twice (hF0.add hFp) hFm
  have hinner := energy_add_le_twice hF0 hFp
  have hsum : reflectedHorizontalBudget T u = A + P + M := by
    simp only [reflectedHorizontalBudget, a, A, P, M, mul_add, Finset.sum_add_distrib, add_assoc]
  have hnA : 0 ≤ D * A := by dsimp [A]; positivity
  have hnP : 0 ≤ D * P := by dsimp [P]; positivity
  have hnM : 0 ≤ D * M := by dsimp [M]; positivity
  rw [hsplit, hsum, show 8 * K * Real.log (T + 3) = 8 * D by dsimp [D]; ring]
  simp only [Pi.add_apply] at houter
  nlinarith only [houter, hinner, h0, hp, hm, hnA, hnP, hnM]

theorem exists_horizontalDefect_le_reflected_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ T α : ℝ, 9 ≤ T →
      horizontalDefect T α ≤ C * reflectedHorizontalBudget T (α * Real.log T) / T := by
  obtain ⟨A, hA, hb⟩ := exists_defectIntegral_le_reflected_budget
  refine ⟨4 * Real.pi * A, by positivity, ?_⟩
  intro T α hT
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : Real.log (T + 3) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T * T) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul ht.ne' ht.ne']; ring
  unfold horizontalDefect
  apply (div_le_iff₀ (by positivity : 0 < T * Real.log T / (2 * Real.pi))).2
  calc
    _ ≤ A * Real.log (T + 3) * reflectedHorizontalBudget T (α * Real.log T) := hb T _ ht.le
    _ ≤ A * (2 * Real.log T) * reflectedHorizontalBudget T (α * Real.log T) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hA.le)
        (reflectedHorizontalBudget_nonneg _ _)
    _ = _ := by field_simp [ht.ne', hl.ne', Real.pi_ne_zero]; ring

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
