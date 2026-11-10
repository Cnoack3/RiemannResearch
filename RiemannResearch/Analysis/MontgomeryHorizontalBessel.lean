/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryDifferenceGram
import RiemannResearch.Analysis.MontgomeryComplexSchur
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import Mathlib.Tactic.GCongr
/-! # Bessel control of the actual horizontal defect
Source: the actual-zero Gram and reflection framework of
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh (2024),
https://doi.org/10.4064/aa230612-20-3, and route B of the user handoff.
The new estimate uses the exact mixed resolvent difference and the proved
unconditional local zero count. No RH, density input, or asymptotic is assumed.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryPoisson MontgomeryComplexGram MontgomeryComplexSchur
open MontgomeryDifferenceGram MontgomeryLocalMass MontgomeryHorizontalTransfer
open ActualZeroOrdinate ZeroOrdinate
variable {ι : Type*} [Fintype ι]

def shiftedDifferenceSignal (a t : ι → ℝ) (c : ι → ℂ) (u s : ℝ) : ℂ :=
  complexSignal (fun i => shiftedExponent (a i) (t i))
    (fun i => c i * (Real.exp (u*a i) : ℂ)) s -
  complexSignal (fun i => shiftedExponent 0 (t i)) c s

/-- The complete signed splitting; the second term must not be discarded. -/
theorem shiftedDifferenceSignal_split (a t : ι → ℝ) (c : ι → ℂ) (u s : ℝ) :
    shiftedDifferenceSignal a t c u s =
      complexSignal (fun i => shiftedExponent (a i) (t i))
        (fun i => c i * ((Real.exp (u*a i) : ℂ)-1)) s +
      differenceSignal a t c s := by
  simp only [shiftedDifferenceSignal, differenceSignal, complexSignal,
    mul_sub, mul_one, sub_mul, Finset.sum_sub_distrib]
  ring

theorem energy_add_le_twice {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2) :
    (∫ s : ℝ, ‖f s+g s‖^2) ≤
      2*(∫ s : ℝ, ‖f s‖^2)+2*(∫ s : ℝ, ‖g s‖^2) := by
  have h := sqrt_energy_add_le hf hg
  have h1 : 0 ≤ (∫ s : ℝ, ‖f s‖^2) := integral_nonneg (fun s => sq_nonneg _)
  have h2 : 0 ≤ (∫ s : ℝ, ‖g s‖^2) := integral_nonneg (fun s => sq_nonneg _)
  have h3 : 0 ≤ (∫ s : ℝ, ‖f s+g s‖^2) := integral_nonneg (fun s => sq_nonneg _)
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt h3] at hs
  nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2,
    sq_nonneg (Real.sqrt (∫ s : ℝ, ‖f s‖^2)-Real.sqrt (∫ s : ℝ, ‖g s‖^2))]

theorem shiftedDifference_energy_le (a t : ι → ℝ) (c : ι → ℂ) (u D : ℝ)
    (hD : 0 ≤ D) (ha : ∀ i, |a i| ≤ 1 / 2)
    (hrow : ∀ i, (∑ j, cauchyWeight (t i-t j)) ≤ D) :
    (∫ s : ℝ, Real.exp (-2*|s|)*‖shiftedDifferenceSignal a t c u s‖^2) ≤
      8*D*∑ i, ‖c i‖^2*((Real.exp (u*a i)-1)^2+(a i)^2) := by
  let z := fun i => shiftedExponent (a i) (t i)
  let b := fun i => c i*((Real.exp (u*a i) : ℂ)-1)
  have hz : ∀ i, |(z i).re| ≤ 1 / 2 := by simpa [z] using ha
  have hA := weightedSignal_memLp z b (fun i => (hz i).trans_lt (by norm_num))
  have hB := weightedDifference_memLp a t c ha
  have hadd := energy_add_le_twice hA hB
  have he (s : ℝ) : weightedSignal z b s +
      (Real.exp (-|s|) : ℂ)*differenceSignal a t c s =
      (Real.exp (-|s|) : ℂ)*shiftedDifferenceSignal a t c u s := by
    rw [shiftedDifferenceSignal_split]
    simp only [weightedSignal, mul_add, z, b]
  simp only [he, weightedSignal_sq, weighted_mul_sq] at hadd
  have hfirst := complex_signal_energy_le_of_rows z b D hz (by simpa [z] using hrow)
  have hsecond := difference_energy_le_of_rows a t c D ha hrow
  have hb (i : ι) : ‖b i‖^2 = ‖c i‖^2*(Real.exp (u*a i)-1)^2 := by
    simp only [b, norm_mul, mul_pow]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hb] at hfirst
  have hn : 0 ≤ ∑ i, ‖c i‖^2*(Real.exp (u*a i)-1)^2 := by positivity
  have hDn := mul_nonneg hD hn
  have hs : (∑ i, ‖c i‖^2*((Real.exp (u*a i)-1)^2+(a i)^2)) =
      (∑ i, ‖c i‖^2*(Real.exp (u*a i)-1)^2)+(∑ i, ‖c i‖^2*(a i)^2) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hs]
  nlinarith only [hadd, hfirst, hsecond, hDn]

def horizontalBudget (T u : ℝ) : ℝ :=
  ∑ i : Copies T, ((Real.exp (u*(i.1.1.re-1 / 2))-1)^2+(i.1.1.re-1 / 2)^2)

theorem horizontalBudget_nonneg (T u : ℝ) : 0 ≤ horizontalBudget T u := by
  unfold horizontalBudget
  positivity

theorem actual_shiftedDifferenceSignal (T u s : ℝ) :
    shiftedDifferenceSignal (fun i : Copies T => i.1.1.re-1 / 2)
      (copyOrdinate T) (fun i => phase u (copyOrdinate T i)) u s =
        coshCorrection T (u+s) := by
  unfold shiftedDifferenceSignal
  have hfirst :
      complexSignal (fun i : Copies T => shiftedExponent (i.1.1.re-1 / 2) (copyOrdinate T i))
        (fun i => phase u (copyOrdinate T i) * (Real.exp (u*(i.1.1.re-1 / 2)) : ℂ)) s =
        landauSum T (u+s) := by
    unfold complexSignal landauSum
    rw [sum_eq_copies]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [phase, shiftedExponent, copyOrdinate, Complex.ofReal_exp,
      ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hsecond :
      complexSignal (fun i : Copies T => shiftedExponent 0 (copyOrdinate T i))
        (fun i => phase u (copyOrdinate T i)) s = ordinateSum T (u+s) := by
    unfold complexSignal ordinateSum
    rw [sum_eq_copies]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [phase, shiftedExponent, copyOrdinate, Complex.ofReal_zero, zero_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfirst, hsecond, exact_signed_correction]
  ring

/-- An unconditional bound linear in the weighted one-point displacement budget. -/
theorem exists_defectIntegral_le_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ T u : ℝ, 0 ≤ T →
      defectIntegral T u ≤ C*Real.log (T+3)*horizontalBudget T u := by
  obtain ⟨A, hA, hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨8*A, by positivity, ?_⟩
  intro T u hT
  have hl : 0 ≤ Real.log (T+3) := Real.log_nonneg (by linarith)
  have h := shiftedDifference_energy_le
    (fun i : Copies T => i.1.1.re-1 / 2) (copyOrdinate T)
    (fun i => phase u (copyOrdinate T i)) u (A*Real.log (T+3)) (by positivity)
    (fun i => (displacement_lt_half i.1.2).le) (fun i => hrow T hT _)
  simpa only [actual_shiftedDifferenceSignal, phase_norm, one_pow, one_mul,
    horizontalBudget, defectIntegral, mul_assoc] using h

/-- Exact Montgomery normalization, with a constant uniform in all frequencies. -/
theorem exists_horizontalDefect_le_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ T α : ℝ, 9 ≤ T →
      horizontalDefect T α ≤ C * horizontalBudget T (α*Real.log T) / T := by
  obtain ⟨A, hA, hb⟩ := exists_defectIntegral_le_budget
  refine ⟨4*Real.pi*A, by positivity, ?_⟩
  intro T α hT
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : Real.log (T+3) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (T*T) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul ht.ne' ht.ne']; ring
  unfold horizontalDefect
  apply (div_le_iff₀ (by positivity : 0 < T*Real.log T/(2*Real.pi))).mpr
  calc
    _ ≤ A*Real.log (T+3)*horizontalBudget T (α*Real.log T) := hb T _ ht.le
    _ ≤ A*(2*Real.log T)*horizontalBudget T (α*Real.log T) := by
      gcongr
      exact horizontalBudget_nonneg _ _
    _ = _ := by field_simp; ring

theorem abs_exp_sub_one_le (x : ℝ) :
    |Real.exp x-1| ≤ |x| *Real.exp |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx))]
    have h := mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg x) (Real.exp_nonneg x)
    rw [← Real.exp_add] at h
    norm_num at h
    nlinarith
  · have hx0 : x < 0 := lt_of_not_ge hx
    have he : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx0.le
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_neg hx0]
    have hb : 1-Real.exp x ≤ -x := by linarith [Real.add_one_le_exp x]
    have hge : 1 ≤ Real.exp (-x) := Real.one_le_exp_iff.mpr (by linarith)
    nlinarith

def exponentialMoment (T v : ℝ) : ℝ :=
  ∑ i : Copies T, (i.1.1.re-1 / 2)^2 * Real.exp (2*v*|i.1.1.re-1 / 2|)

theorem exponentialMoment_nonneg (T v : ℝ) : 0 ≤ exponentialMoment T v := by
  unfold exponentialMoment
  positivity

/-- Uniform in |u| ≤ v. The exponential factor is kept explicitly. -/
theorem horizontalBudget_le_exponentialMoment (T u v : ℝ) (hu : |u| ≤ v) :
    horizontalBudget T u ≤ (1+v^2)*exponentialMoment T v := by
  have hv : 0 ≤ v := (abs_nonneg u).trans hu
  unfold horizontalBudget exponentialMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  let d := i.1.1.re-1 / 2
  have h := pow_le_pow_left₀ (abs_nonneg (Real.exp (u*d)-1)) (abs_exp_sub_one_le (u*d)) 2
  rw [sq_abs, mul_pow, sq_abs] at h
  have he : Real.exp |u*d| ^ 2 ≤ Real.exp (2*v*|d|) := by
    rw [pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [abs_mul]
    nlinarith [abs_nonneg d]
  have hu2 : u^2 ≤ v^2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hge : 1 ≤ Real.exp (2*v*|d|) := Real.one_le_exp_iff.mpr (by positivity)
  have hb : (u*d)^2 * Real.exp |u*d|^2 ≤ v^2*d^2*Real.exp (2*v*|d|) := by
    rw [mul_pow]
    gcongr
  have hd : d^2 ≤ d^2*Real.exp (2*v*|d|) := by nlinarith [sq_nonneg d]
  change (Real.exp (u*d)-1)^2+d^2 ≤ (1+v^2)*(d^2*Real.exp (2*v*|d|))
  nlinarith

theorem exists_horizontalDefect_le_exponentialMoment :
    ∃ C : ℝ, 0 < C ∧ ∀ T α A : ℝ, 9 ≤ T → |α| ≤ A →
      horizontalDefect T α ≤
        C*(1+(A*Real.log T)^2)*exponentialMoment T (A*Real.log T)/T := by
  obtain ⟨C,hC,hbudget⟩ := exists_horizontalDefect_le_budget
  refine ⟨C,hC,?_⟩
  intro T α A hT hα
  have ht : 0 < T := by linarith
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hu : |α*Real.log T| ≤ A*Real.log T := by
    rw [abs_mul, abs_of_nonneg hl]
    exact mul_le_mul_of_nonneg_right hα hl
  calc
    _ ≤ C*horizontalBudget T (α*Real.log T)/T := hbudget T α hT
    _ ≤ C*((1+(A*Real.log T)^2)*exponentialMoment T (A*Real.log T))/T := by
      gcongr
      exact horizontalBudget_le_exponentialMoment T _ _ hu
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
