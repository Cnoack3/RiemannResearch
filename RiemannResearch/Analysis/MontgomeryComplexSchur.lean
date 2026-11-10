/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.MontgomeryComplexGram
import Mathlib.Tactic.FieldSimp
/-! # Complex Cauchy Schur bounds over actual zeta ordinates

Source: the complex-zero Gram method of Baluyot--Goldston--Suriajaya--
Turnage-Butterbaugh, Acta Arithmetica 214 (2024),
https://doi.org/10.4064/aa230612-20-3, for the complex kernel framework.
The elementary entry comparison and Schur bounds below are deductions from
that exact kernel and the already-proved actual local zero-count estimate.
They are upper bounds only; no pair-correlation asymptotic is imported.

In the closed half-strip, each complex Cauchy entry is at most 4/3 times the
raw Cauchy weight of the ordinate difference. Thus local zero counts control
the weighted L2 norm with the squared coefficient sum, uniformly in arbitrary
copy-dependent horizontal displacements. Every multiplicity copy is retained.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryComplexSchur
open MontgomeryPoisson MontgomeryComplexGram MontgomeryLocalMass MarkedFourierTail

theorem complex_cauchy_norm_le (z w : ℂ)
    (hz : |z.re| ≤ 1 / 2) (hw : |w.re| ≤ 1 / 2) :
    ‖(4 / (4-(z+conj w)^2) : ℂ)‖ ≤
      (4 / 3 : ℝ) * cauchyWeight (z.im-w.im) := by
  have hab : |z.re+w.re| ≤ 1 :=
    (abs_add_le _ _).trans (by linarith)
  have ha := abs_le.mp hab
  have hs : (z.re+w.re)^2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-(z.re+w.re))
      (by linarith : 0 ≤ 1+(z.re+w.re))]
  have he : (4-(z+conj w)^2).re =
      4-(z.re+w.re)^2+(z.im-w.im)^2 := by
    simp [pow_two]
    <;> ring
  have hd : 3+(z.im-w.im)^2 ≤ ‖(4-(z+conj w)^2 : ℂ)‖ := by
    have hh : 3+(z.im-w.im)^2 ≤ (4-(z+conj w)^2 : ℂ).re := by
      rw [he]
      linarith
    exact hh.trans (Complex.re_le_norm _)
  calc
    _ = 4 / ‖(4-(z+conj w)^2 : ℂ)‖ := by rw [norm_div]; norm_num
    _ ≤ 4 / (3+(z.im-w.im)^2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
    _ ≤ (4 / 3 : ℝ) * cauchyWeight (z.im-w.im) := by
      unfold cauchyWeight
      have h3 : 0 < 3+(z.im-w.im)^2 := by positivity
      have h4 : 0 < 4+(z.im-w.im)^2 := by positivity
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ h3 h4).mpr
      nlinarith [sq_nonneg (z.im-w.im)]

theorem complexKernel_norm_le_of_rows {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (D : ℝ)
    (hz : ∀ i, |(z i).re| ≤ 1 / 2)
    (hrow : ∀ i, (∑ j, cauchyWeight ((z i).im - (z j).im)) ≤ D) :
    ‖complexKernel z c‖ ≤ (4 / 3 : ℝ) * D * ∑ i, ‖c i‖^2 := by
  have hterm (i j : ι) :
      ‖c i * conj (c j) * (4/(4-(z i+conj (z j))^2))‖ ≤
      (4 / 3 : ℝ) * (cauchyWeight ((z i).im - (z j).im) * ‖c i‖ * ‖c j‖) := by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    calc
      _ ≤ (‖c i‖*‖c j‖)*((4 / 3 : ℝ)*cauchyWeight ((z i).im - (z j).im)) :=
        mul_le_mul_of_nonneg_left (complex_cauchy_norm_le _ _ (hz i) (hz j))
          (by positivity)
      _ = _ := by ring
  have hquad :
      (∑ i, ∑ j, cauchyWeight ((z i).im - (z j).im) * ‖c i‖ * ‖c j‖) ≤
        D * ∑ i, ‖c i‖^2 := by
    apply symmetric_kernel_quadratic_le_row_bound
      Finset.univ (fun i => ‖c i‖) (fun i j => cauchyWeight ((z i).im - (z j).im)) D
    · intro i hi j hj; exact cauchyWeight_nonneg _
    · intro i hi j hj
      unfold cauchyWeight
      congr 2
      ring
    · intro i hi; exact hrow i
  calc
    _ ≤ ∑ i, ‖∑ j, c i * conj (c j) * (4/(4-(z i+conj (z j))^2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ∑ j,
        (4 / 3 : ℝ) * (cauchyWeight ((z i).im - (z j).im) * ‖c i‖ * ‖c j‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (4 / 3 : ℝ) * ∑ i, ∑ j,
        cauchyWeight ((z i).im - (z j).im) * ‖c i‖ * ‖c j‖ := by
      simp only [Finset.mul_sum]
    _ ≤ (4 / 3 : ℝ)*(D*∑ i, ‖c i‖^2) :=
      mul_le_mul_of_nonneg_left hquad (by norm_num)
    _ = _ := by ring

theorem complex_signal_energy_le_of_rows {ι : Type*} [Fintype ι]
    (z c : ι → ℂ) (D : ℝ)
    (hz : ∀ i, |(z i).re| ≤ 1 / 2)
    (hrow : ∀ i, (∑ j, cauchyWeight ((z i).im - (z j).im)) ≤ D) :
    (∫ s : ℝ, Real.exp (-2*|s|)*‖complexSignal z c s‖^2) ≤
      (4 / 3 : ℝ) * D * ∑ i, ‖c i‖^2 := by
  rw [complex_gram_re _ _ (fun i => (hz i).trans_lt (by norm_num))]
  exact (Complex.re_le_norm _).trans (complexKernel_norm_le_of_rows z c D hz hrow)

end RiemannResearch.Analysis.MontgomeryComplexSchur

namespace RiemannResearch.Analysis.MontgomeryComplexSchur
open MontgomeryPoisson MontgomeryComplexGram MontgomeryLocalMass ActualZeroOrdinate

/-- Uniformly displaced actual ordinates satisfy a coefficient Bessel bound.
The displacements may vary by copy; the full closed half-strip is allowed. -/
theorem exists_actual_displaced_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ z c : Copies T → ℂ,
      (∀ i, (z i).im = copyOrdinate T i) →
      (∀ i, |(z i).re| ≤ 1 / 2) →
      (∫ s : ℝ, Real.exp (-2*|s|)*‖complexSignal z c s‖^2) ≤
        C * Real.log (T+3) * ∑ i, ‖c i‖^2 := by
  obtain ⟨A,hA,hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨(4 / 3 : ℝ)*A, by positivity, ?_⟩
  intro T hT z c him hre
  have hr (i : Copies T) :
      (∑ j, cauchyWeight ((z i).im - (z j).im)) ≤ A * Real.log (T+3) := by
    simp_rw [him]
    exact hrow T hT _
  have h := complex_signal_energy_le_of_rows z c (A * Real.log (T+3)) hre hr
  simpa only [mul_assoc] using h

/-- The centered actual complex zeros discharge both the ordinate and strip inputs. -/
theorem exists_actual_centered_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ c : Copies T → ℂ,
      (∫ s : ℝ, Real.exp (-2*|s|)*
        ‖complexSignal (fun i : Copies T => i.1.val-1 / 2) c s‖^2) ≤
        C * Real.log (T+3) * ∑ i, ‖c i‖^2 := by
  obtain ⟨C,hC,henergy⟩ := exists_actual_displaced_energy_bound
  refine ⟨C,hC,?_⟩
  intro T hT c
  apply henergy T hT _ c
  · intro i
    simp [copyOrdinate]
  · intro i
    have h := (displacement_lt_half i.1.property).le
    simpa using h

end RiemannResearch.Analysis.MontgomeryComplexSchur
