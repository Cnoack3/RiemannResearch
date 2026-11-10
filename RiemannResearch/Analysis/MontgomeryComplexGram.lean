/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryPoisson
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Complex Cauchy Gram and its Hilbert-space error inequality

Source: the Poisson/Gram method of Baluyot--Goldston--Suriajaya--
Turnage-Butterbaugh (Acta Arithmetica 214, 2024),
https://doi.org/10.4064/aa230612-20-3, and Section 4 of the user handoff.
The finite identity is proved for arbitrary complex exponents in |Re z|<1.
All integrability is discharged using the bilateral exponential transform.
No asymptotic pair-correlation estimate is imported from the paper.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryComplexGram
open MontgomeryPoisson
variable {ι : Type*} [Fintype ι]

def complexSignal (z c : ι → ℂ) (s : ℝ) : ℂ :=
  ∑ i, c i * Complex.exp ((s : ℂ) * z i)

def complexKernel (z c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, c i * conj (c j) * (4 / (4 - (z i + conj (z j))^2))

theorem feature_complex_product (z w : ℂ) (s : ℝ) :
    feature 2 (z + conj w) s =
      (Real.exp (-2*|s|) : ℂ) *
        (Complex.exp ((s : ℂ)*z) * conj (Complex.exp ((s : ℂ)*w))) := by
  rw [feature, Complex.exp_add, Complex.ofReal_exp]
  congr 1
  · congr 2; ring
  · rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp
    <;> ring

theorem complex_gram_integrand (z c : ι → ℂ) (s : ℝ) :
    ((Real.exp (-2*|s|) * ‖complexSignal z c s‖^2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * conj (c j) * feature 2 (z i + conj (z j)) s := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [complexSignal, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [feature_complex_product]
  ring

theorem pair_strip (z : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) (i j : ι) :
    |(z i + conj (z j)).re| < 2 := by
  simp only [Complex.add_re, Complex.conj_re]
  calc
    _ ≤ |(z i).re| + |(z j).re| := abs_add_le _ _
    _ < 2 := by linarith [hz i, hz j]

theorem complex_gram_integrable (z c : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) :
    Integrable (fun s : ℝ =>
      ((Real.exp (-2*|s|) * ‖complexSignal z c s‖^2 : ℝ) : ℂ)) := by
  simp_rw [complex_gram_integrand]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (integrable_feature 2 _ (pair_strip z hz i j)).const_mul _

theorem complex_gram (z c : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) :
    (∫ s : ℝ, ((Real.exp (-2*|s|) * ‖complexSignal z c s‖^2 : ℝ) : ℂ)) =
      complexKernel z c := by
  have hint (i j : ι) : Integrable (fun s : ℝ =>
      c i * conj (c j) * feature 2 (z i + conj (z j)) s) :=
    (integrable_feature 2 _ (pair_strip z hz i j)).const_mul _
  simp_rw [complex_gram_integrand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  unfold complexKernel
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, integral_feature 2 _ (pair_strip z hz i j)]
  norm_num

theorem complex_gram_re (z c : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) :
    (∫ s : ℝ, Real.exp (-2*|s|) * ‖complexSignal z c s‖^2) =
      (complexKernel z c).re := by
  have h := integral_re (complex_gram_integrable z c hz)
  change (∫ s : ℝ, (((Real.exp (-2*|s|) * ‖complexSignal z c s‖^2 : ℝ) : ℂ)).re) =
    (∫ s : ℝ, ((Real.exp (-2*|s|) * ‖complexSignal z c s‖^2 : ℝ) : ℂ)).re at h
  simpa only [Complex.ofReal_re, complex_gram z c hz] using h

end RiemannResearch.Analysis.MontgomeryComplexGram

namespace RiemannResearch.Analysis.MontgomeryComplexGram
open MontgomeryPoisson
variable {ι : Type*} [Fintype ι]

def weightedSignal (z c : ι → ℂ) (s : ℝ) : ℂ :=
  (Real.exp (-|s|) : ℂ) * complexSignal z c s

theorem weightedSignal_sq (z c : ι → ℂ) (s : ℝ) :
    ‖weightedSignal z c s‖^2 =
      Real.exp (-2*|s|) * ‖complexSignal z c s‖^2 := by
  simp only [weightedSignal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  have h : Real.exp (-|s|)^2 = Real.exp (-2*|s|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h]

theorem weightedSignal_memLp (z c : ι → ℂ) (hz : ∀ i, |(z i).re| < 1) :
    MemLp (weightedSignal z c) 2 := by
  have hc : Continuous (weightedSignal z c) := by
    unfold weightedSignal complexSignal
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simp_rw [weightedSignal_sq]
  have h := (complex_gram_integrable z c hz).re
  change Integrable (fun s : ℝ =>
    (((Real.exp (-2*|s|) * ‖complexSignal z c s‖^2 : ℝ) : ℂ)).re) at h
  simpa only [Complex.ofReal_re] using h

theorem sqrt_integral_sq_norm {f : ℝ → ℂ} (hf : MemLp f 2) :
    Real.sqrt (∫ s : ℝ, ‖f s‖^2) = ‖hf.toLp f‖ := by
  have he : ‖hf.toLp f‖^2 = ∫ s : ℝ, ‖f s‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with s hs
    rw [hs, real_inner_self_eq_norm_sq]
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_energy_reverse_triangle {f g : ℝ → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    |Real.sqrt (∫ s : ℝ, ‖f s‖^2) -
      Real.sqrt (∫ s : ℝ, ‖g s‖^2)| ≤
      Real.sqrt (∫ s : ℝ, ‖f s-g s‖^2) := by
  rw [sqrt_integral_sq_norm hf, sqrt_integral_sq_norm hg]
  change |‖hf.toLp f‖ - ‖hg.toLp g‖| ≤ Real.sqrt (∫ s : ℝ, ‖(f-g) s‖^2)
  rw [sqrt_integral_sq_norm (hf.sub hg), MemLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

theorem complexSignal_shift (z : ι → ℂ) (u s : ℝ) :
    complexSignal z (fun i => Complex.exp ((u : ℂ)*z i)) s =
      ∑ i, Complex.exp (((u+s : ℝ) : ℂ)*z i) := by
  unfold complexSignal
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end RiemannResearch.Analysis.MontgomeryComplexGram
