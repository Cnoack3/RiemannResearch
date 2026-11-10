/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryCoshLaplace
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.ActualZeroCoshMass
import Mathlib.Tactic.Positivity

/-! # Explicit bounds for Montgomery's actual horizontal defect

Source: the user Montgomery continuation handoff, route B.
The signed defect and its integral are those of MontgomeryHorizontalTransfer.
We prove a finite Minkowski bound with exact individual displacement energies,
and a sharp uniform-strip majorant involving the cumulative horizontal energy.
All analytic multiplicities and exponential frequency growth are retained.
No vanishing defect or RH is assumed. The positive strip majorant alone does
not give a weaker-than-RH route at fixed support greater than one; see the ledger.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryHorizontalBound
open MontgomeryCoshLaplace MontgomeryHorizontalTransfer
open ActualZeroOrdinate ActualZeroCoshMass

theorem cosh_abs_half (x : ℝ) : Real.cosh (|x|/2) = Real.cosh (x/2) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), neg_div, Real.cosh_neg]

def stripCoefficient (u : ℝ) : ℝ :=
  (32/3)*Real.cosh u - (512/15)*Real.cosh (u/2) + 24

theorem stripCoefficient_eq_diagonalEnergy (u : ℝ) :
    stripCoefficient u = 16*diagonalEnergy u (1/2) := by
  unfold stripCoefficient diagonalEnergy
  have he : 2*u*(1/2) = u := by ring
  rw [he]
  norm_num
  ring

theorem stripCoefficient_nonneg (u : ℝ) : 0 ≤ stripCoefficient u := by
  rw [stripCoefficient_eq_diagonalEnergy]
  exact mul_nonneg (by norm_num) (diagonalEnergy_nonneg u (1/2) (by norm_num))

theorem defectFeature_le_strip (u d s : ℝ) (hd : d^2 ≤ 1/4) :
    defectFeature u d s ≤ 16*d^4 * defectFeature u (1/2) s := by
  have hb := Real.cosh_mul_sub_one_le_sharp (u+s) d hd
  rw [cosh_abs_half] at hb
  have hn : 0 ≤ Real.cosh ((u+s)*d)-1 := sub_nonneg.mpr (Real.one_le_cosh _)
  have hs := pow_le_pow_left₀ hn hb 2
  unfold defectFeature
  have he : (u+s)*(1/2) = (u+s)/2 := by ring
  rw [he]
  calc
    _ ≤ Real.exp (-2*|s|) * ((4*(Real.cosh ((u+s)/2)-1))*d^2)^2 :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = _ := by ring

theorem diagonalEnergy_le_strip (u d : ℝ) (hd : |d| ≤ 1/2) :
    diagonalEnergy u d ≤ stripCoefficient u * d^4 := by
  have hd1 : |d| < 1 := by linarith
  have hdq : d^2 ≤ 1/4 := by nlinarith [sq_abs d, abs_nonneg d]
  have h := integral_mono (integrable_defectFeature u d hd1)
    ((integrable_defectFeature u (1/2) (by norm_num)).const_mul (16*d^4))
    (fun s => defectFeature_le_strip u d s hdq)
  rw [integral_defectFeature u d hd1, integral_const_mul,
    integral_defectFeature u (1/2) (by norm_num)] at h
  rw [stripCoefficient_eq_diagonalEnergy]
  nlinarith only [h]

theorem integrable_actualDefect (T u : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-2*|s|)*‖coshCorrection T (u+s)‖^2) := by
  have hm := (weightedLandau_memLp T u).sub (weightedOrdinate_memLp T u)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have he (s : ℝ) : (weightedLandau T u - weightedOrdinate T u) s =
      (Real.exp (-|s|) : ℂ)*coshCorrection T (u+s) := by
    simp only [Pi.sub_apply, weightedLandau, weightedOrdinate, exact_signed_correction]
    ring
  simpa only [he, weighted_mul_sq] using hi

/-- This bound preserves the complete exponential frequency dependence. -/
theorem actualDefect_integrand_le (T u s : ℝ) :
    Real.exp (-2*|s|)*‖coshCorrection T (u+s)‖^2 ≤
      (16*horizontalEnergy T ^ 2) * defectFeature u (1/2) s := by
  have hb := (norm_coshCorrection_le_mass T (u+s)).trans
    (coshMass_le_horizontalEnergy_sharp T (u+s))
  rw [cosh_abs_half] at hb
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  unfold defectFeature
  have he : (u+s)*(1/2) = (u+s)/2 := by ring
  rw [he]
  calc
    _ ≤ Real.exp (-2*|s|)*((4*(Real.cosh ((u+s)/2)-1))*horizontalEnergy T)^2 :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = _ := by ring

/-- Unconditional actual-zero estimate, with all multiplicities. It asserts
no decay of the cumulative horizontal energy. -/
theorem defectIntegral_le_horizontalEnergy (T u : ℝ) :
    defectIntegral T u ≤ stripCoefficient u * horizontalEnergy T ^ 2 := by
  have h := integral_mono (integrable_actualDefect T u)
    ((integrable_defectFeature u (1/2) (by norm_num)).const_mul
      (16*horizontalEnergy T^2)) (fun s => actualDefect_integrand_le T u s)
  rw [integral_const_mul, integral_defectFeature u (1/2) (by norm_num)] at h
  rw [stripCoefficient_eq_diagonalEnergy]
  exact h.trans_eq (by ring)

theorem horizontalDefect_le_horizontalEnergy {T : ℝ} (hT : 1 < T) (α : ℝ) :
    horizontalDefect T α ≤
      stripCoefficient (α*Real.log T) * horizontalEnergy T^2 /
        (T*Real.log T/(2*Real.pi)) := by
  apply div_le_div_of_nonneg_right (defectIntegral_le_horizontalEnergy T _)
  exact (div_pos (mul_pos (by linarith) (Real.log_pos hT))
    (mul_pos (by norm_num) Real.pi_pos)).le

open MontgomeryComplexGram ZeroOrdinate

def weightedCopy (T u : ℝ) (i : Copies T) (s : ℝ) : ℂ :=
  (Real.exp (-|s|) : ℂ) * (phase (u+s) i.1.1.im *
    ((Real.cosh ((u+s)*(i.1.1.re-1/2)) : ℂ)-1))

theorem weightedCopy_sq (T u : ℝ) (i : Copies T) (s : ℝ) :
    ‖weightedCopy T u i s‖^2 = defectFeature u (i.1.1.re-1/2) s := by
  unfold weightedCopy
  rw [weighted_mul_sq, norm_mul, phase_norm, one_mul]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  rfl

theorem weightedCopy_memLp (T u : ℝ) (i : Copies T) :
    MemLp (weightedCopy T u i) 2 := by
  have hc : Continuous (weightedCopy T u i) := by
    unfold weightedCopy phase
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simp_rw [weightedCopy_sq]
  exact integrable_defectFeature u _ ((displacement_lt_half i.1.2).trans (by norm_num))

theorem weightedCopy_sum (T u s : ℝ) :
    (∑ i : Copies T, weightedCopy T u i s) =
      (Real.exp (-|s|) : ℂ)*coshCorrection T (u+s) := by
  rw [coshCorrection, sum_eq_copies, Finset.mul_sum]
  rfl

/-- The finite Minkowski bound retains every individual horizontal
displacement and vanishes identically on critical-line copies. -/
theorem sqrt_defectIntegral_le_diagonal (T u : ℝ) :
    Real.sqrt (defectIntegral T u) ≤
      ∑ i : Copies T, Real.sqrt (diagonalEnergy u (i.1.1.re-1/2)) := by
  have h := sqrt_energy_sum_le Finset.univ (weightedCopy T u)
    (weightedCopy_memLp T u)
  simp only [weightedCopy_sum, weighted_mul_sq, weightedCopy_sq] at h
  have hi (i : Copies T) :
      (∫ s : ℝ, defectFeature u (i.1.1.re-1/2) s) =
        diagonalEnergy u (i.1.1.re-1/2) :=
    integral_defectFeature u _ ((displacement_lt_half i.1.2).trans (by norm_num))
  simp_rw [hi] at h
  exact h

theorem defectIntegral_le_diagonal (T u : ℝ) :
    defectIntegral T u ≤
      (∑ i : Copies T, Real.sqrt (diagonalEnergy u (i.1.1.re-1/2)))^2 := by
  have h := sqrt_defectIntegral_le_diagonal T u
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (show 0 ≤ defectIntegral T u from
    integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))] at hsq
  exact hsq

end RiemannResearch.Analysis.MontgomeryHorizontalBound
