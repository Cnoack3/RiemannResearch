/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryComplexGram
import RiemannResearch.Analysis.MontgomeryFormFactor

/-! # Actual complex-zero form factor and horizontal transfer

Source: BGSTB's complex-zero pair statistic and reflection, Acta Arithmetica
214 (2024), https://doi.org/10.4064/aa230612-20-3; the user Montgomery handoff,
Section 4. The 2026 correction to the paper's asymptotic error term is recorded
in MontgomeryParsevalResearch20261110.md; no asymptotic is asserted here.
ActualZeroOrdinate supplies actual zeros, positive multiplicities, reflection,
the critical-strip bound and the exact cosh correction. The new result proves
the complete weighted-L2 reverse triangle inequality with no RH or density
input. Its horizontal defect is explicit and has not been shown to vanish.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer
open MontgomeryComplexGram MontgomeryFormFactor MontgomeryPoisson
open ActualZeroOrdinate ZeroOrdinate

def weightedLandau (T u s : ℝ) : ℂ :=
  (Real.exp (-|s|) : ℂ) * landauSum T (u+s)

def weightedOrdinate (T u s : ℝ) : ℂ :=
  (Real.exp (-|s|) : ℂ) * ordinateSum T (u+s)

theorem weighted_mul_sq (s : ℝ) (v : ℂ) :
    ‖(Real.exp (-|s|) : ℂ)*v‖^2 = Real.exp (-2*|s|)*‖v‖^2 := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  have h : Real.exp (-|s|)^2 = Real.exp (-2*|s|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h]

theorem weightedLandau_memLp (T u : ℝ) : MemLp (weightedLandau T u) 2 := by
  let z : Copies T → ℂ := fun i => i.1.1 - 1/2
  have hz : ∀ i, |(z i).re| < 1 := by
    intro i
    have hi := displacement_lt_half i.1.2
    change |(i.1.1 - 1/2 : ℂ).re| < 1
    have he : (i.1.1 - 1/2 : ℂ).re = i.1.1.re - 1/2 := by norm_num
    rw [he]
    linarith
  have he : weightedLandau T u =
      weightedSignal z (fun i => Complex.exp ((u : ℂ)*z i)) := by
    funext s
    unfold weightedLandau weightedSignal
    rw [complexSignal_shift]
    simp only [landauSum, sum_eq_copies, z]
  rw [he]
  exact weightedSignal_memLp _ _ hz

theorem weightedOrdinate_memLp (T u : ℝ) : MemLp (weightedOrdinate T u) 2 := by
  let z : Copies T → ℂ := fun i => (copyOrdinate T i : ℂ)*Complex.I
  have hz : ∀ i, |(z i).re| < 1 := by
    intro i
    simp [z]
  have he : weightedOrdinate T u =
      weightedSignal z (fun i => Complex.exp ((u : ℂ)*z i)) := by
    funext s
    unfold weightedOrdinate weightedSignal
    rw [complexSignal_shift]
    simp only [ordinateSum, sum_eq_copies, phase, z, copyOrdinate,
      Complex.ofReal_mul, mul_assoc]
  rw [he]
  exact weightedSignal_memLp _ _ hz

def sharpIntegral (T u : ℝ) : ℝ :=
  ∫ s : ℝ, Real.exp (-2*|s|)*‖landauSum T (u+s)‖^2

def rawIntegral (T u : ℝ) : ℝ :=
  ∫ s : ℝ, Real.exp (-2*|s|)*‖ordinateSum T (u+s)‖^2

def defectIntegral (T u : ℝ) : ℝ :=
  ∫ s : ℝ, Real.exp (-2*|s|)*‖coshCorrection T (u+s)‖^2

theorem sqrt_integral_horizontal_error (T u : ℝ) :
    |Real.sqrt (sharpIntegral T u)-Real.sqrt (rawIntegral T u)| ≤
      Real.sqrt (defectIntegral T u) := by
  have h := sqrt_energy_reverse_triangle
    (weightedLandau_memLp T u) (weightedOrdinate_memLp T u)
  have hd (s : ℝ) : weightedLandau T u s - weightedOrdinate T u s =
      (Real.exp (-|s|) : ℂ)*coshCorrection T (u+s) := by
    rw [weightedLandau, weightedOrdinate, exact_signed_correction]
    ring
  simp only [hd] at h
  simp only [weightedLandau, weightedOrdinate, weighted_mul_sq] at h
  exact h

def sharpFormFactor (T α : ℝ) : ℝ :=
  sharpIntegral T (α*Real.log T) / (T*Real.log T/(2*Real.pi))

def horizontalDefect (T α : ℝ) : ℝ :=
  defectIntegral T (α*Real.log T) / (T*Real.log T/(2*Real.pi))

theorem formFactor_eq_rawIntegral (T α : ℝ) :
    formFactor T α =
      rawIntegral T (α*Real.log T) / (T*Real.log T/(2*Real.pi)) := by
  rw [formFactor_gram]
  simp only [rawIntegral, ordinateSum, sum_eq_copies, copyOrdinate]

/-- No density or RH input: the defect remains an actual, explicit integral. -/
theorem sqrt_horizontal_error (T α : ℝ) :
    |Real.sqrt (sharpFormFactor T α)-Real.sqrt (formFactor T α)| ≤
      Real.sqrt (horizontalDefect T α) := by
  have hS : 0 ≤ sharpIntegral T (α*Real.log T) :=
    integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hR : 0 ≤ rawIntegral T (α*Real.log T) :=
    integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hD : 0 ≤ defectIntegral T (α*Real.log T) :=
    integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  rw [sharpFormFactor, horizontalDefect, formFactor_eq_rawIntegral,
    Real.sqrt_div hS, Real.sqrt_div hR, Real.sqrt_div hD,
    ← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (sqrt_integral_horizontal_error T _)
    (Real.sqrt_nonneg _)

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer

namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer
open MontgomeryComplexGram ActualZeroOrdinate

def complexPairTerm (u : ℝ) (ρ σ : ℂ) : ℂ :=
  Complex.exp ((u : ℂ)*(ρ-σ)) * (4/(4-(ρ-σ)^2))

def actualComplexPairSum (T u : ℝ) : ℂ :=
  sum T (fun ρ => sum T (fun σ => complexPairTerm u ρ σ))

theorem centered_pair_reflect (ρ σ : ℂ) :
    (ρ-1/2)+conj (σ-1/2) = ρ-Zeta23.reflect σ := by
  simp only [Zeta23.reflect, map_sub, map_div₀, map_one, map_ofNat]
  ring

theorem centered_exp_product (u : ℝ) (ρ σ : ℂ) :
    Complex.exp ((u : ℂ)*(ρ-1/2)) *
      conj (Complex.exp ((u : ℂ)*(σ-1/2))) =
      Complex.exp ((u : ℂ)*(ρ-Zeta23.reflect σ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal, Zeta23.reflect]
  ring

theorem actual_complex_kernel (T u : ℝ) :
    complexKernel (fun i : Copies T => i.1.1-1/2)
      (fun i => Complex.exp ((u : ℂ)*(i.1.1-1/2))) =
      actualComplexPairSum T u := by
  calc
    _ = ∑ i : Copies T, ∑ j : Copies T,
        complexPairTerm u i.1.1 (Zeta23.reflect j.1.1) := by
      unfold complexKernel
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [centered_pair_reflect, centered_exp_product]
      rfl
    _ = sum T (fun ρ => sum T (fun σ =>
        complexPairTerm u ρ (Zeta23.reflect σ))) := by
      simp only [sum_eq_copies]
    _ = actualComplexPairSum T u := by
      unfold actualComplexPairSum
      congr 1
      funext ρ
      exact sum_reflect T (complexPairTerm u ρ)

/-- Exact identification with the complex-zero double sum, using reflection
of the actual zero multiset. No RH and no asymptotic hypothesis. -/
theorem sharpIntegral_eq_actualComplexPairSum (T u : ℝ) :
    sharpIntegral T u = (actualComplexPairSum T u).re := by
  let z : Copies T → ℂ := fun i => i.1.1-1/2
  have hz : ∀ i, |(z i).re| < 1 := by
    intro i
    have hi := displacement_lt_half i.1.2
    change |(i.1.1-1/2 : ℂ).re| < 1
    have he : (i.1.1 - 1/2 : ℂ).re = i.1.1.re - 1/2 := by norm_num
    rw [he]
    linarith
  have h := complex_gram_re z (fun i => Complex.exp ((u : ℂ)*z i)) hz
  have he (s : ℝ) :
      complexSignal z (fun i => Complex.exp ((u : ℂ)*z i)) s =
        landauSum T (u+s) := by
    rw [complexSignal_shift]
    simp only [landauSum, sum_eq_copies, z]
  simp_rw [he] at h
  change sharpIntegral T u = (complexKernel
    (fun i : Copies T => i.1.1-1/2)
    (fun i => Complex.exp ((u : ℂ)*(i.1.1-1/2)))).re at h
  simpa only [actual_complex_kernel] using h

theorem sharpFormFactor_eq_actualComplexPairSum (T α : ℝ) :
    sharpFormFactor T α =
      (actualComplexPairSum T (α*Real.log T)).re / (T*Real.log T/(2*Real.pi)) := by
  rw [sharpFormFactor, sharpIntegral_eq_actualComplexPairSum]

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer
