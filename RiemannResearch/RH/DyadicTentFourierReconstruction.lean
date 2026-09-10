/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DyadicTentFourierSummability
import RiemannResearch.Analysis.IntegerTentSupport
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Unconditional Fourier reconstruction of the actual dyadic logarithmic tent

Source: continuation of the user-provided
`FourierBridgeLeanVerification20260910(1).md`, specifically the remaining
logarithmic-periodization and scalar Fourier-reconstruction obligation.
The change-of-variables proof and Poisson summation use the Mathlib theorems
imported above.

The actual logarithmic tent is continuous and compactly supported. Its real
Fourier transform equals the already-defined Mellin coefficient, including
frequency zero. The actual periodization is continuous and periodic, and its
Fourier expansion converges to it with an unconditional `HasSum` theorem.
Its integer samples vanish, giving exact signed cancellation of all modes.

These are scalar tent results. The complete signed arithmetic Fourier bridge
and uniform boundary-energy estimate remain separate obligations.
-/

noncomputable section

open MeasureTheory RiemannResearch.Analysis Filter Asymptotics TopologicalSpace
open scoped FourierTransform

namespace RiemannResearch.RH.Pareto

/-- Actual root tent in logarithmic coordinates normalized to period one. -/
def dyadicLogTent (i : ℕ) (t : ℝ) : ℂ :=
  (rootTent (2 * (i + 1)) (Real.exp (Real.log 2 * t)) : ℂ)

theorem continuous_dyadicLogTent (i : ℕ) : Continuous (dyadicLogTent i) := by
  unfold dyadicLogTent
  exact Complex.continuous_ofReal.comp
    ((continuous_rootTent _).comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

theorem dyadicLogTent_eq_zero_of_le (i : ℕ) {t : ℝ}
    (ht : t ≤ Real.log (2 * (i + 1)) / Real.log 2) : dyadicLogTent i t = 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < (2 * (i + 1) : ℝ) := by positivity
  have ht' : Real.log 2 * t ≤ Real.log (2 * (i + 1)) := by
    simpa only [mul_comm] using (le_div_iff₀ hlog).mp ht
  have he := (Real.le_log_iff_exp_le ha).mp ht'
  simp only [dyadicLogTent, rootTent_eq_zero_of_le he, Complex.ofReal_zero]

theorem dyadicLogTent_eq_zero_of_ge (i : ℕ) {t : ℝ}
    (ht : Real.log (2 * (i + 1) + 2) / Real.log 2 ≤ t) : dyadicLogTent i t = 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 < (2 * (i + 1) + 2 : ℝ) := by positivity
  have ht' : Real.log (2 * (i + 1) + 2) ≤ Real.log 2 * t := by
    simpa only [mul_comm] using (div_le_iff₀ hlog).mp ht
  have he := (Real.log_le_iff_le_exp ha).mp ht'
  simp only [dyadicLogTent, rootTent_eq_zero_of_ge he, Complex.ofReal_zero]

theorem hasCompactSupport_dyadicLogTent (i : ℕ) : HasCompactSupport (dyadicLogTent i) := by
  apply HasCompactSupport.intro (K := Set.Icc
    (Real.log (2 * (i + 1)) / Real.log 2)
    (Real.log (2 * (i + 1) + 2) / Real.log 2)) isCompact_Icc
  intro t ht
  by_cases hlo : Real.log (2 * (i + 1)) / Real.log 2 ≤ t
  · exact dyadicLogTent_eq_zero_of_ge i
      (le_of_not_ge (fun hhi => ht ⟨hlo, hhi⟩))
  · exact dyadicLogTent_eq_zero_of_le i (le_of_not_ge hlo)

theorem integrable_dyadicLogTent (i : ℕ) : Integrable (dyadicLogTent i) :=
  (continuous_dyadicLogTent i).integrable_of_hasCompactSupport
    (hasCompactSupport_dyadicLogTent i)

theorem dyadicLogTent_isBigO_cocompact (i : ℕ) (b : ℝ) :
    dyadicLogTent i =O[cocompact ℝ] (fun t : ℝ => |t| ^ (-b)) := by
  have hz : dyadicLogTent i =ᶠ[cocompact ℝ] 0 := by
    simpa only [Filter.coclosedCompact_eq_cocompact] using
      (hasCompactSupport_iff_eventuallyEq.mp (hasCompactSupport_dyadicLogTent i))
  exact hz.isBigO.trans (Asymptotics.isBigO_zero _ _)

/-- The actual periodization, with the summands fixed before reconstruction. -/
def dyadicLogTentPeriodization (i : ℕ) (t : ℝ) : ℂ :=
  ∑' n : ℤ, dyadicLogTent i (t + n)

def dyadicLogTentContinuousMap (i : ℕ) : C(ℝ, ℂ) :=
  ⟨dyadicLogTent i, continuous_dyadicLogTent i⟩

theorem summable_norm_dyadicLogTent_restrict_translates (i : ℕ) (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((dyadicLogTentContinuousMap i).comp (ContinuousMap.addRight n)).restrict K‖) := by
  exact summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((isBigO_norm_restrict_cocompact (dyadicLogTentContinuousMap i)
      (by norm_num : (0 : ℝ) < 2) (dyadicLogTent_isBigO_cocompact i 2) K).comp_tendsto
      Int.tendsto_coe_cofinite)

theorem summable_dyadicLogTentContinuousMap_translates (i : ℕ) :
    Summable (fun n : ℤ => (dyadicLogTentContinuousMap i).comp (ContinuousMap.addRight n)) :=
  ContinuousMap.summable_of_locally_summable_norm
    (summable_norm_dyadicLogTent_restrict_translates i)

theorem dyadicLogTentPeriodization_eq_continuousMap (i : ℕ) :
    dyadicLogTentPeriodization i =
      ((∑' n : ℤ, (dyadicLogTentContinuousMap i).comp (ContinuousMap.addRight n)) : C(ℝ, ℂ)) := by
  funext t
  exact ContinuousMap.tsum_apply (summable_dyadicLogTentContinuousMap_translates i) t

theorem continuous_dyadicLogTentPeriodization (i : ℕ) :
    Continuous (dyadicLogTentPeriodization i) := by
  rw [dyadicLogTentPeriodization_eq_continuousMap]
  exact ContinuousMap.continuous _

theorem periodic_dyadicLogTentPeriodization (i : ℕ) :
    Function.Periodic (dyadicLogTentPeriodization i) 1 := by
  rw [dyadicLogTentPeriodization_eq_continuousMap]
  simpa only [zsmul_one] using
    (dyadicLogTentContinuousMap i).periodic_tsum_comp_add_zsmul (1 : ℝ)

theorem summable_dyadicLogTent_translates (i : ℕ) (t : ℝ) :
    Summable (fun n : ℤ => dyadicLogTent i (t + n)) := by
  exact (ContinuousMap.hasSum_apply (summable_dyadicLogTentContinuousMap_translates i).hasSum t).summable


private theorem dyadicFourierKernel_log_substitution (i : ℕ) (h : ℤ)
    {x : ℝ} (hx : 0 < x) :
    (x⁻¹ / Real.log 2) •
        (Complex.exp ((((-2 * Real.pi * (Real.log x / Real.log 2) * (h : ℝ)) : ℝ) : ℂ) *
          Complex.I) • dyadicLogTent i (Real.log x / Real.log 2)) =
      (Real.log 2 : ℂ)⁻¹ * (rootTent (2 * (i + 1)) x : ℂ) *
        (x : ℂ) ^ (-Complex.I * (dyadicLogFrequency h : ℂ) - 1) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hexp :
      (((-2 * Real.pi * (Real.log x / Real.log 2) * (h : ℝ)) : ℝ) : ℂ) * Complex.I =
        (Real.log x : ℂ) * (-Complex.I * (dyadicLogFrequency h : ℂ)) := by
    unfold dyadicLogFrequency
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hcpow : (x : ℂ) ^ (-Complex.I * (dyadicLogFrequency h : ℂ) - 1) =
      Complex.exp
        ((((-2 * Real.pi * (Real.log x / Real.log 2) * (h : ℝ)) : ℝ) : ℂ) * Complex.I) *
          (x : ℂ)⁻¹ := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hx0, Complex.cpow_neg_one,
      Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le, ← hexp]
  have he : Real.exp (Real.log 2 * (Real.log x / Real.log 2)) = x := by
    rw [show Real.log 2 * (Real.log x / Real.log 2) = Real.log x by field_simp [hlog]]
    exact Real.exp_log hx
  unfold dyadicLogTent
  rw [he, hcpow]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- The actual real Fourier transform is the already-defined Mellin integral,
including frequency zero. No reconstruction provider is assumed. -/
theorem dyadicLogTent_fourier_eq_mellin (i : ℕ) (h : ℤ) :
    𝓕 (dyadicLogTent i) (h : ℝ) = dyadicTentMellinCoefficient i h := by
  let a : ℝ := 2 * (i + 1)
  let L : ℝ := Real.log a / Real.log 2
  let U : ℝ := Real.log (a + 2) / Real.log 2
  let g : ℝ → ℂ := fun t =>
    Complex.exp ((((-2 * Real.pi * t * (h : ℝ)) : ℝ) : ℂ) * Complex.I) •
      dyadicLogTent i t
  have ha : 0 < a := by dsimp [a]; positivity
  have hpos : ∀ x ∈ Set.uIcc a (a + 2), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (show a ≤ a + 2 by linarith)] at hx
    exact lt_of_lt_of_le ha hx.1
  have hder : ∀ x ∈ Set.uIcc a (a + 2),
      HasDerivAt (fun y => Real.log y / Real.log 2) (x⁻¹ / Real.log 2) x := by
    intro x hx
    exact (Real.hasDerivAt_log (hpos x hx).ne').div_const _
  have hcder : ContinuousOn (fun x : ℝ => x⁻¹ / Real.log 2) (Set.uIcc a (a + 2)) := by
    exact (continuousOn_id.inv₀ (fun x hx => (hpos x hx).ne')).div_const _
  have hcg : Continuous g := by
    dsimp [g]
    exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (((continuous_const.mul continuous_id).mul continuous_const))).mul continuous_const)).smul
      (continuous_dyadicLogTent i)
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (g := g) hder hcder hcg
  have hsupp : Function.support g ⊆ Set.Ioc L U := by
    intro t ht
    change g t ≠ 0 at ht
    constructor
    · by_contra hle
      have hz := dyadicLogTent_eq_zero_of_le i (le_of_not_gt hle)
      exact ht (by simp only [g, hz, smul_zero])
    · by_contra hle
      have hz := dyadicLogTent_eq_zero_of_ge i (le_of_lt (lt_of_not_ge hle))
      exact ht (by simp only [g, hz, smul_zero])
  calc
    𝓕 (dyadicLogTent i) (h : ℝ) = ∫ t in L..U, g t := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      exact (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
    _ = ∫ x in a..a + 2,
        (x⁻¹ / Real.log 2) • g (Real.log x / Real.log 2) := hsub.symm
    _ = dyadicTentMellinCoefficient i h := by
      unfold dyadicTentMellinCoefficient
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      simpa only [g, mul_assoc] using dyadicFourierKernel_log_substitution i h (hpos x hx)

/-- Unconditional reconstruction of the actual logarithmic tent periodization. -/
theorem dyadicLogTentPeriodization_eq_fourier (i : ℕ) (t : ℝ) :
    dyadicLogTentPeriodization i t =
      ∑' h : ℤ, dyadicTentMellinCoefficient i h * fourier h (t : UnitAddCircle) := by
  have hs : Summable (fun h : ℤ => 𝓕 (dyadicLogTent i) (h : ℝ)) := by
    simpa only [dyadicLogTent_fourier_eq_mellin] using summable_dyadicTentMellinCoefficient i
  simpa only [dyadicLogTentPeriodization, dyadicLogTent_fourier_eq_mellin] using
    Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
      (continuous_dyadicLogTent i) (by norm_num : (1 : ℝ) < 2)
      (dyadicLogTent_isBigO_cocompact i 2) hs t

/-- The actual Fourier expansion converges absolutely at every real phase. -/
theorem dyadicLogTentPeriodization_hasSum_fourier (i : ℕ) (t : ℝ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h * fourier h (t : UnitAddCircle))
      (dyadicLogTentPeriodization i t) := by
  rw [dyadicLogTentPeriodization_eq_fourier i t]
  apply Summable.hasSum
  apply Summable.of_norm
  apply summable_norm_dyadicTentMellinCoefficient_mul_of_bounded i _ 1
  intro h
  exact (ContinuousMap.norm_coe_le_norm (fourier h) (t : UnitAddCircle)).trans
    (le_of_eq (fourier_norm h))

theorem dyadicLogTent_int_eq_zero (i : ℕ) (n : ℤ) : dyadicLogTent i n = 0 := by
  have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      have hz0 : ((Int.ofNat 0 : ℤ) : ℝ) = 0 := by norm_num
      rw [hz0]
      have he : rootTent (2 * (i + 1)) 1 = 0 := by
        apply rootTent_eq_zero_of_le
        have hi : (0 : ℝ) ≤ i := by positivity
        linarith
      simp only [dyadicLogTent, mul_zero, Real.exp_zero, he, Complex.ofReal_zero]
    | succ k =>
      change dyadicLogTent i ((k + 1 : ℕ) : ℝ) = 0
      have he : Real.exp (Real.log 2 * ((k + 1 : ℕ) : ℝ)) =
          2 * ((2 ^ k : ℕ) : ℝ) := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        push_cast
        rw [pow_succ]
        ring
      have hz : rootTent (2 * (i + 1)) (2 * ((2 ^ k : ℕ) : ℝ)) = 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using rootTent_even_nat (i + 1) (2 ^ k)
      simp only [dyadicLogTent, he, hz, Complex.ofReal_zero]
  | negSucc k =>
    have hn : ((Int.negSucc k : ℤ) : ℝ) ≤ 0 := by
      have hk : (0 : ℝ) ≤ k := by positivity
      push_cast
      linarith
    have he : Real.exp (Real.log 2 * ((Int.negSucc k : ℤ) : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hlog hn)
    have hz := rootTent_eq_zero_of_le
      (a := (2 * (i + 1) : ℝ)) (he.trans (by
        have hi : (0 : ℝ) ≤ i := by positivity
        linarith))
    simp only [dyadicLogTent, hz, Complex.ofReal_zero]

theorem dyadicLogTentPeriodization_zero (i : ℕ) : dyadicLogTentPeriodization i 0 = 0 := by
  simp only [dyadicLogTentPeriodization, zero_add, dyadicLogTent_int_eq_zero, tsum_zero]

/-- At logarithmic phase zero, the exact sum of all Fourier modes vanishes. -/
theorem hasSum_dyadicTentMellinCoefficient_zero (i : ℕ) :
    HasSum (dyadicTentMellinCoefficient i) 0 := by
  simpa [dyadicLogTentPeriodization_zero] using
    dyadicLogTentPeriodization_hasSum_fourier i 0

theorem tsum_dyadicTentMellinCoefficient_eq_zero (i : ℕ) :
    (∑' h : ℤ, dyadicTentMellinCoefficient i h) = 0 :=
  (hasSum_dyadicTentMellinCoefficient_zero i).tsum_eq

end RiemannResearch.RH.Pareto
