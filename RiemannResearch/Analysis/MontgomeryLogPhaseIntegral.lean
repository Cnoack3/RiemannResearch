/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import RiemannResearch.Analysis.MontgomeryLogMeanSquare
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The logarithmically weighted oscillatory integral in BGSTB

Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh, §3, between (3.4)
and (3.5), https://arxiv.org/html/2501.14545v3#S3.E4. Integration by parts
controls the individual frequency n in the A₁–A₂ cross integral. Both
endpoint terms and the integral remainder are retained in the identity.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.Analysis.MontgomeryLogPhaseIntegral
open ZeroOrdinate MontgomeryLogMeanSquare

private theorem phase_deriv (v t : ℝ) :
    HasDerivAt (phase v) (((v : ℂ) * Complex.I) * phase v t) t := by
  have h := ((((hasDerivAt_id t).const_mul v).ofReal_comp).mul_const Complex.I).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp (((v * x : ℝ) : ℂ) * Complex.I)) _ t
  simpa [phase, mul_comm] using h

/-- The signed endpoint formula at every real frequency, including zero. -/
theorem log_phase_integral_parts (v : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ((v : ℂ) * Complex.I) * (∫ t in (0 : ℝ)..T, (Real.log (t + 2) : ℂ) * phase v t) =
      (Real.log (T + 2) : ℂ) * phase v T - (Real.log 2 : ℂ) -
        ∫ t in (0 : ℝ)..T, (((t + 2)⁻¹ : ℝ) : ℂ) * phase v t := by
  let f := fun t : ℝ => (Real.log (t + 2) : ℂ)
  let f' := fun t : ℝ => (((t + 2)⁻¹ : ℝ) : ℂ)
  let z := (v : ℂ) * Complex.I
  have hs {x : ℝ} (hx : x ∈ uIcc 0 T) : 0 ≤ x := by
    rw [uIcc_of_le hT] at hx
    exact hx.1
  have hf (t : ℝ) (ht : t ∈ uIcc 0 T) : HasDerivAt f (f' t) t :=
    (shifted_log_hasDerivAt (hs ht)).ofReal_comp
  have hf' : ContinuousOn f' (uIcc 0 T) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    exact (continuous_id.continuousOn.add continuousOn_const).inv₀
      (fun t ht => by have := hs ht; change t + 2 ≠ 0; linarith)
  have hg' : Continuous (fun t => z * phase v t) :=
    continuous_const.mul (continuous_iff_continuousAt.mpr (fun t => (phase_deriv v t).continuousAt))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf (fun t _ => phase_deriv v t)
    hf'.intervalIntegrable (hg'.intervalIntegrable _ _)
  calc
    _ = ∫ t in (0 : ℝ)..T, f t * (z * phase v t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      change z * (f t * phase v t) = _
      ring
    _ = _ := by simpa [f, f', phase] using hparts

/-- Explicit bound for the individual term n^(it) log(t+2) of the BGSTB
cross integral. It holds for every real n > 1 and every T ≥ 0. -/
theorem norm_log_phase_integral_le {n T : ℝ} (hn : 1 < n) (hT : 0 ≤ T) :
    ‖∫ t in (0 : ℝ)..T, (Real.log (t + 2) : ℂ) * phase (Real.log n) t‖ ≤
      2 * Real.log (T + 2) / Real.log n := by
  let v := Real.log n
  let g := fun t : ℝ => (((t + 2)⁻¹ : ℝ) : ℂ) * phase v t
  let a := (Real.log (T + 2) : ℂ) * phase v T
  let b := (Real.log 2 : ℂ)
  have hv : 0 < v := Real.log_pos hn
  have hlog : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ha : ‖a‖ = Real.log (T + 2) := by
    simp only [a, norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog]
  have hb : ‖b‖ = Real.log 2 := by
    simp only [b, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog2]
  have hr : ‖∫ t in (0 : ℝ)..T, g t‖ ≤ Real.log (T + 2) - Real.log 2 := by
    have hd : ContinuousOn (fun t : ℝ => (t + 2)⁻¹) (uIcc 0 T) := by
      exact (continuous_id.continuousOn.add continuousOn_const).inv₀ (fun t ht => by
        rw [uIcc_of_le hT] at ht
        change t + 2 ≠ 0
        linarith [ht.1])
    calc
      ‖∫ t in (0 : ℝ)..T, g t‖ ≤ ∫ t in (0 : ℝ)..T, ‖g t‖ := by
        simp only [intervalIntegral.integral_of_le hT]
        exact norm_integral_le_integral_norm _
      _ = ∫ t in (0 : ℝ)..T, (t + 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        have ht' : 0 ≤ (t + 2)⁻¹ := inv_nonneg.mpr (by linarith [ht.1])
        simp only [g, norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht']
      _ = Real.log (T + 2) - Real.log 2 := by
        simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => shifted_log_hasDerivAt (show 0 ≤ t by rw [uIcc_of_le hT] at ht; exact ht.1))
          hd.intervalIntegrable
  have hz : ‖(v : ℂ) * Complex.I‖ = v := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  let J := ∫ t in (0 : ℝ)..T, (Real.log (t + 2) : ℂ) * phase v t
  apply (le_div_iff₀ hv).mpr
  calc
    ‖J‖ * v = ‖((v : ℂ) * Complex.I) * J‖ := by rw [norm_mul, hz, mul_comm]
    _ = ‖a - b - ∫ t in (0 : ℝ)..T, g t‖ :=
      congrArg (fun z : ℂ => ‖z‖) (log_phase_integral_parts v hT)
    _ ≤ ‖a - b‖ + ‖∫ t in (0 : ℝ)..T, g t‖ := norm_sub_le _ _
    _ ≤ (‖a‖ + ‖b‖) + (Real.log (T + 2) - Real.log 2) := add_le_add (norm_sub_le _ _) hr
    _ = _ := by rw [ha, hb]; ring

end RiemannResearch.Analysis.MontgomeryLogPhaseIntegral
