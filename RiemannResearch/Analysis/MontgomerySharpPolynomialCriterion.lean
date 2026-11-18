/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFejerCertificate
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A polynomial-growth RH criterion for the complex form factor

The unnormalized complex form factor is the weighted Landau energy
`sharpIntegral`. A separate analytic input gives a cutoff-uniform exponential
lower bound from one fixed right-half zero. Given this input, a polynomial
upper bound at cofinal heights yields an explicit bound for that zero's
horizontal displacement. A common polynomial exponent at arbitrarily large
normalized frequencies then forces RH.
-/

noncomputable section

open MeasureTheory Zeta23
namespace RiemannResearch.Analysis.MontgomeryHorizontalTransfer

open ActualZeroOrdinate MontgomeryFormFactor

/-- A fixed right-half zero supplies a lower bound for the complex energy
at every later cutoff. The constant may depend on the zero. -/
def FixedRightZeroSharpIntegralLower : Prop :=
  ∀ (H : ℝ) (ρ : ℂ), ρ ∈ cutoff H → 1 / 2 < ρ.re →
    ∃ c : ℝ, 0 < c ∧ ∀ T u : ℝ, 1 < T → ρ.im ≤ T → 0 ≤ u →
      c * Real.exp (2 * (ρ.re - 1 / 2) * u) ≤ sharpIntegral T u

/-- A bounded linear map on the weighted \(L^2\) signal isolates a fixed
right-half zero with a cutoff-independent norm. -/
def FixedRightZeroSharpSeparator : Prop :=
  ∀ (H : ℝ) (ρ : ℂ), ρ ∈ cutoff H → 1 / 2 < ρ.re →
    ∃ (ℓ : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ) (b : ℝ), 0 < b ∧
      ∀ T u : ℝ, 1 < T → ρ.im ≤ T → 0 ≤ u →
        ‖ℓ ((weightedLandau_memLp T u).toLp (weightedLandau T u))‖ =
          b * Real.exp ((ρ.re - 1 / 2) * u)

/-- The operator norm of a separator supplies the fixed-zero energy lower
bound uniformly in both the cutoff and the displacement parameter. -/
theorem fixedRightZeroSharpIntegralLower_of_separator
    (h : FixedRightZeroSharpSeparator) : FixedRightZeroSharpIntegralLower := by
  intro H ρ hρ hβ
  obtain ⟨ℓ, b, hb, heval⟩ := h H ρ hρ hβ
  have hℓ : 0 < ‖ℓ‖ + 1 := by positivity
  refine ⟨(b / (‖ℓ‖ + 1)) ^ 2, by positivity, ?_⟩
  intro T u hT hγ hu
  let g := (weightedLandau_memLp T u).toLp (weightedLandau T u)
  have hnorm : Real.sqrt (sharpIntegral T u) = ‖g‖ := by
    have hint := MontgomeryComplexGram.sqrt_integral_sq_norm (weightedLandau_memLp T u)
    simpa only [weightedLandau, weighted_mul_sq, sharpIntegral] using hint
  have hnonneg : 0 ≤ sharpIntegral T u := by
    unfold sharpIntegral
    exact integral_nonneg (fun s => by positivity)
  have hop := ℓ.le_opNorm g
  change ‖ℓ ((weightedLandau_memLp T u).toLp (weightedLandau T u))‖ ≤ ‖ℓ‖ * ‖g‖ at hop
  rw [heval T u hT hγ hu] at hop
  have hbound :
      b / (‖ℓ‖ + 1) * Real.exp ((ρ.re - 1 / 2) * u) ≤ ‖g‖ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hℓ).2
    exact hop.trans (by nlinarith [norm_nonneg g])
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤
      b / (‖ℓ‖ + 1) * Real.exp ((ρ.re - 1 / 2) * u)) hbound 2
  rw [← hnorm, Real.sq_sqrt hnonneg, mul_pow, pow_two (Real.exp _), ← Real.exp_add] at hsq
  have hearg : (ρ.re - 1 / 2) * u + (ρ.re - 1 / 2) * u =
      2 * (ρ.re - 1 / 2) * u := by ring
  simpa only [hearg] using hsq

/-- A common polynomial exponent bounds the unnormalized complex form factor
at cofinal heights above every fixed frequency floor. The multiplicative
constant may depend on that floor. The frequency may move with the cutoff. -/
def CofinalSharpPolynomialUpper : Prop :=
  ∃ M : ℝ, ∀ A : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, ∃ T α : ℝ,
    Y ≤ T ∧ 1 < T ∧ A ≤ α ∧
      sharpIntegral T (α * Real.log T) ≤ C * Real.exp (M * Real.log T)

/-- A polynomial bound of exponent \(M\) at frequencies at least \(A\)
forces \(2A(\beta-1/2)\le M\) for each fixed right-half zero. -/
theorem rightZero_exponent_le_of_cofinal_sharpIntegral_upper
    (hlower : FixedRightZeroSharpIntegralLower) {H A M C : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ cutoff H) (hβ : 1 / 2 < ρ.re) (hA : 0 ≤ A) (hC : 0 < C)
    (hupper : ∀ Y : ℝ, ∃ T α : ℝ, Y ≤ T ∧ 1 < T ∧ A ≤ α ∧
      sharpIntegral T (α * Real.log T) ≤ C * Real.exp (M * Real.log T)) :
    2 * A * (ρ.re - 1 / 2) ≤ M := by
  by_contra! hm
  obtain ⟨c, hc, hρlower⟩ := hlower H ρ hρ hβ
  let d : ℝ := 2 * A * (ρ.re - 1 / 2) - M
  have hd : 0 < d := sub_pos.mpr hm
  let y : ℝ := (Real.log (C / c) + 1) / d
  obtain ⟨T, α, hYT, hT, hAα, hupperT⟩ :=
    hupper (max ρ.im (Real.exp y))
  have hγT : ρ.im ≤ T := (le_max_left _ _).trans hYT
  have hyT : Real.exp y ≤ T := (le_max_right _ _).trans hYT
  have hlog : y ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos y) hyT
  have hlogDiff : Real.log (C / c) + 1 ≤ Real.log T * d :=
    (div_le_iff₀ hd).mp hlog
  have hexpDiff : C / c < Real.exp (d * Real.log T) := by
    rw [← Real.exp_log (div_pos hC hc), Real.exp_lt_exp]
    linarith
  have habs : C < Real.exp (d * Real.log T) * c := (div_lt_iff₀ hc).mp hexpDiff
  have hL : 0 ≤ Real.log T := (Real.log_pos hT).le
  have hδ : 0 ≤ ρ.re - 1 / 2 := sub_nonneg.mpr hβ.le
  have hscaled :
      2 * A * (ρ.re - 1 / 2) * Real.log T ≤
        2 * (ρ.re - 1 / 2) * (α * Real.log T) := by
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAα (by norm_num : 0 ≤ (2 : ℝ))) hδ) hL
    rw [show 2 * (ρ.re - 1 / 2) * (α * Real.log T) =
      2 * α * (ρ.re - 1 / 2) * Real.log T by ring]
    exact hp
  have hstrict :
      C * Real.exp (M * Real.log T) <
        c * Real.exp (2 * A * (ρ.re - 1 / 2) * Real.log T) := by
    calc
      _ < (Real.exp (d * Real.log T) * c) * Real.exp (M * Real.log T) :=
        mul_lt_mul_of_pos_right habs (Real.exp_pos _)
      _ = c * Real.exp (d * Real.log T + M * Real.log T) := by
        rw [Real.exp_add]
        ring
      _ = _ := by
        congr 2
        dsimp [d]
        ring
  have hρlowerT := hρlower T (α * Real.log T) hT hγT
    (mul_nonneg (hA.trans hAα) hL)
  exact (not_lt_of_ge hupperT)
    (hstrict.trans_le ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscaled) hc.le).trans
      hρlowerT))

/-- A uniform exponent at arbitrarily large frequencies, together with the
fixed-zero lower bound, implies RH. -/
theorem riemannHypothesis_of_cofinal_sharpPolynomialUpper
    (hlower : FixedRightZeroSharpIntegralLower) (hupper : CofinalSharpPolynomialUpper) :
    RiemannHypothesis := by
  have hright (H : ℝ) (ρ : ℂ) (hρ : ρ ∈ cutoff H) : ¬ 1 / 2 < ρ.re := by
    intro hβ
    obtain ⟨M, hM⟩ := hupper
    let A : ℝ := (|M| + 1) / (2 * (ρ.re - 1 / 2))
    have hδ : 0 < ρ.re - 1 / 2 := sub_pos.mpr hβ
    have hA : 0 ≤ A := div_nonneg (by positivity) (by positivity)
    obtain ⟨C, hC, hCofinal⟩ := hM A
    have hb := rightZero_exponent_le_of_cofinal_sharpIntegral_upper
      hlower hρ hβ hA hC hCofinal
    have hAeq : 2 * A * (ρ.re - 1 / 2) = |M| + 1 := by
      calc
        2 * A * (ρ.re - 1 / 2) = A * (2 * (ρ.re - 1 / 2)) := by ring
        _ = |M| + 1 := div_mul_cancel₀ _ (by positivity : 2 * (ρ.re - 1 / 2) ≠ 0)
    rw [hAeq] at hb
    linarith [le_abs_self M]
  apply cofinal_fejer_critical_line_iff_RH.mp
  apply cofinal_fejer_critical_line_iff.mpr
  intro H ρ hρ
  by_contra hn
  rcases lt_or_gt_of_ne hn with hβ | hβ
  · apply hright H (reflect ρ) (reflect_mem hρ)
    rw [reflect_re]
    linarith
  · exact hright H ρ hρ hβ

/-- In the presence of a fixed-zero separator, the cofinal polynomial upper
bound proves RH. -/
theorem riemannHypothesis_of_cofinal_sharpPolynomialUpper_of_separator
    (hseparator : FixedRightZeroSharpSeparator) (hupper : CofinalSharpPolynomialUpper) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_sharpPolynomialUpper
    (fixedRightZeroSharpIntegralLower_of_separator hseparator) hupper

end RiemannResearch.Analysis.MontgomeryHorizontalTransfer
