/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryPositiveGapDensity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed integrated positive-gap criterion

The triangle identity from Goldston, Lee, Schettler and Suriajaya,
arXiv:2503.15449v2, §2, underlies Equation (12) of the user-provided note
`Montgomery_Pair_Correlation_Without_RH.md`. The two signed deficits
are evaluated at the same width. The reduction uses neither RH nor PCC.
-/

noncomputable section
open Filter MeasureTheory Set intervalIntegral Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance

/-- The positive-half-line triangular integral of the sine-kernel hole. -/
def sineHoleTriangle (R : ℝ) : ℝ :=
  (2 / R) * ∫ s in (0 : ℝ)..R, (R - s) * Real.sinc (Real.pi * s) ^ 2

/-- The signed, integrated shortfall of the actual positive gaps from the model. -/
def integratedGapDeficit (T R : ℝ) : ℝ :=
  (2 / R) * ((∫ u in (0 : ℝ)..R, sineGapMass u) -
    ∫ u in (0 : ℝ)..R, positiveGapMass T u)

/-- The signed excess of the unfolded physical triangle over the square of its width. -/
def shortWindowMomentDeficit (T R : ℝ) : ℝ :=
  (actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) - R ^ 2) / R

private theorem continuous_sineGapMass : Continuous sineGapMass := by
  apply continuous_primitive
  intro a b
  have hc : Continuous (fun u : ℝ => 1 - Real.sinc (Real.pi * u) ^ 2) := by fun_prop
  exact hc.intervalIntegrable a b

/-- Integrating the sine process's gap mass retains the full triangular sine-hole term. -/
theorem integral_sineGapMass (R : ℝ) :
    (∫ u in (0 : ℝ)..R, sineGapMass u) =
      R ^ 2 / 2 - (∫ s in (0 : ℝ)..R, (R - s) * Real.sinc (Real.pi * s) ^ 2) := by
  let k := fun x : ℝ => Real.sinc (Real.pi * x) ^ 2
  let K := fun u : ℝ => ∫ s in (0 : ℝ)..u, k s
  let J := fun u : ℝ => ∫ s in (0 : ℝ)..u, s * k s
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hsk : Continuous (fun s : ℝ => s * k s) := continuous_id.mul hk
  have hK (u : ℝ) : HasDerivAt K (k u) u :=
    integral_hasDerivAt_right (hk.intervalIntegrable 0 u)
      hk.stronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hcont : Continuous K := continuous_iff_continuousAt.mpr
    (fun u => (hK u).continuousAt)
  have hparts : (∫ u in (0 : ℝ)..R, K u) = R * K R - J R := by
    have hid (u : ℝ) : HasDerivAt (fun x : ℝ => x) (1 : ℝ) u := hasDerivAt_id u
    have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := R) (fun u _ => hid u) (fun u _ => hK u)
      intervalIntegrable_const (hk.intervalIntegrable 0 R)
    simp only [one_mul, zero_mul, sub_zero] at hp
    change J R = R * K R - (∫ u in (0 : ℝ)..R, K u) at hp
    linarith only [hp]
  have hgap (u : ℝ) : sineGapMass u = u - K u := by
    unfold sineGapMass K
    rw [integral_sub intervalIntegrable_const (hk.intervalIntegrable _ _)]
    simp
  have hweighted : (∫ s in (0 : ℝ)..R, (R - s) * k s) = R * K R - J R := by
    simp_rw [sub_mul]
    rw [integral_sub ((hk.const_mul R).intervalIntegrable 0 R) (hsk.intervalIntegrable 0 R),
      intervalIntegral.integral_const_mul]
  have hid : Continuous (fun u : ℝ => u) := continuous_id
  simp_rw [hgap]
  rw [integral_sub (hid.intervalIntegrable 0 R) (hcont.intervalIntegrable 0 R),
    integral_id, hparts, ← hweighted]
  ring

theorem sineHoleTriangle_le_one {R : ℝ} (hR : 0 < R) : sineHoleTriangle R ≤ 1 := by
  have hline : Continuous (fun u : ℝ => u - 1 / 2) := by fun_prop
  have hlow : (∫ u in (0 : ℝ)..R, u - 1 / 2) ≤ ∫ u in (0 : ℝ)..R, sineGapMass u :=
    intervalIntegral.integral_mono_on hR.le (hline.intervalIntegrable _ _)
      (continuous_sineGapMass.intervalIntegrable _ _) (fun u hu => sineGapMass_lower hu.1)
  have hlin : (∫ u in (0 : ℝ)..R, u - 1 / 2) = R ^ 2 / 2 - R / 2 := by
    have hid : Continuous (fun u : ℝ => u) := continuous_id
    rw [integral_sub (hid.intervalIntegrable 0 R) intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [hlin, integral_sineGapMass] at hlow
  unfold sineHoleTriangle
  have hI : (∫ s in (0 : ℝ)..R, (R - s) * Real.sinc (Real.pi * s) ^ 2) ≤ R / 2 := by
    linarith only [hlow]
  calc
    _ ≤ (2 / R) * (R / 2) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp [hR.ne']

/-- Exact normalized collision mass, keeping both signed deficits. -/
theorem collision_div_main_eq_signed_gap_deficits {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) =
      sineHoleTriangle R + shortWindowMomentDeficit T R + integratedGapDeficit T R := by
  unfold shortWindowMomentDeficit integratedGapDeficit sineHoleTriangle
  rw [physicalTriangle_eq_collision_add_positive_gaps hT hR.le, integral_sineGapMass]
  field_simp [hR.ne']
  ring

/-- One upper bound on the sum of the signed deficits at a common fixed
width suffices. Each width may depend on the requested error. -/
theorem collision_limit_of_integratedGapDeficits
    (h : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ᶠ T : ℝ in atTop,
      shortWindowMomentDeficit T R + integratedGapDeficit T R ≤ ε) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) atTop
      (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [tendsto_count_div_mainTerm.eventually (lt_mem_nhds ha),
      eventually_gt_atTop (1 : ℝ)] with T hn hT
    have hC : Ncount 0 T ≤ actualCollision T := by
      rw [actualCollision_eq_count_add_excess T]
      omega
    have hD : 0 ≤ T * Real.log T / (2 * Real.pi) :=
      div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le))
        (by positivity)
    exact hn.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hC) hD)
  · intro b hb
    obtain ⟨R, hR, hwindow⟩ := h ((b - 1) / 2) (by linarith)
    have hr := zero_lt_one.trans_le hR
    filter_upwards [hwindow, eventually_gt_atTop (1 : ℝ)] with T hdef hT
    rw [collision_div_main_eq_signed_gap_deficits hT hr]
    linarith only [sineHoleTriangle_le_one hr, hdef, hb]

/-- Density one from the common-width signed upper bound. The sum permits
compensation between the two deficits at the chosen width. -/
theorem density_one_of_integratedGapDeficits
    (h : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ᶠ T : ℝ in atTop,
      shortWindowMomentDeficit T R + integratedGapDeficit T R ≤ ε) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  density_one_of_collision_limit (collision_limit_of_integratedGapDeficits h)

end RiemannResearch.Analysis.MontgomeryPositiveGap
