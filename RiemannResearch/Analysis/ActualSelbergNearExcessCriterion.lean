/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamDensityBound
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.ActualSelbergTransitionWindow
import RiemannResearch.Analysis.ActualSelbergTruncatedNearLine
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualZeroLogExcessIntegral
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Near-line log-excess criteria for Z03

The classical Ingham provider is now available for the actual inclusive zero
count. This discharges the away-line input in the Z03 checkpoint. The target
is equivalent to the stated truncated near-line log-excess estimate. For
slopes below `4/3`, the required estimate can instead be restricted to the
moving transition window.

The near/away-line strategy and shifted count are the ones in Baluyot,
*On the Zeros of Riemann's Zeta-function* (2017), §3.6, and the
[RiemannResearch Ingham / Z03 checkpoint](https://riemann-ingham-z03-checkpoint-20261116.dreamymeter1.chatgpt.site).
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Integrate the Selberg profile while retaining its upper-endpoint term. -/
theorem rightLogExcessWindow_le_of_selbergDensity {H T α C a : ℝ}
    (hHT : H ≤ T) (hT : 1 < T) (ha : 0 < a) (hα : α ∈ Icc (1 / 2 : ℝ) 1)
    (hD : SelbergDensityBound T C a) :
    rightLogExcessWindow H T α ≤
      C / a * T * (Real.exp (-(a * Real.log T) * (α - 1 / 2)) -
        Real.exp (-(a * Real.log T) * (1 - 1 / 2))) := by
  have hT₀ : 0 < T := by linarith
  let q := a * Real.log T
  let profile (σ : ℝ) := C * T * Real.log T * Real.exp (-q * (σ - 1 / 2))
  have hcont : Continuous profile := by
    dsimp [profile]
    fun_prop
  have hmono : (∫ σ in α..(1 : ℝ), rightInclusiveWindow H T σ) ≤
      ∫ σ in α..(1 : ℝ), profile σ := by
    apply intervalIntegral.integral_mono_on hα.2
      (intervalIntegrable_rightInclusiveWindow H T α 1) (hcont.intervalIntegrable α 1)
    intro σ hσ
    rw [rightInclusiveWindow_eq_sub hHT]
    exact (sub_le_self _ (rightInclusiveCount_nonneg _ _)).trans
      ((selbergDensityBound_iff_exp T C a hT₀).mp hD σ ⟨hα.1.trans hσ.1, hσ.2⟩)
  let F (σ : ℝ) := -(C / a * T) * Real.exp (-q * (σ - 1 / 2))
  have hderiv (σ : ℝ) : HasDerivAt F (profile σ) σ := by
    have hlin : HasDerivAt (fun x : ℝ => -q * (x - 1 / 2)) (-q) σ := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id σ).sub_const (1 / 2 : ℝ)).const_mul (-q)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-q * (x - 1 / 2)))
        (Real.exp (-q * (σ - 1 / 2)) * (-q)) σ := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (-q * (σ - 1 / 2))).comp σ hlin
    have hrate :
        -(C / a * T) * (Real.exp (-q * (σ - 1 / 2)) * (-q)) = profile σ := by
      dsimp [profile, q]
      field_simp [ha.ne']
    have h := hexp.const_mul (-(C / a * T))
    rw [hrate] at h
    exact h
  rw [rightLogExcessWindow_eq_integral_rightInclusiveWindow H T α hα.2]
  calc
    _ ≤ ∫ σ in α..(1 : ℝ), profile σ := hmono
    _ = _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hderiv t) (hcont.intervalIntegrable α 1)]
      dsimp [F, q]
      ring

/-- A uniform Selberg estimate gives a dyadic excess envelope with the same
exponent and no additional logarithmic term. -/
theorem exists_dyadic_logExcess_of_uniformSelbergDensity {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧ ∀ T : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
      rightLogExcessWindow (T / 2) T α ≤
        D * T * Real.exp (-(a * Real.log T) * (α - 1 / 2)) := by
  obtain ⟨C, H, hC, hH, hb⟩ := hD
  refine ⟨C / a, H, div_nonneg hC ha.le, hH, ?_⟩
  intro T hT α hα
  have hT₁ := hH.trans_le hT
  have hT₀ : 0 ≤ T := by linarith
  exact (rightLogExcessWindow_le_of_selbergDensity (by linarith) hT₁ ha hα
    (hb T hT)).trans (mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_nonneg _))
      (mul_nonneg (div_nonneg hC ha.le) hT₀))

/-- The fixed-strip near-line excess estimate recorded as Z1 in the
Ingham / Z03 checkpoint. -/
def UniformSelbergTruncatedNearExcess (a : ℝ) : Prop :=
  ∃ η A D E H : ℝ, 0 < η ∧ 0 < 1 - a * η ∧ 0 ≤ D ∧ 0 ≤ E ∧ 1 < H ∧
    ∀ T : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 + A / Real.log T) (1 / 2 + η),
      rightLogExcessWindow (T / 2) T α ≤
        D * T * Real.exp (-(a * Real.log T) * (α - 1 / 2)) + E * Real.log T

/-- Exact criterion for the checkpoint's fixed-strip route, using the
unconditional Ingham theorem. -/
theorem uniformSelbergDensity_iff_truncated_near_excess {a : ℝ}
    (ha : 0 < a) (ha' : a ≤ 4 / 3) :
    UniformSelbergDensity a ↔ UniformSelbergTruncatedNearExcess a := by
  constructor
  · intro h
    obtain ⟨D, H, hD, hH, hb⟩ := exists_dyadic_logExcess_of_uniformSelbergDensity ha h
    refine ⟨1 / 2, 0, D, 0, H, by norm_num, by linarith only [ha'], hD, le_rfl, hH, ?_⟩
    intro T hT α hα
    have hα' : α ∈ Icc (1 / 2 : ℝ) 1 := by
      simpa only [zero_div, add_zero, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using hα
    simpa only [zero_mul, add_zero] using hb T hT α hα'
  · rintro ⟨η, A, D, E, H, hη, hp, hD, hE, hH, hbound⟩
    exact uniformSelbergDensity_of_truncated_near_excess_and_ingham
      ha ha' hη hp inghamDensityBound ⟨D, E, H, hD, hE, hH, hbound⟩

/-- A dyadic excess envelope is needed only in the transition range. The
optimized shift decreases the scaled threshold by `1/a`, so the lower cut
for applying the count criterion is `A + 1/a`. -/
theorem uniformSelbergDensity_iff_dyadic_transition_logExcess {a : ℝ}
    (A : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (ha' : a < 4 / 3) :
    UniformSelbergDensity a ↔
      ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧ ∀ T : ℝ, 2 * H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
        A < (α - 1 / 2) * Real.log T →
        (4 / 3 - a) * ((α - 1 / 2) * Real.log T) < 2 * Real.log (Real.log T) →
        rightLogExcessWindow (T / 2) T α ≤
          D * T * Real.exp (-(a * Real.log T) * (α - 1 / 2)) := by
  constructor
  · intro h
    obtain ⟨D, H, hD, hH, hb⟩ := exists_dyadic_logExcess_of_uniformSelbergDensity ha h
    exact ⟨D, H, hD, hH, fun T hT α hα _ _ => hb T (by linarith) α hα⟩
  · rintro ⟨D, H, hD, hH, hb⟩
    apply (uniformSelbergDensity_iff_dyadic_transition (A + 1 / a) ha.le ha').mpr
    refine ⟨a * Real.exp 1 * D, H, by positivity, hH, ?_⟩
    intro T hT σ hσ hlo hhi
    have hT₁ : 1 < T := by linarith
    have hT₀ : 0 < T := by linarith
    have hlog := Real.log_pos hT₁
    have hgap : 0 < 1 / (a * Real.log T) := one_div_pos.mpr (mul_pos ha hlog)
    let α := σ - 1 / (a * Real.log T)
    have hshift : (α - 1 / 2) * Real.log T =
        (σ - 1 / 2) * Real.log T - 1 / a := by
      dsimp [α]
      field_simp [ha.ne', hlog.ne']
      ring
    have halow : A < (α - 1 / 2) * Real.log T := by
      rw [hshift]
      linarith only [hlo]
    have hastrip : α ∈ Icc (1 / 2 : ℝ) 1 :=
      ⟨sub_nonneg.mp (nonneg_of_mul_nonneg_left (hA.trans halow.le) hlog),
        (sub_le_self σ hgap.le).trans hσ.2⟩
    have hamove : (α - 1 / 2) * Real.log T ≤ (σ - 1 / 2) * Real.log T := by
      rw [hshift]
      exact sub_le_self _ (one_div_nonneg.mpr ha.le)
    have hahigh := (mul_le_mul_of_nonneg_left hamove (sub_nonneg.mpr ha'.le)).trans_lt hhi
    have hcount := densityWindow_le_of_shifted_logExcess
      (H := T / 2) (σ := σ) (D := D) (E := 0) hT₁ ha
      (by simpa only [α, zero_mul, add_zero] using hb T hT α hastrip halow hahigh)
    calc
      _ ≤ (a * Real.exp 1 * D) *
          (T * Real.log T * Real.exp (-(a * Real.log T) * (σ - 1 / 2))) := by
        simpa only [zero_mul, mul_zero, add_zero, mul_assoc] using hcount
      _ = _ := by rw [← selberg_power_kernel_eq_exp T a σ hT₀]; ring

/-- Z03 at the quarter exponent, with the exact transition constant `24/13`. -/
theorem uniformSelbergDensity_quarter_iff_dyadic_transition_logExcess (A : ℝ) (hA : 0 ≤ A) :
    UniformSelbergDensity (1 / 4) ↔
      ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧ ∀ T : ℝ, 2 * H ≤ T → ∀ α ∈ Icc (1 / 2 : ℝ) 1,
        A < (α - 1 / 2) * Real.log T →
        (α - 1 / 2) * Real.log T < (24 / 13) * Real.log (Real.log T) →
        rightLogExcessWindow (T / 2) T α ≤
          D * T * Real.exp (-((1 / 4 : ℝ) * Real.log T) * (α - 1 / 2)) := by
  have hfactor (u v : ℝ) : (4 / 3 - (1 / 4 : ℝ)) * u < 2 * v ↔ u < (24 / 13) * v := by
    constructor <;> intro h <;> linarith only [h]
  simpa only [hfactor] using
    uniformSelbergDensity_iff_dyadic_transition_logExcess
      (a := (1 / 4 : ℝ)) A hA (by norm_num) (by norm_num)

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_iff_truncated_near_excess' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformSelbergDensity_iff_truncated_near_excess

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.uniformSelbergDensity_quarter_iff_dyadic_transition_logExcess' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms uniformSelbergDensity_quarter_iff_dyadic_transition_logExcess

end RiemannResearch.Analysis.ActualZeroOrdinate
