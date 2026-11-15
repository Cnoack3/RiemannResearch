/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergIngham
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.ActualSelbergDyadicAssembly
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selberg assembly on the actual logarithmically truncated near-line strip

Source for the analytic ranges: Baluyot (2017), Lemma 3.2.1 and equations
(3.6.11)--(3.6.13) of *On the Zeros of Riemann's Zeta-function*:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The near-line input starts at 1/2 + A/log T and retains the logarithmic
boundary cost. Total counting handles the additional shift range and a
positive exponent absorbs the boundary cost. The analytic input remains
explicit, as does the away-line estimate of Ingham.
-/

noncomputable section
open Set

namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem log_le_density_power_div {T a η σ : ℝ} (hT : 1 ≤ T) (ha : 0 ≤ a)
    (hp : 0 < 1 - a * η) (hσ : σ ≤ 1 / 2 + η) :
    Real.log T ≤ T ^ (1 - a * (σ - 1 / 2)) / (1 - a * η) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  apply (le_div_iff₀ hp).2
  calc
    _ ≤ T ^ (1 - a * η) := by
      rw [Real.rpow_def_of_pos hT0]
      linarith only [Real.add_one_le_exp (Real.log T * (1 - a * η))]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT (by
      nlinarith only [mul_le_mul_of_nonneg_left
        (show σ - 1 / 2 ≤ η by linarith only [hσ]) ha])

/-- The near-line estimate is needed only on its source strip, with the
original logarithmic error. An independently proved Ingham estimate supplies
the away-line windows. Both bounds remain explicit hypotheses. -/
theorem uniformSelbergDensity_of_truncated_near_excess_and_ingham
    {a η A : ℝ} (ha : 0 < a) (ha' : a < 4 / 3) (hη : 0 < η) (hp : 0 < 1 - a * η)
    (hI : InghamDensityBound)
    (hnear : ∃ D E H : ℝ, 0 ≤ D ∧ 0 ≤ E ∧ 1 < H ∧
      ∀ T : ℝ, H ≤ T → ∀ α ∈ Icc (1 / 2 + A / Real.log T) (1 / 2 + η),
        rightLogExcessWindow (T / 2) T α ≤
          D * T * Real.exp (-(a * Real.log T) * (α - 1 / 2)) + E * Real.log T) :
    UniformSelbergDensity a := by
  obtain ⟨D, E, H₁, hD, hE, hH₁, hnear⟩ := hnear
  obtain ⟨F, H₂, hF, hH₂, hfar⟩ := exists_selberg_far_windows_of_ingham ha' hη hI
  obtain ⟨B, hB, hband⟩ := exists_selberg_form_on_logarithmic_strip a (A + 1 / a) ha.le
  let H : ℝ := max (max H₁ H₂) 9
  let M : ℝ := a * Real.exp 1 * D + a * E / (1 - a * η)
  let K : ℝ := max B (max M F)
  have hH : 1 < H := hH₁.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  have hBK : B ≤ K := le_max_left _ _
  have hMK : M ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hFK : F ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  apply uniformSelbergDensity_of_dyadic_windows ha.le (by linarith)
  refine ⟨K, H, hB.le.trans hBK, hH, ?_⟩
  intro T hT σ hσ
  have hHT : H ≤ T := by linarith
  have hT₁ : H₁ ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hHT
  have hT₂ : H₂ ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hHT
  have hT9 : 9 ≤ T := (le_max_right _ _).trans hHT
  have hT1 : 1 < T := hH.trans_le hHT
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  have enlarge {C : ℝ} (hCK : C ≤ K) :
      C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T ≤
        K * T ^ (1 - a * (σ - 1 / 2)) * Real.log T :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg hT0.le _)) hL.le
  by_cases hs : 1 / 2 + η ≤ σ
  · exact (hfar T hT₂ σ ⟨hs, hσ.2⟩).trans (enlarge hFK)
  by_cases hb : (σ - 1 / 2) * Real.log T ≤ A + 1 / a
  · have hw : rightInclusiveWindow (T / 2) T σ ≤ rightInclusiveCount T σ := by
      rw [rightInclusiveWindow_eq_sub (show T / 2 ≤ T by linarith)]
      exact sub_le_self _ (rightInclusiveCount_nonneg _ _)
    exact hw.trans ((hband T hT9 σ hb).trans (enlarge hBK))
  · have hq : 0 < a * Real.log T := mul_pos ha hL
    have hthin : (A + 1 / a) / Real.log T ≤ σ - 1 / 2 :=
      ((div_le_iff₀ hL).2 (le_of_not_ge hb))
    have hsum : A / Real.log T + 1 / (a * Real.log T) =
        (A + 1 / a) / Real.log T := by
      field_simp [ha.ne', hL.ne']
    rw [← hsum] at hthin
    have hshift : σ - 1 / (a * Real.log T) ∈
        Icc (1 / 2 + A / Real.log T) (1 / 2 + η) :=
      ⟨by linarith, by linarith [one_div_pos.mpr hq]⟩
    have hw := densityWindow_le_of_shifted_logExcess hT1 ha (hnear T hT₁ _ hshift)
    have hlog := log_le_density_power_div hT1.le ha.le hp (le_of_not_ge hs)
    have herror : a * E * (Real.log T) ^ 2 ≤
        (a * E / (1 - a * η)) * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
      calc
        _ = (a * E * Real.log T) * Real.log T := by ring
        _ ≤ (a * E * Real.log T) * (T ^ (1 - a * (σ - 1 / 2)) / (1 - a * η)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (a * Real.exp 1 * D) *
            (T * Real.log T * Real.exp (-(a * Real.log T) * (σ - 1 / 2))) +
          a * E * (Real.log T) ^ 2 := by
        (convert hw using 1; ring)
      _ ≤ M * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
        rw [← selberg_power_kernel_eq_exp T a σ hT0]
        dsimp [M]
        nlinarith only [herror]
      _ ≤ _ := enlarge hMK

end RiemannResearch.Analysis.ActualZeroOrdinate
