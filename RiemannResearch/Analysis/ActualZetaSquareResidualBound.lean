/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SmoothedDivisorDyadicMoment
import RiemannResearch.Analysis.ActualZetaSquareRemainderIdentity
import RiemannResearch.Analysis.ActualZetaSquareRightHeadMoment
import RiemannResearch.Analysis.ZetaSquareInfiniteTailMoment
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ActualZetaSquareMovingResidue
import RiemannResearch.Analysis.ActualZetaFourthMomentDyadic

/-!
# Unconditional uniform actual zeta-square remainder and fourth moment

The exact contour identity decomposes the actual residual into the smoothing
defect, the moving double-pole residue, the right finite-head integral, and the
left infinite-tail integral. All four terms have proved uniform second moments.
This supplies the actual dyadic residual provider and closes Ingham obligation I1.

The contour proof is uniform for every integer cutoff with `U / 2 ≤ N ≤ U`,
not only the canonical floor cutoff. The final fourth-moment theorem has no
supplied moment, growth, contour, or residual premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis

private theorem norm_sub_three_sq_le (a b c d : ℂ) :
    ‖a-b-c-d‖ ^ 2 ≤ 4*(‖a‖ ^ 2+‖b‖ ^ 2+‖c‖ ^ 2+‖d‖ ^ 2) := by
  have hn : ‖a-b-c-d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    have h1 := norm_sub_le (a-b-c) d
    have h2 := norm_sub_le (a-b) c
    have h3 := norm_sub_le a b
    linarith
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖a‖-‖b‖), sq_nonneg (‖a‖-‖c‖),
    sq_nonneg (‖a‖-‖d‖), sq_nonneg (‖b‖-‖c‖),
    sq_nonneg (‖b‖-‖d‖), sq_nonneg (‖c‖-‖d‖)]

private theorem four_piece_moment_le {R A B C D : ℝ → ℂ} {H T : ℝ}
    (hHT : H ≤ T) (hR : Continuous R)
    (hA : IntervalIntegrable (fun t => ‖A t‖ ^ 2) volume H T)
    (hB : IntervalIntegrable (fun t => ‖B t‖ ^ 2) volume H T)
    (hC : IntervalIntegrable (fun t => ‖C t‖ ^ 2) volume H T)
    (hD : IntervalIntegrable (fun t => ‖D t‖ ^ 2) volume H T)
    (he : ∀ t, R t = A t - B t - C t - D t) :
    (∫ t in H..T, ‖R t‖ ^ 2) ≤
      4*((∫ t in H..T, ‖A t‖ ^ 2)+(∫ t in H..T, ‖B t‖ ^ 2)+
        (∫ t in H..T, ‖C t‖ ^ 2)+(∫ t in H..T, ‖D t‖ ^ 2)) := by
  calc
    _ ≤ ∫ t in H..T, 4*(‖A t‖ ^ 2+‖B t‖ ^ 2+‖C t‖ ^ 2+‖D t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on hHT
        ((hR.norm.pow 2).intervalIntegrable H T)
        ((((hA.add hB).add hC).add hD).const_mul 4)
      intro t ht
      change ‖R t‖ ^ 2 ≤ _
      rw [he t]
      exact norm_sub_three_sq_le _ _ _ _
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((hA.add hB).add hC) hD,
        intervalIntegral.integral_add (hA.add hB) hC,
        intervalIntegral.integral_add hA hB]

private theorem log_four_scale_le {N : ℕ} (hN : 0 < N) {U C : ℝ}
    (hU : 2 ≤ U) (hNU : (N : ℝ) ≤ U) (hC : 0 ≤ C) :
    C * U * (1 + Real.log N) ^ 4 ≤ 162*C * U * (Real.log U) ^ 4 := by
  apply le_trans _ (cutoff_log_four_cost_le hN hU hNU hC)
  gcongr
  exact le_add_of_nonneg_right (Nat.cast_nonneg N)

private theorem exists_moving_residue_log_four_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U Y : ℝ, 2 ≤ U → 1 ≤ Y → Y ≤ U →
      (∫ t in U..2 * U, ‖zetaSquareMovingResidue Y t‖ ^ 2) ≤
        C * U * (Real.log U) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquareMovingResidue_uniform_second_moment 0
  refine ⟨162*C, by positivity, ?_⟩
  intro U Y hU hY hYU
  have hh : (∫ t in U..2 * U, ‖zetaSquareMovingResidue Y t‖ ^ 2) ≤ C * U := by
    simpa using hb U Y (by linarith) hY hYU
  have hc := log_four_scale_le (N := 1) (by decide) hU (by norm_num; linarith) hC
  norm_num at hc
  exact hh.trans hc


section
variable (Head Tail : ℕ → ℝ → ℂ)
variable (hHead : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ U : ℝ,
  2 ≤ U → (N : ℝ) ≤ U → U ≤ 2 * N →
  IntervalIntegrable (fun t => ‖Head N t‖ ^ 2) volume U (2 * U) ∧
  (∫ t in U..2 * U, ‖Head N t‖ ^ 2) ≤ C * U * (1 + Real.log N) ^ 4)
variable (hTail : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ U : ℝ,
  2 ≤ U → (N : ℝ) ≤ U → U ≤ 2 * N →
  IntervalIntegrable (fun t => ‖Tail N t‖ ^ 2) volume U (2 * U) ∧
  (∫ t in U..2 * U, ‖Tail N t‖ ^ 2) ≤ C * U * (1 + Real.log N) ^ 4)
variable (hIdentity : ∀ (N : ℕ), 0 < N → ∀ t : ℝ,
  zetaSquareResidual (divisorPolynomial N (fun _ => 1))
    (fun t => zetaSquareCriticalPhase t * star (divisorPolynomial N (fun _ => 1) t)) t =
  divisorSmoothingDefect N t - zetaSquareMovingResidue N t - Head N t - Tail N t)

include hHead hTail hIdentity

private theorem exists_residual_bound_of_four_pieces :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ U : ℝ,
      2 ≤ U → (N : ℝ) ≤ U → U ≤ 2 * N →
      (∫ t in U..2 * U, ‖zetaSquareResidual (divisorPolynomial N (fun _ => 1))
        (fun t => zetaSquareCriticalPhase t *
          star (divisorPolynomial N (fun _ => 1) t)) t‖ ^ 2) ≤
        C * U * (Real.log U) ^ 4 := by
  obtain ⟨CH, hCH, hH⟩ := hHead
  obtain ⟨CT, hCT, hT⟩ := hTail
  obtain ⟨CM, hCM, hM⟩ := exists_moving_residue_log_four_moment
  let CS := 162*(4*smoothedDivisorMomentConstant + 8*divisorMeanValueConstant)
  have hCS : 0 ≤ CS := by
    dsimp [CS, smoothedDivisorMomentConstant, divisorMeanValueConstant]
    positivity
  refine ⟨4*(CS+CM+162*CH+162*CT), by positivity, ?_⟩
  intro N hN U hU hNU hUN
  obtain ⟨hiH, hmH⟩ := hH N hN U hU hNU hUN
  obtain ⟨hiT, hmT⟩ := hT N hN U hU hNU hUN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP := continuous_divisorPolynomial N (fun _ => 1)
  have hR : Continuous (zetaSquareResidual (divisorPolynomial N (fun _ => 1))
      (fun t => zetaSquareCriticalPhase t * star (divisorPolynomial N (fun _ => 1) t))) :=
    continuous_zetaSquareResidual hP (continuous_zetaSquareCriticalPhase.mul hP.star)
  have hh := four_piece_moment_le (by linarith : U ≤ 2 * U) hR
    (((continuous_divisorSmoothingDefect hN).norm.pow 2).intervalIntegrable U (2 * U))
    (((continuous_zetaSquareMovingResidue hN0).norm.pow 2).intervalIntegrable U (2 * U))
    hiH hiT (hIdentity N hN)
  have hS := divisorSmoothingDefect_dyadic_second_moment_le hN hU hNU hUN
  have hMM := hM U N hU hN1 hNU
  have hHH := hmH.trans (log_four_scale_le hN hU hNU hCH)
  have hTT := hmT.trans (log_four_scale_le hN hU hNU hCT)
  have hsum := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add hS hMM) hHH) hTT) (by norm_num : (0 : ℝ) ≤ 4)
  convert! hh.trans hsum using 1 <;> dsimp [CS] <;> ring
end

/-- The actual residual has a uniform second moment for every comparable cutoff.
All contour integrals, series interchanges, and four moment providers are proved. -/
theorem exists_zetaSquareResidual_comparable_cutoff_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ U : ℝ,
      2 ≤ U → (N : ℝ) ≤ U → U ≤ 2 * N →
      (∫ t in U..2 * U, ‖zetaSquareResidual (divisorPolynomial N (fun _ => 1))
        (fun t => zetaSquareCriticalPhase t *
          star (divisorPolynomial N (fun _ => 1) t)) t‖ ^ 2) ≤
        C * U * (Real.log U) ^ 4 := by
  apply exists_residual_bound_of_four_pieces
    (fun N t => zetaSquareRightHeadIntegral N N t)
    (fun N t => zetaSquareInfiniteTailIntegral N N t)
  · obtain ⟨C, hC, hb⟩ := exists_zetaSquareRightHeadIntegral_uniform_second_moment
    refine ⟨C, hC, ?_⟩
    intro N hN U hU hNU _
    exact (hb N N U hN (by exact_mod_cast hN) hNU (by linarith) hNU).2
  · obtain ⟨C, hC, hb⟩ := exists_zetaSquareInfiniteTailIntegral_dyadic_second_moment
    exact ⟨C, hC, fun N hN U hU _ hUN => hb N hN U hU hUN⟩
  · intro N hN t
    have hh := zetaSquareResidual_eq_mellin_remainder N
      (Y := N) (by exact_mod_cast hN) t (b := 1 / 4) (by norm_num) (by norm_num)
    rw [← smoothedDivisorSeries_eq_dampedDivisorSeries hN t] at hh
    simpa only [divisorSmoothingDefect, zetaSquareRightHeadIntegral,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hh

/-- The canonical floor-cutoff residual provider, with no analytic hypotheses. -/
theorem exists_actual_zetaSquareResidual_dyadic_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U ≥ 2,
      (∫ t in U..2 * U, ‖zetaSquareResidual
        (divisorPolynomial ⌊U⌋₊ (fun _ => 1))
        (fun t => zetaSquareCriticalPhase t *
          star (divisorPolynomial ⌊U⌋₊ (fun _ => 1) t)) t‖ ^ 2) ≤
            C * U * (Real.log U) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquareResidual_comparable_cutoff_bound
  refine ⟨C, hC, ?_⟩
  intro U hU
  have hN : 0 < ⌊U⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hNU : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le (by linarith)
  have hN1 : (1 : ℝ) ≤ ⌊U⌋₊ := by exact_mod_cast hN
  have hUN : U ≤ 2 * (⌊U⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one U
    linarith
  exact hb ⌊U⌋₊ hN U hU hNU hUN

/-- Ingham I1 for the actual Riemann zeta function, uniformly for every `T ≥ 2`. -/
theorem exists_actual_zeta_fourth_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T ≥ 2,
      (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ^ 4) ≤
        C * T * (Real.log T) ^ 4 := by
  obtain ⟨C, hC, hb⟩ := exists_actual_zetaSquareResidual_dyadic_bound
  exact exists_fourth_moment_bound_of_actual_dyadic_residual (H := 2) le_rfl hC hb

end RiemannResearch.Analysis
