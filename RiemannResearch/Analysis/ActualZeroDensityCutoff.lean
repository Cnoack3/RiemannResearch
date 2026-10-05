/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualHyperbolicLogRemainder
import RiemannResearch.Analysis.NonlinearZeroDensityRate

/-!
# Actual count-normalized shrinking density cutoffs

For every prescribed subpower integer support and sublinear logarithmic margin,
the exact inverse cutoff tends to zero and eventually belongs to [0,1/32].
This is unconditional cutoff algebra and actual-count normalization, not a
proof of zero-density decay. The source scale retains the log(log T) term
from Chourasiya--Simonic, arXiv:2507.15184v2, Theorem 1:
https://arxiv.org/html/2507.15184v2.
-/

noncomputable section
open Filter
set_option maxHeartbeats 800000
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23 FiniteHyperbolicHarmonicCap ZeroDensityRate
/-- The actual count-normalized, count-only inverse cutoff. -/
def sourceCountCutoff (T : ℝ) (d : ℕ) (C ω : ℝ) : ℝ :=
  positiveCountCutoff (Real.log T+Real.log (Real.log T))
    (2*(C*T*(Real.log T)^3)*harmonicHyperbolicCap d/(Ncount 0 T : ℝ)) ω

/-- The source's normalized exponent margin is sublinear for every subpower
integer support and every sublinear auxiliary margin. No density is used. -/
theorem source_positive_margin_ratio_tendsto_zero
    (d : ℝ → ℕ) (ω : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (nhds 0))
    (hωsmall : Tendsto (fun T : ℝ => ω T/Real.log T) atTop (nhds 0)) :
    Tendsto (fun T : ℝ =>
      max 0 (Real.log (2*(C*T*(Real.log T)^3)*harmonicHyperbolicCap (d T)/
        (Ncount 0 T : ℝ))+ω T)/(Real.log T+Real.log (Real.log T)))
      atTop (nhds 0) := by
  have hll := Real.log_div_self_tendsto_zero.comp Real.tendsto_log_atTop
  have hc : Tendsto (fun T : ℝ => Real.log (64*Real.pi*C)/Real.log T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hn : Tendsto (fun T : ℝ =>
      (Real.log (64*Real.pi*C)+Real.log (d T : ℝ)+3*Real.log (Real.log T)+ω T)/
        Real.log T) atTop (nhds 0) := by
    have h := ((hc.add hsmall).add (hll.const_mul (3:ℝ))).add hωsmall
    convert h using 1
    · funext T
      dsimp only [Function.comp_def]
      ring
    · norm_num
  have hm := Real.positivePart_div_tendsto_zero
    (fun T : ℝ => Real.log (64*Real.pi*C)+Real.log (d T : ℝ)+
      3*Real.log (Real.log T)+ω T) (fun T => Real.log T)
    (Real.tendsto_log_atTop.eventually_gt_atTop 0) hn
  refine squeeze_zero' ?_ ?_ hm
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hl
    have hll0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hl
    exact div_nonneg (le_max_left _ _) (by linarith)
  · filter_upwards [hd, eventually_count_ge_log, eventually_gt_atTop (0:ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      hsmall.eventually_le_const (by norm_num : (0:ℝ)<1)]
      with T hdT hN hT hL hs
    let L := Real.log T
    have hL0 : 0 < L := by dsimp [L]; linarith
    have hd0 : (0:ℝ) < (d T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hdT)
    have hel : Real.log (d T : ℝ) ≤ L := by
      have h := (div_le_one hL0).mp hs
      exact h
    have hW : harmonicHyperbolicCap (d T) ≤ 2*(d T : ℝ)*L := by
      have hw := harmonicHyperbolicCap_le_card_log (d T) hdT
      have hx := mul_le_mul_of_nonneg_left hel hd0.le
      dsimp [L] at *
      nlinarith
    have hlog0 : 0 < Real.log T := hL0
    have hn0 : (0:ℝ) < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
    have hw0 : 0 < harmonicHyperbolicCap (d T) :=
      hd0.trans_le (harmonicHyperbolicCap_ge_card (d T))
    let A := 2*(C*T*L^3)*harmonicHyperbolicCap (d T)/(Ncount 0 T : ℝ)
    have hA0 : 0 < A := by dsimp [A]; positivity
    have hAu : A ≤ 64*Real.pi*C*(d T : ℝ)*L^3 := by
      calc
        _ ≤ (2*(C*T*L^3)*(2*(d T : ℝ)*L))/(Ncount 0 T : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hW (by positivity)) hn0.le
        _ ≤ (2*(C*T*L^3)*(2*(d T : ℝ)*L))/((1/(16*Real.pi))*T*L) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hN
        _ = _ := by field_simp [hT.ne', hL0.ne', Real.pi_pos.ne']; ring
    have hlog : Real.log A ≤ Real.log (64*Real.pi*C)+Real.log (d T : ℝ)+
        3*Real.log L := by
      calc
        _ ≤ Real.log (64*Real.pi*C*(d T : ℝ)*L^3) := Real.log_le_log hA0 hAu
        _ = _ := by
          rw [Real.log_mul (by positivity : 64*Real.pi*C*(d T : ℝ) ≠ 0)
            (pow_ne_zero 3 hL0.ne'),
            Real.log_mul (by positivity : 64*Real.pi*C ≠ 0) hd0.ne', Real.log_pow]
          norm_num
    have hll0 : 0 ≤ Real.log L := Real.log_nonneg hL
    change max 0 (Real.log A+ω T)/(L+Real.log L) ≤
      max 0 (Real.log (64*Real.pi*C)+Real.log (d T : ℝ)+3*Real.log L+ω T)/L
    calc
      _ ≤ max 0 (Real.log A+ω T)/L :=
        div_le_div_of_nonneg_left (le_max_left _ _) hL0 (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right
        (max_le_max le_rfl (add_le_add hlog le_rfl)) hL0.le
/-- Unconditional shrinking and source-range transfer. The hypotheses
describe prescribed support/margin growth; no zero-density estimate occurs. -/
theorem sourceCountCutoff_shrinking
    (d : ℝ → ℕ) (ω : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (nhds 0))
    (hωsmall : Tendsto (fun T : ℝ => ω T/Real.log T) atTop (nhds 0)) :
    Tendsto (fun T => sourceCountCutoff T (d T) C (ω T)) atTop (nhds 0) ∧
      ∀ᶠ T : ℝ in atTop, 0 ≤ sourceCountCutoff T (d T) C (ω T) ∧
        sourceCountCutoff T (d T) C (ω T) ≤ 1/32 := by
  have hm : ∀ᶠ T : ℝ in atTop, 0 < Real.log T+Real.log (Real.log T) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with T ht
    have h := Real.log_nonneg ht
    linarith
  have hr := source_positive_margin_ratio_tendsto_zero d ω C hC hd hsmall hωsmall
  exact ⟨positiveCountCutoff_tendsto_zero _ _ _ hm hr,
    positiveCountCutoff_eventually_nearLine _ _ _ hm hr⟩

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroDensityRate
/-- Source-admissible shrinking cutoff. The added lower margin makes the
source's strict near-line restriction automatic without a count upper bound. -/
def sourceAdmissibleCutoff (T : ℝ) (d : ℕ) (C ω η : ℝ) : ℝ :=
  max (sourceCountCutoff T d C ω) (2*η/Real.log T)

theorem sourceAdmissibleCutoff_shrinking
    (d : ℝ → ℕ) (ω : ℝ → ℝ) (C η : ℝ) (hC : 0 < C) (hη : 0 < η)
    (hd : ∀ᶠ T : ℝ in atTop, 1 ≤ d T)
    (hsmall : Tendsto (fun T : ℝ => Real.log (d T : ℝ)/Real.log T) atTop (nhds 0))
    (hωsmall : Tendsto (fun T : ℝ => ω T/Real.log T) atTop (nhds 0)) :
    Tendsto (fun T => sourceAdmissibleCutoff T (d T) C (ω T) η) atTop (nhds 0) ∧
      ∀ᶠ T : ℝ in atTop,
        0 ≤ sourceAdmissibleCutoff T (d T) C (ω T) η ∧
        sourceAdmissibleCutoff T (d T) C (ω T) η ≤ 1/32 ∧
        η/Real.log T < sourceAdmissibleCutoff T (d T) C (ω T) η := by
  have hc := sourceCountCutoff_shrinking d ω C hC hd hsmall hωsmall
  have hl : Tendsto (fun T : ℝ => 2*η/Real.log T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hs : Tendsto (fun T => sourceAdmissibleCutoff T (d T) C (ω T) η)
      atTop (nhds 0) := by
    simpa only [sourceAdmissibleCutoff, max_self] using hc.1.max hl
  refine ⟨hs, ?_⟩
  filter_upwards [hc.2, hs.eventually_le_const (by norm_num : (0:ℝ)<1/32),
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with T ht hu hL
  refine ⟨ht.1.trans (le_max_left _ _), hu, ?_⟩
  have hk : 0 < η/Real.log T := div_pos hη hL
  have hm := le_max_right (sourceCountCutoff T (d T) C (ω T)) (2*η/Real.log T)
  change η/Real.log T < max _ _
  simp only [mul_div_assoc] at hm ⊢
  linarith

theorem sourceAdmissibleCutoff_leftLine {T C ω η : ℝ} (d : ℕ)
    (hη : 0 < η) (hL : 0 < Real.log T) :
    1/2 < 1/2+sourceAdmissibleCutoff T d C ω η-η/Real.log T ∧
      1/2+sourceAdmissibleCutoff T d C ω η-η/Real.log T <
        1/2+sourceAdmissibleCutoff T d C ω η := by
  have hk : 0 < η/Real.log T := div_pos hη hL
  have hm := le_max_right (sourceCountCutoff T d C ω) (2*η/Real.log T)
  unfold sourceAdmissibleCutoff
  simp only [mul_div_assoc] at hm ⊢
  constructor <;> linarith
end RiemannResearch.Analysis.ActualZeroOrdinate
