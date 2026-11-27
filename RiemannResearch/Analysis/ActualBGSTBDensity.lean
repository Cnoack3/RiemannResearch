/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The moving endpoint in the BGSTB density hypothesis

Source for the moving strip, inclusive count, and signed pair-remainder scale:
Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh, arXiv:2306.04799,
Theorem 3, Lemma 7 and equation (6.3), <https://arxiv.org/abs/2306.04799>.
The full-strip density input gives exact Selberg slope two via the total zero count.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Uniform little-o density on the closed moving strip ending at b. -/
def BGSTBStripDensity (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (1 / 2 + 1 / (2 * Real.log T)) b,
    rightInclusiveCount T σ ≤ ε * T ^ (2 * (1 - σ))

/-- The Riemann–von Mangoldt total count covers the remaining interval
from 1/2 to the moving boundary. One constant works at exact slope two. -/
theorem uniformSelbergDensity_two_of_full_bgstb (hs : BGSTBStripDensity 1) :
    UniformSelbergDensity 2 := by
  obtain ⟨C, hC, hc⟩ := exists_selberg_form_on_logarithmic_strip 2 (1 / 2) (by norm_num)
  obtain ⟨U, hU⟩ := eventually_atTop.1 (hs 1 zero_lt_one)
  obtain ⟨V, hV⟩ := eventually_atTop.1 (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  refine ⟨max C 1, max 9 (max U V), le_trans hC.le (le_max_left _ _),
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 9) (le_max_left _ _), ?_⟩
  intro T hT σ hσ
  have h9 := (le_max_left 9 (max U V)).trans hT
  have hUV := (le_max_right 9 (max U V)).trans hT
  have hL : 1 ≤ Real.log T := hV T ((le_max_right _ _).trans hUV)
  have hTp : 0 < T := by linarith
  have hLp : 0 < Real.log T := zero_lt_one.trans_le hL
  let p := T ^ (1 - 2 * (σ - 1 / 2))
  have hp : 0 ≤ p := Real.rpow_nonneg hTp.le _
  by_cases hh : σ < 1 / 2 + 1 / (2 * Real.log T)
  · have he : 1 / (2 * Real.log T) = (1 / 2) / Real.log T := by ring
    rw [he] at hh
    have hband : (σ - 1 / 2) * Real.log T ≤ 1 / 2 :=
      (le_div_iff₀ hLp).mp (by linarith only [hh])
    exact (hc T h9 σ hband).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 1) hp) hLp.le)
  · have hh' := hU T ((le_max_left _ _).trans hUV) σ ⟨le_of_not_gt hh, hσ.2⟩
    rw [one_mul, show 2 * (1 - σ) = 1 - 2 * (σ - 1 / 2) by ring] at hh'
    calc
      _ ≤ p := hh'
      _ = 1 * p * 1 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right C 1) hp)
        hL zero_le_one (mul_nonneg (hC.le.trans (le_max_left _ _)) hp)

/-- At scaled displacement d one has the exact height scale T exp(-2d). -/
theorem bgstb_scaled_height {T : ℝ} (hT : 1 < T) (d : ℝ) :
    T ^ (2 * (1 - (1 / 2 + d / Real.log T))) = T / Real.exp (2 * d) := by
  have hL := (Real.log_pos hT).ne'
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hT),
    show Real.log T * (2 * (1 - (1 / 2 + d / Real.log T))) = Real.log T - 2 * d by
      field_simp [hL]; ring,
    Real.exp_sub, Real.exp_log (zero_lt_one.trans hT)]

/-- At scaled displacement 1/2, the closed lower endpoint alone yields
little-o of T/e from the BGSTB estimate. No far-strip input is used. -/
theorem bgstb_endpoint_isLittleO_height_div_exp {b : ℝ} (hb : 1 / 2 < b)
    (h : BGSTBStripDensity b) :
    (fun T : ℝ => rightInclusiveCount T (1 / 2 + 1 / (2 * Real.log T))) =o[atTop]
      (fun T : ℝ => T / Real.exp 1) := by
  have hsmall : Tendsto (fun T : ℝ => (1 / 2 : ℝ) / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply Asymptotics.isLittleO_iff.mpr
  intro c hc
  filter_upwards [h c hc, hsmall.eventually (gt_mem_nhds (sub_pos.mpr hb)),
    eventually_gt_atTop (1 : ℝ)] with T hC hcut hT
  have he : 1 / (2 * Real.log T) = (1 / 2) / Real.log T := by ring
  have hm : 1 / 2 + 1 / (2 * Real.log T) ≤ b := by rw [he]; linarith only [hcut]
  have hC' := hC _ ⟨le_rfl, hm⟩
  have hp := bgstb_scaled_height hT (1 / 2)
  rw [← he, show 2 * (1 / 2 : ℝ) = 1 by norm_num] at hp
  rw [hp] at hC'
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rightInclusiveCount_nonneg _ _),
    abs_of_pos (div_pos (zero_lt_one.trans hT) (Real.exp_pos 1))] using hC'

/-- Riemann–von Mangoldt converts the same endpoint to little-o of
N(T)/log T. Multiplicities in the numerator and denominator are retained. -/
theorem bgstb_endpoint_isLittleO_count_div_log {b : ℝ} (hb : 1 / 2 < b)
    (h : BGSTBStripDensity b) :
    (fun T : ℝ => rightInclusiveCount T (1 / 2 + 1 / (2 * Real.log T))) =o[atTop]
      (fun T : ℝ => (Ncount 0 T : ℝ) / Real.log T) := by
  apply (bgstb_endpoint_isLittleO_height_div_exp hb h).trans_isBigO
  apply Asymptotics.IsBigO.of_bound (16 * Real.pi / Real.exp 1)
  filter_upwards [eventually_count_ge_log, eventually_gt_atTop (1 : ℝ)] with T hn hT
  have hTp := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have ha : 0 < 16 * Real.pi := by positivity
  have hc := (le_div_iff₀ hL).mpr hn
  change (1 / (16 * Real.pi)) * T ≤ (Ncount 0 T : ℝ) / Real.log T at hc
  simp only [Real.norm_eq_abs, abs_of_pos (div_pos hTp (Real.exp_pos 1)),
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hL.le)]
  calc
    T / Real.exp 1 = (16 * Real.pi / Real.exp 1) * ((1 / (16 * Real.pi)) * T) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

/-- The endpoint also has zero proportion among all zero occurrences. -/
theorem bgstb_endpoint_isLittleO_count {b : ℝ} (hb : 1 / 2 < b)
    (h : BGSTBStripDensity b) :
    (fun T : ℝ => rightInclusiveCount T (1 / 2 + 1 / (2 * Real.log T))) =o[atTop]
      (fun T : ℝ => (Ncount 0 T : ℝ)) := by
  apply (bgstb_endpoint_isLittleO_count_div_log hb h).trans_isBigO
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hL
  have hn : (0 : ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn,
    abs_of_nonneg (div_nonneg hn (zero_le_one.trans hL))] using div_le_self hn hL

/-- The normalization asked for at the moving endpoint uses the total
number of zero occurrences divided by Euler's number. -/
theorem bgstb_endpoint_isLittleO_count_div_exp {b : ℝ} (hb : 1 / 2 < b)
    (h : BGSTBStripDensity b) :
    (fun T : ℝ => rightInclusiveCount T (1 / 2 + 1 / (2 * Real.log T))) =o[atTop]
      (fun T : ℝ => (Ncount 0 T : ℝ) / Real.exp 1) := by
  apply (bgstb_endpoint_isLittleO_count_div_log hb h).trans_isBigO
  apply Asymptotics.IsBigO.of_bound'
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with T hL
  have hn : (0 : ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hn (Real.exp_pos 1).le),
    abs_of_nonneg (div_nonneg hn ((Real.exp_pos 1).le.trans hL))] using
    div_le_div_of_nonneg_left hn (Real.exp_pos 1) hL

/-- Conversion of the remainder scale in BGSTB (6.3), for use with
Lemma 7. The estimate on the signed pair remainder is the hypothesis. -/
theorem isLittleO_count_div_exp_of_height_log {S : ℝ → ℝ}
    (h : S =o[atTop] (fun T : ℝ => T * Real.log T)) :
    S =o[atTop] (fun T : ℝ => (Ncount 0 T : ℝ) / Real.exp 1) := by
  apply h.trans_isBigO
  apply Asymptotics.IsBigO.of_bound (16 * Real.pi * Real.exp 1)
  filter_upwards [eventually_count_ge_log, eventually_gt_atTop (1 : ℝ)] with T hN hT
  have ht := zero_lt_one.trans hT
  simp only [Real.norm_eq_abs, abs_of_pos (mul_pos ht (Real.log_pos hT)),
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.exp_pos 1).le)]
  calc
    T * Real.log T = (16 * Real.pi) * ((1 / (16 * Real.pi)) * T * Real.log T) := by
      field_simp
    _ ≤ (16 * Real.pi) * (Ncount 0 T : ℝ) := mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by field_simp

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.bgstb_endpoint_isLittleO_count_div_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bgstb_endpoint_isLittleO_count_div_exp

end RiemannResearch.Analysis.ActualZeroOrdinate
