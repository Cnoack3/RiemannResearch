/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualEvenHorizontalMomentRate
import RiemannResearch.Analysis.ActualZeroHorizontalRemainder
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed horizontal Fourier corrections at all even orders

The exact finite Taylor decomposition in `ActualZeroHorizontalRemainder`
retains the phase of every even horizontal moment. Ford–Meng–Zaharescu,
https://arxiv.org/abs/1511.06814, motivate the underlying comparison of
actual-ordinate phases and centered Landau sums. The Cauchy density profile
supplies a common unconditional estimate for all Taylor orders. The stronger
uniform density estimate of Baluyot, *On the Zeros of Riemann's Zeta-function*,
Theorem 1.2.1, https://hdl.handle.net/1802/32855, supplies every fixed
frequency band strictly below `(8/7) * log T` when given as a Lean premise.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The unconditional density profile controls all normalized even moments
and all signed Taylor errors, with one height threshold and one prefactor. -/
theorem eventually_horizontalHarmonic_loglog_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ (J : ℕ) (u : ℝ),
      let v := horizontalTailDecay T / 2
      ‖evenHorizontalMoment T u (J + 1) / (T : ℂ)‖ ≤
        ((Nat.factorial (2 * (J + 1)) : ℝ) / v ^ (2 * (J + 1))) * (K * Real.log T) ∧
      (|u| ≤ v → ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
        (|u| / v) ^ (2 * (J + 1)) * (K * Real.log T)) := by
  obtain ⟨K, hK, htail⟩ := eventually_rightStrictTail_loglog_bound
  refine ⟨2 * K / 3, by positivity, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with T htail hT hℓ
  intro J u
  let q := horizontalTailDecay T
  let v := q / 2
  let M := 2 * (K * T * Real.log T)
  have hTp : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hq : 0 < q := by dsimp [q, horizontalTailDecay]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hvq : v < q := by dsimp [v]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hprofile (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
      strictTail T t ≤ M * Real.exp (-q * t) := by
    rw [strictTail_eq_twice_right T t ht.1]
    simpa only [M, q, mul_assoc] using
      mul_le_mul_of_nonneg_left (htail t ht) (by norm_num : (0 : ℝ) ≤ 2)
  have hratio : M * v ^ 2 / (q ^ 2 - v ^ 2) / T = 2 * K / 3 * Real.log T := by
    have hd : q ^ 2 - v ^ 2 = 3 * q ^ 2 / 4 := by dsimp [v]; ring
    rw [hd]
    dsimp only [v, M]
    field_simp [hq.ne', hTp.ne']
    <;> ring
  constructor
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp]
    calc
      _ ≤ (((Nat.factorial (2 * (J + 1)) : ℝ) / v ^ (2 * (J + 1))) *
        (M * v ^ 2 / (q ^ 2 - v ^ 2))) / T :=
        div_le_div_of_nonneg_right
          (norm_evenHorizontalMoment_le_expTail T u v M q J hv hM hvq hprofile) hTp.le
      _ = _ := by rw [mul_div_assoc, hratio]
  · intro hu
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp]
    calc
      _ ≤ ((|u| / v) ^ (2 * (J + 1)) * (M * v ^ 2 / (q ^ 2 - v ^ 2))) / T :=
        div_le_div_of_nonneg_right
          (horizontalTaylorError_of_expTail T u v M q J hv hu hM hvq hprofile) hTp.le
      _ = _ := by rw [mul_div_assoc, hratio]

/-- For any strict subband of the density exponent, keep the entire
signed Taylor remainder. The comparison frequency can approach the
density exponent and the constant is independent of the Taylor order. -/
theorem normalized_horizontalTaylorError_of_selberg_width
    (T u C a c : ℝ) (J : ℕ) (hT : 1 < T) (hC : 0 ≤ C)
    (hc : 0 < c) (hca : c < a) (hu : |u| ≤ c * Real.log T)
    (hD : SelbergDensityBound T C a) :
    ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
      (2 * C * c ^ 2 / (a ^ 2 - c ^ 2)) * Real.log T *
        (|u| / (c * Real.log T)) ^ (2 * (J + 1)) := by
  let L := Real.log T
  have hL : 0 < L := Real.log_pos hT
  have hTp : 0 < T := by linarith
  have hden : 0 < a ^ 2 - c ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hca) (show 0 < a + c by linarith)]
  have h := horizontalTaylorError_of_expTail T u (c * L) (2 * C * T * L) (a * L) J
    (mul_pos hc hL) hu (by positivity) (mul_lt_mul_of_pos_right hca hL)
    (fun t ht => strictTail_of_selbergDensity T C a t hTp ht hD)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp]
  refine (div_le_div_of_nonneg_right h hTp.le).trans_eq ?_
  rw [show (a * L) ^ 2 - (c * L) ^ 2 = (a ^ 2 - c ^ 2) * L ^ 2 by ring]
  field_simp [hTp.ne', hL.ne', hc.ne', hden.ne']
  <;> ring

/-- The open Conrey–Baluyot range supports every strict inner frequency
band, simultaneously at every Taylor order. -/
theorem ConreyBaluyotDensityHypothesis.horizontalTaylorBand
    (hD : ConreyBaluyotDensityHypothesis) {b : ℝ} (hb : 0 ≤ b) (hb' : b < 8 / 7) :
    ∃ c K : ℝ, b < c ∧ c < 8 / 7 ∧ 0 ≤ K ∧
      ∀ᶠ T : ℝ in atTop, ∀ (J : ℕ) (u : ℝ), |u| ≤ b * Real.log T →
        ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
          K * Real.log T * (|u| / (c * Real.log T)) ^ (2 * (J + 1)) := by
  let a : ℝ := (b + 8 / 7) / 2
  let c : ℝ := (b + a) / 2
  have hba : b < a := by dsimp [a]; linarith
  have ha : 0 < a := by linarith
  have ha' : a < 8 / 7 := by dsimp [a]; linarith
  have hbc : b < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  have hc : 0 < c := by linarith
  have hden : 0 < a ^ 2 - c ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hca) (show 0 < a + c by linarith)]
  obtain ⟨C, H, hC, hH, hbound⟩ := hD a ha ha'
  refine ⟨c, 2 * C * c ^ 2 / (a ^ 2 - c ^ 2), hbc, hca.trans ha', by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop H] with T hT J u hu
  have hT₁ := hH.trans_le hT
  have hlog := (Real.log_pos hT₁).le
  exact normalized_horizontalTaylorError_of_selberg_width T u C a c J hT₁ hC hc hca
    (hu.trans (mul_le_mul_of_nonneg_right hbc.le hlog)) (hbound T hT)

end RiemannResearch.Analysis.ActualZeroOrdinate
