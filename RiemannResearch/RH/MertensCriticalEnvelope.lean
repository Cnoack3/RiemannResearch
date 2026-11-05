/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.VKSecondProfile
import RiemannResearch.RH.MertensEndpointEnvelope

/-!
# Transferring the second Lee–Leong exponent through a finite Möbius window

The physical-site shift at fixed coefficients of Φ and Φ / log log costs
at most a constant times Φ² / log. This and the harmonic logarithm are
absorbed in the additional square-root correction.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis

/-- At the same primary and secondary coefficients, a fixed square-root
margin absorbs the cutoff shift and leaves any desired square-root saving. -/
theorem errorEnvelope_eventually_le_vk_critical (A b t : ℝ) (hA : 0 < A)
    (hb : 0 ≤ b) (ht : 0 ≤ t) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (Real.exp (-A * vkProfile (N : ℝ) - b * vkSecondProfile (N : ℝ) -
        (2 * (t + 2)) * Real.sqrt (vkProfile (N : ℝ)))) ≤
        2 + K * ((n : ℝ) * Real.exp (-A * vkProfile (n : ℝ) - b * vkSecondProfile (n : ℝ) -
          t * Real.sqrt (vkProfile (n : ℝ)))) := by
  let B := A + b + t + 1
  let u := 2 * (t + 2)
  let D := A + b + 1
  let K := 8 + 5 * (A + b + u)
  let δ := 1 / (D * B)
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hK : 3 ≤ K := by dsimp [K]; linarith only [hA, hb, hu]
  have hK0 : 0 ≤ K := by linarith
  have hcancel : (D * B) * δ = 1 := by
    dsimp [δ]
    field_simp [hD.ne', hB.ne']
  obtain ⟨Y, hY⟩ := eventually_atTop.1
    ((vk_sq_div_log_eventual_le_sqrt δ hδ).and (vkProfile_dominates_logLog_sq 1 (by norm_num)))
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨K, hK0, ?_⟩
  filter_upwards [hnat.eventually (eventually_ge_atTop Y),
    hnat.eventually vk_eventual_relative_increment, hnat.eventually vkProfile_eventually_mono,
    hnat.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))),
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (4 : ℝ))),
    eventually_ge_atTop (2 : ℕ)] with N hNY hinc hmono hE hp4 hN n
  let P := vkProfile (n : ℝ)
  let p := vkProfile (N : ℝ)
  let W := vkSecondProfile (n : ℝ)
  let w := vkSecondProfile (N : ℝ)
  let T := Real.log (n : ℝ)
  let L := Real.log T
  let l := Real.log (Real.log (N : ℝ))
  let e := Real.exp (-A * p - b * w - u * Real.sqrt p)
  let v := Real.exp (-A * P - b * W - t * Real.sqrt P)
  have hsite : 0 ≤ (n : ℝ) * v := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  change errorEnvelope N n e ≤ 2 + K * ((n : ℝ) * v)
  rw [errorEnvelope]
  split_ifs with hhead
  · linarith [mul_nonneg hK0 hsite]
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnr : 0 < (n : ℝ) := hNr.trans_le hNn
  change Real.exp 1 ≤ Real.log (N : ℝ) at hE
  have hTN : 0 < Real.log (N : ℝ) := (Real.exp_pos _).trans_le hE
  have hTcmp : Real.log (N : ℝ) ≤ T := Real.log_le_log hNr hNn
  have hT : 0 < T := hTN.trans_le hTcmp
  have hT1 : 1 ≤ T := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans (hE.trans hTcmp)
  have hl1 : 1 ≤ l := (Real.le_log_iff_exp_le hTN).mpr hE
  have hlL : l ≤ L := Real.log_le_log hTN hTcmp
  have hL1 : 1 ≤ L := hl1.trans hlL
  have hl0 : 0 < l := by linarith
  have hL0 : 0 < L := hl0.trans_le hlL
  change 4 ≤ p at hp4
  have hp0 : 0 ≤ p := by linarith
  have hpP : p ≤ P := hmono _ hNn
  have hP : 0 ≤ P := hp0.trans hpP
  have hpw : w ≤ p := div_le_self hp0 hl1
  have hPW : W ≤ P := div_le_self hP hL1
  have hPT : P ≤ T := by
    calc
      P ≤ T ^ (3 / 5 : ℝ) := div_le_self
        (Real.rpow_nonneg hT.le _) (Real.one_le_rpow hL1 (by norm_num))
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one _
  have hS : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have hS2 : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  have hSbig : 2 ≤ Real.sqrt P := by
    refine le_of_sq_le_sq ?_ hS
    rw [hS2]
    linarith
  have hhalf : Real.sqrt P ≤ P / 2 := by
    nlinarith only [mul_nonneg hS (sub_nonneg.mpr hSbig), hS2]
  have hSP : Real.sqrt P ≤ P := by linarith only [hhalf, hP]
  by_cases hcut : (N : ℝ) ≤ (n : ℝ) * Real.exp (-B * P)
  · apply (min_le_left _ _).trans
    have he : Real.exp (-B * P) ≤ v := by
      apply Real.exp_le_exp.mpr
      dsimp only [B]
      linarith only [mul_le_mul_of_nonneg_left hPW hb,
        mul_le_mul_of_nonneg_left hSP ht, hP]
    have hx := hcut.trans (mul_le_mul_of_nonneg_left he hnr.le)
    linarith only [hx, mul_le_mul_of_nonneg_right hK hsite]
  · apply (min_le_right _ _).trans
    obtain ⟨hslope, hlogsave⟩ := hY (n : ℝ) (hNY.trans hNn)
    change P ^ 2 / T ≤ δ * Real.sqrt P at hslope
    change L ^ 2 ≤ 1 * P at hlogsave
    have hlog : L ≤ Real.sqrt P := by
      refine le_of_sq_le_sq ?_ hS
      linarith only [hlogsave, hS2]
    have hl := Real.log_lt_log (mul_pos hnr (Real.exp_pos _)) (lt_of_not_ge hcut)
    rw [Real.log_mul hnr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hspan : T - Real.log (N : ℝ) ≤ B * P := by dsimp only [T]; linarith only [hl]
    have hincr : P - p ≤ P / T * (B * P) :=
      (hinc _ hNn).trans (mul_le_mul_of_nonneg_left hspan (div_nonneg hP hT.le))
    have hshift : D * (P - p) ≤ Real.sqrt P := by
      calc
        _ ≤ D * (P / T * (B * P)) := mul_le_mul_of_nonneg_left hincr hD.le
        _ = (D * B) * (P ^ 2 / T) := by ring
        _ ≤ (D * B) * (δ * Real.sqrt P) :=
          mul_le_mul_of_nonneg_left hslope (mul_nonneg hD.le hB.le)
        _ = _ := by rw [← mul_assoc, hcancel, one_mul]
    have hsec : W - w ≤ P - p := by
      have hquot : p / L ≤ p / l := by
        apply (div_le_div_iff₀ hL0 hl0).mpr
        exact mul_le_mul_of_nonneg_left hlL hp0
      calc
        _ ≤ P / L - p / L := sub_le_sub_left hquot _
        _ = (P - p) / L := by ring
        _ ≤ P - p := div_le_self (sub_nonneg.mpr hpP) hL1
    have hdiff : P - p ≤ Real.sqrt P := by
      have := mul_le_mul_of_nonneg_right hD1 (sub_nonneg.mpr hpP)
      linarith only [this, hshift]
    have hroot : Real.sqrt P ≤ 2 * Real.sqrt p := by
      refine le_of_sq_le_sq ?_ (by positivity)
      nlinarith only [hS2, Real.sq_sqrt hp0, hdiff, hhalf, hP]
    have hsecondary : A * (P - p) + b * (W - w) ≤ Real.sqrt P := by
      dsimp only [D] at hshift
      linarith only [hshift, mul_le_mul_of_nonneg_left hsec hb, hpP]
    have hcharge : (t + 2) * Real.sqrt P ≤ u * Real.sqrt p := by
      have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ t + 2 by linarith)
      dsimp only [u]
      linarith only [h]
    have hexp : -A * p - b * w - u * Real.sqrt p + L ≤ -A * P - b * W - t * Real.sqrt P := by
      linarith only [hsecondary, hcharge, hlog]
    have hfactor : 2 + T + 5 * (1 + A * p + b * w + u * Real.sqrt p) ≤ K * T := by
      dsimp only [K]
      linarith only [mul_le_mul_of_nonneg_left (hpP.trans hPT) hA.le,
        mul_le_mul_of_nonneg_left ((hpw.trans hpP).trans hPT) hb,
        mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hpP).trans (hSP.trans hPT)) hu, hT1]
    have hcost : e * (2 + T + 5 * (1 + A * p + b * w + u * Real.sqrt p)) ≤ K * v := by
      calc
        _ ≤ e * (K * T) := mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
        _ = K * Real.exp (-A * p - b * w - u * Real.sqrt p + L) := by
          rw [Real.exp_add, Real.exp_log hT]
          dsimp only [e]
          ring
        _ ≤ K * v := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hK0
    have hlogcharge : Real.log (1 / e) = A * p + b * w + u * Real.sqrt p := by
      dsimp [e]
      rw [one_div, Real.log_inv, Real.log_exp]
      ring
    rw [hlogcharge]
    change 2 + (n : ℝ) * (e * (2 + T) + 5 * (e * (1 + (A * p + b * w + u * Real.sqrt p)))) ≤
      2 + K * ((n : ℝ) * v)
    linarith only [mul_le_mul_of_nonneg_left hcost hnr.le]

end RiemannResearch.RH.QMertensFirstMoment
