/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensFullProfile
import RiemannResearch.RH.MertensEndpointEnvelope

/-!
# A physical Möbius envelope retaining the full ordinary Mertens exponent

For a profile with increments bounded by a fixed multiple of the VK increment,
both the shift in a near window and the harmonic logarithm have size o(√Φ).
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis

/-- Transfer a complete exponent with VK-size increments, at any given
square-root cost. The exponent need only be controlled at large real inputs. -/
theorem errorEnvelope_eventually_le_full_profile_of_increment (F : ℝ → ℝ)
    (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (hbound : ∀ᶠ x : ℝ in atTop, F x ≤ C * vkProfile x)
    (hchange : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      F y - F x ≤ C * (vkProfile y - vkProfile x)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (Real.exp (-F (N : ℝ) + δ / 4 * Real.sqrt (vkProfile (N : ℝ)))) ≤
        2 + K * ((n : ℝ) * Real.exp (-F (n : ℝ) + δ * Real.sqrt (vkProfile (n : ℝ)))) := by
  let K := 8 + 5 * C
  let γ := δ / (4 * C ^ 2)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hK : 3 ≤ K := by dsimp [K]; linarith
  have hK0 : 0 ≤ K := by linarith
  have hcost : C ^ 2 * γ = δ / 4 := by
    dsimp [γ]
    field_simp [hC.ne']
  have hsmall : 0 < δ / 4 := by positivity
  obtain ⟨Y, hY⟩ := eventually_atTop.1
    (((vk_sq_div_log_eventual_le_sqrt γ hγ).and
      (vkProfile_dominates_logLog_sq ((δ / 4) ^ 2) (sq_pos_of_pos hsmall))).and hbound)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨K, hK0, ?_⟩
  filter_upwards [hnat.eventually (eventually_ge_atTop Y),
    hnat.eventually vk_eventual_relative_increment, hnat.eventually vkProfile_eventually_mono,
    hnat.eventually hchange, hnat.eventually hbound,
    hnat.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 1))),
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))),
    eventually_ge_atTop (2 : ℕ)] with N hNY hinc hmono hchg hFN hE hp0 hN n
  let P := vkProfile (n : ℝ)
  let p := vkProfile (N : ℝ)
  let T := Real.log (n : ℝ)
  let L := Real.log T
  let e := Real.exp (-F (N : ℝ) + δ / 4 * Real.sqrt p)
  let v := Real.exp (-F (n : ℝ) + δ * Real.sqrt P)
  have hsite : 0 ≤ (n : ℝ) * v := mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  change errorEnvelope N n e ≤ 2 + K * ((n : ℝ) * v)
  rw [errorEnvelope]
  split_ifs with hhead
  · linarith only [mul_nonneg hK0 hsite]
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnr : 0 < (n : ℝ) := hNr.trans_le hNn
  change Real.exp 1 ≤ Real.log (N : ℝ) at hE
  have hTN : 0 < Real.log (N : ℝ) := (Real.exp_pos _).trans_le hE
  have hTcmp : Real.log (N : ℝ) ≤ T := Real.log_le_log hNr hNn
  have hT : 0 < T := hTN.trans_le hTcmp
  have hT1 : 1 ≤ T := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)).trans (hE.trans hTcmp)
  have hL1 : 1 ≤ L := (Real.le_log_iff_exp_le hT).mpr (hE.trans hTcmp)
  change 0 ≤ p at hp0
  have hpP : p ≤ P := hmono _ hNn
  have hP : 0 ≤ P := hp0.trans hpP
  have hPT : P ≤ T := by
    calc
      P ≤ T ^ (3 / 5 : ℝ) := div_le_self
        (Real.rpow_nonneg hT.le _) (Real.one_le_rpow hL1 (by norm_num))
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one _
  obtain ⟨⟨hslope, hlogsq⟩, hFn⟩ := hY (n : ℝ) (hNY.trans hNn)
  change F (n : ℝ) ≤ C * P at hFn
  change F (N : ℝ) ≤ C * p at hFN
  have hδS := mul_nonneg hδ.le (Real.sqrt_nonneg P)
  by_cases hcut : (N : ℝ) ≤ (n : ℝ) * Real.exp (-C * P)
  · apply (min_le_left _ _).trans
    have he : Real.exp (-C * P) ≤ v := Real.exp_le_exp.mpr (by linarith only [hFn, hδS])
    have hx := hcut.trans (mul_le_mul_of_nonneg_left he hnr.le)
    linarith only [hx, mul_le_mul_of_nonneg_right hK hsite]
  · apply (min_le_right _ _).trans
    change P ^ 2 / T ≤ γ * Real.sqrt P at hslope
    change L ^ 2 ≤ (δ / 4) ^ 2 * P at hlogsq
    have hlog : L ≤ δ / 4 * Real.sqrt P := by
      refine le_of_sq_le_sq ?_ (mul_nonneg hsmall.le (Real.sqrt_nonneg _))
      simpa only [mul_pow, Real.sq_sqrt hP] using hlogsq
    have hl := Real.log_lt_log (mul_pos hnr (Real.exp_pos _)) (lt_of_not_ge hcut)
    rw [Real.log_mul hnr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hspan : T - Real.log (N : ℝ) ≤ C * P := by dsimp only [T]; linarith only [hl]
    have hincr : P - p ≤ P / T * (C * P) :=
      (hinc _ hNn).trans (mul_le_mul_of_nonneg_left hspan (div_nonneg hP hT.le))
    have hshift : F (n : ℝ) - F (N : ℝ) ≤ δ / 4 * Real.sqrt P := by
      calc
        _ ≤ C * (P - p) := hchg _ hNn
        _ ≤ C * (P / T * (C * P)) := mul_le_mul_of_nonneg_left hincr hC.le
        _ = C ^ 2 * (P ^ 2 / T) := by ring
        _ ≤ C ^ 2 * (γ * Real.sqrt P) := mul_le_mul_of_nonneg_left hslope (sq_nonneg C)
        _ = _ := by rw [← mul_assoc, hcost]
    have hexp : -F (N : ℝ) + δ / 4 * Real.sqrt p + L ≤ -F (n : ℝ) + δ * Real.sqrt P := by
      linarith only [hshift, hlog, hδS,
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpP) hsmall.le]
    have hfactor : 2 + T + 5 * (1 + (F (N : ℝ) - δ / 4 * Real.sqrt p)) ≤ K * T := by
      dsimp only [K]
      linarith only [hFN, mul_le_mul_of_nonneg_left (hpP.trans hPT) hC.le,
        mul_nonneg hsmall.le (Real.sqrt_nonneg p), hT1]
    have hmix : e * (2 + T + 5 * (1 + (F (N : ℝ) - δ / 4 * Real.sqrt p))) ≤ K * v := by
      calc
        _ ≤ e * (K * T) := mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
        _ = K * Real.exp (-F (N : ℝ) + δ / 4 * Real.sqrt p + L) := by
          rw [Real.exp_add, Real.exp_log hT]
          dsimp only [e]
          ring
        _ ≤ K * v := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hK0
    have hlogcharge : Real.log (1 / e) = F (N : ℝ) - δ / 4 * Real.sqrt p := by
      dsimp [e]
      rw [one_div, Real.log_inv, Real.log_exp]
      ring
    rw [hlogcharge]
    change 2 + (n : ℝ) * (e * (2 + T) + 5 * (e * (1 + (F (N : ℝ) - δ / 4 * Real.sqrt p)))) ≤
      2 + K * ((n : ℝ) * v)
    linarith only [mul_le_mul_of_nonneg_left hmix hnr.le]

/-- The full coefficient in Lee–Leong, Theorem 1.1, survives
the transfer up to an arbitrarily small positive square-root loss. -/
theorem errorEnvelope_eventually_le_leeLeong_full (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (Real.exp (-leeLeongFullProfile (N : ℝ) +
        δ / 4 * Real.sqrt (vkProfile (N : ℝ)))) ≤
        2 + K * ((n : ℝ) * Real.exp (-leeLeongFullProfile (n : ℝ) +
          δ * Real.sqrt (vkProfile (n : ℝ)))) := by
  have hA : 0 < leeLeongRate := by unfold leeLeongRate; positivity
  apply errorEnvelope_eventually_le_full_profile_of_increment leeLeongFullProfile
    (2 * leeLeongRate) δ (by positivity) hδ
  · exact leeLeongFullProfile_eventually_bounds.mono (fun _ hx => hx.2)
  · exact leeLeongFullProfile_eventually_increment

end RiemannResearch.RH.QMertensFirstMoment
