/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalHigherHorizontalEndpoint
import RiemannResearch.Analysis.ActualRationalHorizontalSaturation
import RiemannResearch.Analysis.ActualEvenHorizontalMomentRate

/-!
# Saturation at every fixed even horizontal order

Source: Section 6 of `FRZ_Strengthening_2026-11-10.pdf`. The proof retains
exact horizontal Taylor terms. Low frequencies use the all-order reflected
Taylor bound and arbitrarily high fixed Landau precision. High frequencies
use induction on the retained order and the actual even-moment bounds.
The only analytic provider is `UniformSelbergDensity (1 / 4)`.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem inverse_pow_le_height_ratio (W L : ℝ) (q : ℕ)
    (hW : 1 ≤ W) (hL : 0 < L) :
    1 / L ^ q ≤ L * (W / L) ^ (q + 1) := by
  calc
    _ ≤ W ^ (q + 1) / L ^ q :=
      div_le_div_of_nonneg_right (one_le_pow₀ hW) (by positivity)
    _ = _ := by rw [div_pow, pow_succ L]; field_simp

/-- Uniform control of each retained actual horizontal term, including all
frequencies, not merely a logarithmic band. -/
theorem eventually_rationalHorizontalTaylorTerm_ratio_bound
    (j : ℕ) (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖rationalHorizontalTaylorTerm T n m j‖ ≤
        K * Real.log T * (rationalModeWeight n m / Real.log T) ^ (2 * (j + 1)) := by
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  let D : ℝ := (8 : ℝ) ^ (2 * (j + 1)) * (2 * C / 3)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT
  intro n m hn hm
  have hT1 : 1 < T := hT₀.trans_le hT
  have hL : 0 < Real.log T := Real.log_pos hT1
  let u := Real.log ((n : ℝ) / (m : ℝ))
  let W := rationalModeWeight n m
  have huW : |u| ≤ W := rational_log_abs_le_weight n m hn hm
  have hW : 0 ≤ W := (abs_nonneg u).trans huW
  have hb := normalized_evenHorizontalTaylorTerm_of_selberg
    T u C (1 / 4) j hT1 hC (by norm_num) (hden T hT)
  change ‖rationalHorizontalTaylorTerm T n m j‖ ≤ _ at hb
  have hbase : 2 * |u| / ((1 / 4) * Real.log T) ≤ 8 * W / Real.log T := by
    apply (div_le_div_iff₀ (by positivity) hL).2
    nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |u| / ((1 / 4) * Real.log T))
    hbase (2 * (j + 1))
  calc
    _ ≤ (8 * W / Real.log T) ^ (2 * (j + 1)) * (2 * C * Real.log T / 3) :=
      hb.trans (mul_le_mul_of_nonneg_right hp (by positivity))
    _ = D * Real.log T * (W / Real.log T) ^ (2 * (j + 1)) := by
      dsimp [D]
      simp only [div_pow, mul_pow]
      ring
    _ ≤ (D + 1) * Real.log T * (W / Real.log T) ^ (2 * (j + 1)) := by
      have hratio : 0 ≤ (W / Real.log T) ^ (2 * (j + 1)) := by positivity
      nlinarith

/-- All retained orders have an actual low-band corrected estimate. Constants
and the common height threshold precede every rational mode. -/
theorem eventually_higherCorrectedRationalRemainder_lowBand
    (J : ℕ) (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m → rationalModeWeight n m ≤ Real.log T / 8 →
      ‖higherCorrectedRationalRemainder T n m J‖ ≤
        K * Real.log T * (rationalModeWeight n m / Real.log T) ^ (2 * (J + 1)) := by
  obtain ⟨CL, hCL, hland⟩ := eventually_rational_landau_error_le_inv_log_pow (2 * J + 1)
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  let D : ℝ := (8 : ℝ) ^ (2 * (J + 1)) * (2 * C / 3)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D + CL, by positivity, ?_⟩
  filter_upwards [hland, eventually_ge_atTop T₀] with T hland hT
  have hT1 : 1 < T := hT₀.trans_le hT
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hpos (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
      (hband : rationalModeWeight n m ≤ Real.log T / 8) :
      ‖higherCorrectedRationalRemainder T n m J‖ ≤
        (D + CL) * Real.log T *
          (rationalModeWeight n m / Real.log T) ^ (2 * (J + 1)) := by
    have hn : 1 ≤ n := by omega
    let W := rationalModeWeight n m
    let u := Real.log ((n : ℝ) / (m : ℝ))
    have hW : 1 ≤ W := by
      dsimp [W, rationalModeWeight]
      linarith [abs_nonneg (Real.log (n : ℝ) + Real.log (m : ℝ))]
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hlm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hlogW : Real.log (n : ℝ) ≤ W := by
      dsimp [W, rationalModeWeight]
      rw [abs_of_nonneg (add_nonneg hln hlm)]
      linarith
    have huW : |u| ≤ W := rational_log_abs_le_weight n m hn hm
    have hu : |u| ≤ (1 / 4) * Real.log T / 2 := by linarith
    have hE := normalized_horizontalTaylorError_of_selberg
      T u C (1 / 4) J hT1 hC (by norm_num) hu (hden T hT)
    have hbase : 2 * |u| / ((1 / 4) * Real.log T) ≤ 8 * W / Real.log T := by
      apply (div_le_div_iff₀ (by positivity) hL).2
      nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |u| / ((1 / 4) * Real.log T))
      hbase (2 * (J + 1))
    have hE' : ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
        D * Real.log T * (W / Real.log T) ^ (2 * (J + 1)) := by
      calc
        _ ≤ (8 * W / Real.log T) ^ (2 * (J + 1)) * (2 * C * Real.log T / 3) :=
          hE.trans (mul_le_mul_of_nonneg_right hp (by positivity))
        _ = _ := by dsimp [D]; simp only [div_pow, mul_pow]; ring
    have hLa := hland n m hm hmn (hlogW.trans hband)
    have hi := inverse_pow_le_height_ratio W (Real.log T) (2 * J + 1) hW hL
    have hpow : 2 * J + 1 + 1 = 2 * (J + 1) := by omega
    rw [hpow] at hi
    have hLa' : ‖(landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)) /
        (T : ℂ)‖ ≤ CL * Real.log T * (W / Real.log T) ^ (2 * (J + 1)) := by
      apply hLa.trans
      have hh := mul_le_mul_of_nonneg_left hi hCL.le
      simpa only [mul_one_div, mul_assoc] using hh
    rw [higherCorrectedRationalRemainder_eq_taylor_landau T hT0.ne' hmn J]
    exact (norm_add_le _ _).trans (by nlinarith [hE', hLa'])
  intro n m hn hm hband
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact hpos n m hm hmn hband
  · subst n
    rw [higherCorrectedRationalRemainder_self T m J hm, norm_zero]
    have hw : 0 ≤ rationalModeWeight m m := by dsimp [rationalModeWeight]; positivity
    positivity
  · rw [higherCorrectedRationalRemainder_swap T n m J hn hm, norm_star]
    have hb' : rationalModeWeight m n ≤ Real.log T / 8 := by
      simpa only [rationalModeWeight, add_comm] using hband
    simpa only [rationalModeWeight, add_comm] using hpos m n hn hnm hb'

/-- Global coarse control at every fixed retained order. The induction uses
the actual next horizontal term above the band and the next Taylor remainder
inside the band. -/
theorem eventually_higherCorrectedRationalRemainder_ratio_coarse
    (J : ℕ) (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
        K * Real.log T * (rationalModeWeight n m / Real.log T) ^ (2 * (J + 1)) := by
  induction J with
  | zero =>
    obtain ⟨K, hK, hb⟩ := eventually_correctedRationalRemainder_quadratic hD
    refine ⟨K, hK, ?_⟩
    filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
    intro n m hn hm
    have hL : 0 < Real.log T := Real.log_pos hT1
    simpa only [Nat.zero_add, Nat.mul_one, higherCorrectedRationalRemainder_one,
      div_pow, mul_div_assoc, mul_pow] using
      (hT n m hn hm).trans_eq (show
        K * rationalModeWeight n m ^ 2 / Real.log T =
          K * Real.log T * (rationalModeWeight n m / Real.log T) ^ 2 by field_simp)
  | succ J ih =>
    obtain ⟨CK, hCK, hcoarse⟩ := ih
    obtain ⟨CL, hCL, hlow⟩ := eventually_higherCorrectedRationalRemainder_lowBand (J + 2) hD
    obtain ⟨CM, hCM, hterm⟩ := eventually_rationalHorizontalTaylorTerm_ratio_bound (J + 1) hD
    let K := CL + 64 * CK + CM
    have hK : 0 < K := by dsimp [K]; positivity
    refine ⟨K, hK, ?_⟩
    filter_upwards [hcoarse, hlow, hterm, eventually_gt_atTop (1 : ℝ)]
      with T hcoarse hlow hterm hT1
    intro n m hn hm
    have hL : 0 < Real.log T := Real.log_pos hT1
    let W := rationalModeWeight n m
    let y := W / Real.log T
    have hW : 1 ≤ W := by
      dsimp [W, rationalModeWeight]
      linarith [abs_nonneg (Real.log (n : ℝ) + Real.log (m : ℝ))]
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have he1 : 2 * (J + 2) = 2 * (J + 1) + 2 := by omega
    have he2 : 2 * (J + 2 + 1) = 2 * (J + 2) + 2 := by omega
    have hK1 : CL ≤ K := by dsimp [K]; linarith
    have hK2 : 64 * CK + CM ≤ K := by dsimp [K]; linarith
    change ‖higherCorrectedRationalRemainder T n m (J + 2)‖ ≤
      K * Real.log T * y ^ (2 * (J + 2))
    by_cases hband : W ≤ Real.log T / 8
    · have hy1 : y ≤ 1 := (div_le_one hL).2 (by linarith)
      have hy2 : y ^ 2 ≤ 1 := by nlinarith
      have hh := hlow n m hn hm hband
      change ‖higherCorrectedRationalRemainder T n m (J + 2)‖ ≤
        CL * Real.log T * y ^ (2 * (J + 2 + 1)) at hh
      rw [he2, pow_add] at hh
      calc
        _ ≤ CL * Real.log T * (y ^ (2 * (J + 2)) * y ^ 2) := hh
        _ ≤ CL * Real.log T * y ^ (2 * (J + 2)) := by
          have h := mul_le_mul_of_nonneg_left hy2
            (show 0 ≤ CL * Real.log T * y ^ (2 * (J + 2)) by positivity)
          nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK1 hL.le) (pow_nonneg hy _)
    · have hy8 : 1 / 8 ≤ y := (le_div_iff₀ hL).2 (by linarith)
      have hy2 : 1 ≤ 64 * y ^ 2 := by nlinarith
      have hb := hcoarse n m hn hm
      change ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
        CK * Real.log T * y ^ (2 * (J + 1)) at hb
      have hb' : ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
          64 * CK * Real.log T * y ^ (2 * (J + 2)) := by
        apply hb.trans
        rw [he1, pow_add]
        have hh := mul_le_mul_of_nonneg_left hy2
          (show 0 ≤ CK * Real.log T * y ^ (2 * (J + 1)) by positivity)
        nlinarith
      have hm' := hterm n m hn hm
      change ‖rationalHorizontalTaylorTerm T n m (J + 1)‖ ≤
        CM * Real.log T * y ^ (2 * (J + 2)) at hm'
      rw [show J + 2 = (J + 1) + 1 by omega,
        higherCorrectedRationalRemainder_succ]
      calc
        _ ≤ ‖higherCorrectedRationalRemainder T n m (J + 1)‖ +
            ‖rationalHorizontalTaylorTerm T n m (J + 1)‖ := norm_add_le _ _
        _ ≤ (64 * CK + CM) * Real.log T * y ^ (2 * (J + 2)) := by
          nlinarith [hb', hm']
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK2 hL.le) (pow_nonneg hy _)

/-- Global fine estimate at each fixed retained order. -/
theorem eventually_higherCorrectedRationalRemainder_ratio_fine
    (J : ℕ) (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
        K * Real.log T * (rationalModeWeight n m / Real.log T) ^ (2 * (J + 2)) := by
  obtain ⟨CK, hCK, hcoarse⟩ := eventually_higherCorrectedRationalRemainder_ratio_coarse J hD
  obtain ⟨CL, hCL, hlow⟩ := eventually_higherCorrectedRationalRemainder_lowBand (J + 1) hD
  refine ⟨CL + 64 * CK, by positivity, ?_⟩
  filter_upwards [hcoarse, hlow, eventually_gt_atTop (1 : ℝ)] with T hcoarse hlow hT1
  intro n m hn hm
  have hL : 0 < Real.log T := Real.log_pos hT1
  let W := rationalModeWeight n m
  let y := W / Real.log T
  have hW : 1 ≤ W := by
    dsimp [W, rationalModeWeight]
    linarith [abs_nonneg (Real.log (n : ℝ) + Real.log (m : ℝ))]
  have hy : 0 ≤ y := by dsimp [y]; positivity
  by_cases hband : W ≤ Real.log T / 8
  · exact (hlow n m hn hm hband).trans (by
      have hh : 0 ≤ 64 * CK * Real.log T * y ^ (2 * (J + 2)) := by positivity
      change CL * Real.log T * y ^ (2 * (J + 2)) ≤
        (CL + 64 * CK) * Real.log T * y ^ (2 * (J + 2))
      nlinarith)
  · have hy8 : 1 / 8 ≤ y := (le_div_iff₀ hL).2 (by linarith)
    have hy2 : 1 ≤ 64 * y ^ 2 := by nlinarith
    have hb := hcoarse n m hn hm
    change ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
      CK * Real.log T * y ^ (2 * (J + 1)) at hb
    apply hb.trans
    change CK * Real.log T * y ^ (2 * (J + 1)) ≤
      (CL + 64 * CK) * Real.log T * y ^ (2 * (J + 2))
    rw [show 2 * (J + 2) = 2 * (J + 1) + 2 by omega, pow_add]
    have hh := mul_le_mul_of_nonneg_left hy2
      (show 0 ≤ CK * Real.log T * y ^ (2 * (J + 1)) by positivity)
    have hp : 0 ≤ CL * Real.log T * (y ^ (2 * (J + 1)) * y ^ 2) := by positivity
    nlinarith

/-- Saturated all-orders envelope. For retained order r=J+1, the factor is
L·(w/L)^(2r)·min(1,(w/L)²), exactly the paper's endpoint scale. -/
theorem eventually_higherCorrectedRationalRemainder_saturated
    (J : ℕ) (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ,
      1 ≤ n → 1 ≤ m →
      ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
        (K * Real.log T * (rationalModeWeight n m / Real.log T) ^ (2 * (J + 1))) *
          min 1 ((rationalModeWeight n m / Real.log T) ^ 2) := by
  obtain ⟨CK, hCK, hcoarse⟩ := eventually_higherCorrectedRationalRemainder_ratio_coarse J hD
  obtain ⟨CF, hCF, hfine⟩ := eventually_higherCorrectedRationalRemainder_ratio_fine J hD
  refine ⟨CK + CF, by positivity, ?_⟩
  filter_upwards [hcoarse, hfine, eventually_gt_atTop (1 : ℝ)] with T hcoarse hfine hT1
  intro n m hn hm
  have hL : 0 < Real.log T := Real.log_pos hT1
  let y := rationalModeWeight n m / Real.log T
  have hy : 0 ≤ y := by
    dsimp [y, rationalModeWeight]
    positivity
  have hbase : 0 ≤ (CK + CF) * Real.log T * y ^ (2 * (J + 1)) := by positivity
  change ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
    ((CK + CF) * Real.log T * y ^ (2 * (J + 1))) * min 1 (y ^ 2)
  rw [mul_min_of_nonneg _ _ hbase, mul_one]
  apply le_min
  · exact (hcoarse n m hn hm).trans (by
      change CK * Real.log T * y ^ (2 * (J + 1)) ≤ _
      nlinarith [show 0 ≤ CF * Real.log T * y ^ (2 * (J + 1)) by positivity])
  · have hh := hfine n m hn hm
    change ‖higherCorrectedRationalRemainder T n m (J + 1)‖ ≤
      CF * Real.log T * y ^ (2 * (J + 2)) at hh
    rw [show 2 * (J + 2) = 2 * (J + 1) + 2 by omega, pow_add] at hh
    nlinarith [show 0 ≤ CK * Real.log T * (y ^ (2 * (J + 1)) * y ^ 2) by positivity]

end RiemannResearch.Analysis.ActualZeroOrdinate
