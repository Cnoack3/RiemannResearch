/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualCriticalProportionDisplacement
import RiemannResearch.Analysis.ActualZeroLoglogTilt
import RiemannResearch.Analysis.ActualZeroHorizontalMomentRate
import RiemannResearch.Analysis.FiniteStrictTailSecondMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Capped Selberg bounds for the actual horizontal energy

At each height, combine the off-line count with the exponential density
estimate before integrating the quadratic moment. The cutoff at displacement
1/2 gives a negative explicit boundary term. When the two envelopes meet
inside the strip their crossing gives the exact integral of their minimum.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem integral_linear_constant (F d : ℝ) :
    (∫ t in (0 : ℝ)..d, F * (2 * t)) = F * d ^ 2 := by
  rw [show (fun t : ℝ => F * (2 * t)) = (fun t : ℝ => (F * 2) * t) by funext t; ring,
    intervalIntegral.integral_const_mul, integral_id]
  ring

private theorem integral_linear_exp_between (M q d B : ℝ) (hq : 0 < q) :
    (∫ t in d..B, (M * Real.exp (-q * t)) * (2 * t)) =
      2 * M / q ^ 2 * ((1 + q * d) * Real.exp (-q * d) - (1 + q * B) * Real.exp (-q * B)) := by
  have hc : Continuous (fun t : ℝ => t * Real.exp (-q * t)) := by fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 d) (hc.intervalIntegrable (μ := volume) d B)
  rw [FiniteStrictTail.integral_linear_exponential q d hq,
    FiniteStrictTail.integral_linear_exponential q B hq] at hi
  rw [show (fun t : ℝ => (M * Real.exp (-q * t)) * (2 * t)) =
    (fun t : ℝ => (2 * M) * (t * Real.exp (-q * t))) by funext t; ring,
    intervalIntegral.integral_const_mul]
  have hformula : (∫ t in d..B, t * Real.exp (-q * t)) =
      ((1 + q * d) * Real.exp (-q * d) - (1 + q * B) * Real.exp (-q * B)) / q ^ 2 := by
    calc
      _ = (1 - (1 + q * B) * Real.exp (-q * B)) / q ^ 2 -
          (1 - (1 + q * d) * Real.exp (-q * d)) / q ^ 2 := by
        apply eq_sub_of_add_eq
        rw [add_comm]
        exact hi
      _ = _ := by ring
  rw [hformula]
  ring

/-- Exact cap integral with the upper endpoint retained. Equal envelopes at
the crossing make this the pointwise minimum on the full interval. -/
theorem integral_min_constant_exponential {F M q d B : ℝ}
    (hM : 0 ≤ M) (hq : 0 < q) (hd : d ∈ Icc (0 : ℝ) B)
    (hcross : M * Real.exp (-q * d) = F) :
    (∫ t in (0 : ℝ)..B, min F (M * Real.exp (-q * t)) * (2 * t)) =
      F * d ^ 2 + 2 * M / q ^ 2 *
        ((1 + q * d) * Real.exp (-q * d) - (1 + q * B) * Real.exp (-q * B)) := by
  have hc : Continuous (fun t : ℝ => min F (M * Real.exp (-q * t)) * (2 * t)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 d) (hc.intervalIntegrable d B)]
  have hhead : (∫ t in (0 : ℝ)..d, min F (M * Real.exp (-q * t)) * (2 * t)) =
      ∫ t in (0 : ℝ)..d, F * (2 * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hd.1] at ht
    have h := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.2 (by linarith : -q ≤ 0))) hM
    rw [hcross] at h
    simp only [min_eq_left h]
  have htail : (∫ t in d..B, min F (M * Real.exp (-q * t)) * (2 * t)) =
      ∫ t in d..B, (M * Real.exp (-q * t)) * (2 * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hd.2] at ht
    have h := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (by linarith : -q ≤ 0))) hM
    rw [hcross] at h
    simp only [min_eq_right h]
  rw [hhead, htail, integral_linear_constant, integral_linear_exp_between M q d B hq]

/-- Exact two-envelope majorant for the energy of actual zero occurrences. -/
theorem horizontalEnergy_le_capped_exponential {T F M q d : ℝ}
    (hF : strictTail T 0 ≤ F) (hM : 0 ≤ M) (hq : 0 < q)
    (hd : d ∈ Icc (0 : ℝ) (1 / 2)) (hcross : M * Real.exp (-q * d) = F)
    (hD : ∀ t ∈ Icc (0 : ℝ) (1 / 2), strictTail T t ≤ M * Real.exp (-q * t)) :
    horizontalEnergy T ≤ F * d ^ 2 +
      2 * M / q ^ 2 * ((1 + q * d) * Real.exp (-q * d) - (1 + q / 2) * Real.exp (-q / 2)) := by
  rw [horizontalEnergy_eq_strictTail_integral]
  calc
    _ ≤ ∫ t in (0 : ℝ)..(1 / 2), min F (M * Real.exp (-q * t)) * (2 * t) := by
      have hc : Continuous (fun t : ℝ => min F (M * Real.exp (-q * t)) * (2 * t)) := by fun_prop
      apply intervalIntegral.integral_mono_on (by norm_num)
        (FiniteStrictTail.intervalIntegrable_tail_mul Finset.univ (copyDisplacement T)
          (fun t => 2 * t) (by fun_prop) 0 (1 / 2)) (hc.intervalIntegrable _ _)
      intro t ht
      exact mul_le_mul_of_nonneg_right (le_min ((strictTail_le_zero T t ht.1).trans hF)
        (hD t ht)) (mul_nonneg (by norm_num) ht.1)
    _ = _ := by
      rw [integral_min_constant_exponential hM hq hd hcross]
      congr 1
      ring_nf

/-- At the analytic crossing d=log(M/F)/q the rescaled bound has a closed
polynomial numerator. It can be immediately applied with q=a log T. -/
theorem horizontalEnergy_log_crossing {T F M q : ℝ}
    (hF : strictTail T 0 ≤ F) (hFp : 0 < F) (hM : F ≤ M) (hq : 0 < q)
    (hstrip : Real.log (M / F) ≤ q / 2)
    (hD : ∀ t ∈ Icc (0 : ℝ) (1 / 2), strictTail T t ≤ M * Real.exp (-q * t)) :
    horizontalEnergy T * q ^ 2 ≤ F * ((Real.log (M / F)) ^ 2 + 2 * Real.log (M / F) + 2)
      - 2 * M * (1 + q / 2) * Real.exp (-q / 2) := by
  let d := Real.log (M / F) / q
  have hMp := hFp.trans_le hM
  have hpos := div_pos hMp hFp
  have hlog : 0 ≤ Real.log (M / F) := Real.log_nonneg ((one_le_div hFp).mpr hM)
  have hd : d ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨div_nonneg hlog hq.le, (div_le_iff₀ hq).mpr (by linarith)⟩
  have heq : q * d = Real.log (M / F) := by dsimp [d]; field_simp
  have hcross : M * Real.exp (-q * d) = F := by
    rw [neg_mul, heq, Real.exp_neg, Real.exp_log hpos]
    field_simp
  have hb := mul_le_mul_of_nonneg_right
    (horizontalEnergy_le_capped_exponential hF hMp.le hq hd hcross hD) (sq_nonneg q)
  apply hb.trans_eq
  rw [heq, show Real.exp (-q * d) = F / M by apply (eq_div_iff hMp.ne').mpr; linarith [hcross]]
  dsimp [d]
  field_simp [hq.ne', hMp.ne']
  ring

/-- The polynomial advantage in the leading coefficient is strict whenever
the exponential bound at zero exceeds the off-line count cap. -/
theorem capped_energy_coefficient_lt_uncapped {F M : ℝ} (hF : 0 < F) (hFM : F < M) :
    F * (Real.log (M / F) ^ 2 + 2 * Real.log (M / F) + 2) < 2 * M := by
  let y := Real.log (M / F)
  have hy : 0 < y := Real.log_pos ((one_lt_div hF).mpr hFM)
  have he : Real.exp y = M / F := Real.exp_log (div_pos (hF.trans hFM) hF)
  have hs := Real.sum_le_exp_of_nonneg hy.le 4
  rw [he] at hs
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have hpoly : y ^ 2 + 2 * y + 2 < 2 * (M / F) := by
    nlinarith only [hs, pow_pos hy 3]
  have hscaled := mul_lt_mul_of_pos_left hpoly hF
  have heq : F * (2 * (M / F)) = 2 * M := by field_simp
  simpa only [heq, y] using hscaled

/-- Combines an actual distinct-on-line lower bound with the Selberg exponent at
every sufficiently large height. The constants C and a may vary with height
whenever their finite-height density inequality and the crossing conditions hold. -/
theorem CumulativeDistinctCriticalProportion.capped_selbergEnergy {κ : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ C a : ℝ, 0 < a → SelbergDensityBound T C a →
      let F := (1 - κ + ε) * (Ncount 0 T : ℝ)
      let M := 2 * C * T * Real.log T
      let q := a * Real.log T
      0 < F → F ≤ M → Real.log (M / F) ≤ q / 2 →
        horizontalEnergy T * q ^ 2 ≤ F * ((Real.log (M / F)) ^ 2 + 2 * Real.log (M / F) + 2)
          - 2 * M * (1 + q / 2) * Real.exp (-q / 2) := by
  filter_upwards [hκ.normalized_tail ε hε, eventually_count_pos,
    eventually_gt_atTop (1 : ℝ)] with T htail hN hT
  intro C a ha hD F M q hFp hFM hstrip
  have hF : strictTail T 0 ≤ F :=
    (div_le_iff₀ (show 0 < (Ncount 0 T : ℝ) by exact_mod_cast hN)).mp (htail 0 le_rfl)
  apply horizontalEnergy_log_crossing hF hFp hFM (mul_pos ha (Real.log_pos hT)) hstrip
  intro t ht
  simpa only [M, q, mul_assoc] using
    strictTail_of_selbergDensity T C a t (zero_lt_one.trans hT) ht hD

/-- Convert the lower critical-line fraction to the original height
normalization. The only slack is an arbitrary increase of the limiting
coefficient above (1-κ)/(2π). -/
theorem CumulativeDistinctCriticalProportion.strictTail_zero_height {κ B : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ)
    (hB : (1 - κ) / (2 * Real.pi) < B) :
    ∀ᶠ T : ℝ in atTop, strictTail T 0 ≤ B * (T * Real.log T) := by
  let f (x : ℝ) := (1 - κ + x) * (1 / (2 * Real.pi) + x)
  have hsmall : f 0 < B := by simpa [f, div_eq_mul_inv] using hB
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 0, f x < B :=
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hsmall)
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x := self_mem_nhdsWithin
  obtain ⟨η, hη, hs⟩ := (hpos.and hev).exists
  have hn := eventually_count_le_log_of_lt
    (show 1 / (2 * Real.pi) < 1 / (2 * Real.pi) + η by linarith)
  filter_upwards [hκ.normalized_tail η hη, hn, eventually_count_pos,
    eventually_gt_atTop (1 : ℝ)] with T htail hcnt hN hT
  have hN' : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hN
  have ht := (div_le_iff₀ hN').mp (htail 0 le_rfl)
  have htr : 0 ≤ strictTail T 0 := by
    unfold strictTail FiniteStrictTail.tail
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hcoeff : 0 ≤ 1 - κ + η :=
    (div_nonneg htr hN'.le).trans (htail 0 le_rfl)
  have hTL : 0 ≤ T * Real.log T := mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le
  calc
    _ ≤ (1 - κ + η) * (Ncount 0 T : ℝ) := ht
    _ ≤ (1 - κ + η) * ((1 / (2 * Real.pi) + η) * T * Real.log T) :=
      mul_le_mul_of_nonneg_left hcnt hcoeff
    _ = f η * (T * Real.log T) := by dsimp [f]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs.le hTL

/-- The capped Selberg rate with a fixed density constant C. In the original
height normalization its coefficient is strictly smaller than 4C/a² whenever
B<2C. The finite-height theorem above additionally retains the upper endpoint. -/
theorem CumulativeDistinctCriticalProportion.capped_selberg_rate {κ C a B : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) (ha : 0 < a)
    (hB : (1 - κ) / (2 * Real.pi) < B) (hB0 : 0 < B) (hBC : B ≤ 2 * C)
    (hD : ∀ᶠ T : ℝ in atTop, SelbergDensityBound T C a) :
    ∀ᶠ T : ℝ in atTop, horizontalEnergy T / T * Real.log T ≤
      (B / a ^ 2) * (Real.log (2 * C / B) ^ 2 + 2 * Real.log (2 * C / B) + 2) := by
  have hC : 0 < C := by linarith
  filter_upwards [hκ.strictTail_zero_height hB, hD, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log (2 * C / B) / a)]
      with T htail hd ht hdsize
  let L := Real.log T
  have hT := zero_lt_one.trans ht
  have hL : 0 < L := Real.log_pos ht
  have hr : 2 * C * T * L / (B * (T * L)) = 2 * C / B := by field_simp
  have hsize : Real.log (2 * C * T * L / (B * (T * L))) ≤ a * L / 2 := by
    rw [hr]
    have h := (div_le_iff₀ ha).mp hdsize
    change 2 * Real.log (2 * C / B) ≤ L * a at h
    linarith
  have hb := horizontalEnergy_log_crossing (F := B * (T * L)) (M := 2 * C * T * L)
    (q := a * L) htail (by positivity) (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hBC (mul_pos hT hL).le)
    (mul_pos ha hL) hsize (fun t hh => by
      simpa only [L, mul_assoc] using strictTail_of_selbergDensity T C a t hT hh hd)
  rw [hr] at hb
  have hp : 0 ≤ 2 * (2 * C * T * L) * (1 + a * L / 2) * Real.exp (-(a * L) / 2) := by positivity
  have hb' : horizontalEnergy T * (a * L) ^ 2 ≤
      B * (T * L) * (Real.log (2 * C / B) ^ 2 + 2 * Real.log (2 * C / B) + 2) := by
    linarith only [hb, hp]
  have hs := (div_le_div_iff_of_pos_right (mul_pos (mul_pos hT hL) (sq_pos_of_pos ha))).mpr hb'
  change horizontalEnergy T / T * L ≤ _
  calc
    _ = (horizontalEnergy T * (a * L) ^ 2) / ((T * L) * a ^ 2) := by
      field_simp [hT.ne', hL.ne', ha.ne']
    _ ≤ _ := hs
    _ = _ := by field_simp [hT.ne', hL.ne', ha.ne']

/-- Reflection maps the strict half-plane complementary to the inclusive
right half-plane onto the strict right half-plane. This keeps critical-line
copies in the inclusive count. -/
theorem twice_rightInclusive_half_add_strictTail (T : ℝ) :
    2 * rightInclusiveCount T (1 / 2) + strictTail T 0 = 2 * (Ncount 0 T : ℝ) := by
  have href : realSum T (fun ρ => if 1 / 2 < (reflect ρ).re then 1 else 0) =
      rightStrictTail T 0 := by
    simpa only [rightStrictTail, add_zero] using
      realSum_reflect T (fun ρ => if 1 / 2 < ρ.re then (1 : ℝ) else 0)
  have hsum : rightInclusiveCount T (1 / 2) + rightStrictTail T 0 = (Ncount 0 T : ℝ) := by
    rw [← href, ← realSum_one T, rightInclusiveCount, ← realSum_add]
    congr 1
    funext ρ
    rw [reflect_re]
    by_cases h : 1 / 2 ≤ ρ.re
    · simp only [if_pos h, if_neg (show ¬ 1 / 2 < 1 - ρ.re by linarith), add_zero]
    · simp only [if_neg h, if_pos (show 1 / 2 < 1 - ρ.re by linarith), zero_add]
  rw [strictTail_eq_twice_right T 0 le_rfl]
  linarith only [hsum]

/-- An inclusive Selberg estimate at the central line forces a lower bound
on its constant even when the exponent is unspecified. -/
theorem CumulativeDistinctCriticalProportion.selbergConstant_floor {κ k C a : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) (hk : 0 ≤ k) (hkκ : k < κ)
    (hD : ∀ᶠ T : ℝ in atTop, SelbergDensityBound T C a) :
    (1 + k) / (2 * Real.pi) ≤ 2 * C := by
  have hk1 : 0 < 1 + k := by linarith
  by_contra! bad
  have hc : 2 * C / (1 + k) < 1 / (2 * Real.pi) :=
    (div_lt_iff₀ hk1).mpr (by convert bad using 1; ring)
  obtain ⟨b, hb, hb'⟩ := exists_between hc
  have he : ∀ᶠ T : ℝ in atTop, False := by
    filter_upwards [hD, hκ.normalized_tail (κ - k) (sub_pos.mpr hkκ),
      eventually_count_ge_log_of_lt hb', eventually_count_pos, eventually_gt_atTop (1 : ℝ)]
        with T hd ht hN hNpos hT
    have hN' : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hNpos
    have hhead := (div_le_iff₀ hN').mp (ht 0 le_rfl)
    have hr := (selbergDensityBound_iff_exp T C a (zero_lt_one.trans hT)).mp hd
      (1 / 2) (by norm_num)
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at hr
    have hupper : (1 + k) * (Ncount 0 T : ℝ) ≤ 2 * C * (T * Real.log T) := by
      nlinarith only [twice_rightInclusive_half_add_strictTail T, hhead, hr]
    have hh : ((1 + k) * b) * (T * Real.log T) ≤ (2 * C) * (T * Real.log T) := by
      calc
        _ = (1 + k) * (b * T * Real.log T) := by ring
        _ ≤ (1 + k) * (Ncount 0 T : ℝ) := mul_le_mul_of_nonneg_left hN hk1.le
        _ ≤ _ := hupper
    have hle := le_of_mul_le_mul_right hh (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT))
    have hlt := (div_lt_iff₀ hk1).mp hb
    linarith only [hle, hlt]
  exact he.exists.elim (fun _ hh => hh)

/-- Every inclusive Selberg constant benefits from the critical-line
proportion. For k approaching κ the improvement factor over 4C/a² is
r(1 + log(1/r) + log(1/r)²/2), with r=(1-k)/(1+k). -/
theorem CumulativeDistinctCriticalProportion.capped_selberg_uniform_gain {κ k C a : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) (hk : 0 ≤ k) (hkκ : k < κ)
    (hk1 : k < 1) (ha : 0 < a) (hD : ∀ᶠ T : ℝ in atTop, SelbergDensityBound T C a) :
    let r := (1 - k) / (1 + k)
    ∀ᶠ T : ℝ in atTop, horizontalEnergy T / T * Real.log T ≤
      (2 * C / a ^ 2) * r * (Real.log (1 / r) ^ 2 + 2 * Real.log (1 / r) + 2) := by
  let r := (1 - k) / (1 + k)
  have hkpos : 0 < 1 + k := by linarith
  have hpos : 0 < r := div_pos (sub_pos.mpr hk1) hkpos
  have hr1 : r ≤ 1 := (div_le_one hkpos).mpr (by linarith)
  have hfloor := hκ.selbergConstant_floor hk hkκ hD
  have hC2 : 0 < 2 * C := lt_of_lt_of_le (div_pos hkpos (by positivity)) hfloor
  have hB : (1 - κ) / (2 * Real.pi) < (2 * C) * r := by
    calc
      _ < (1 - k) / (2 * Real.pi) := div_lt_div_of_pos_right (by linarith) (by positivity)
      _ = ((1 + k) / (2 * Real.pi)) * r := by dsimp [r]; field_simp [hkpos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hfloor hpos.le
  have hb := hκ.capped_selberg_rate ha hB (mul_pos hC2 hpos)
    (mul_le_of_le_one_right hC2.le hr1) hD
  have hC : C ≠ 0 := by linarith
  have hrat : 2 * C / (2 * C * r) = 1 / r := by field_simp [hC, hpos.ne']
  filter_upwards [hb] with T ht
  rw [hrat] at ht
  convert ht using 1; ring

/-- The critical-line proportion is retained in the optimal cutoff limit for
the tilted fourth moment throughout the Ingham sublinear frequency band. -/
theorem CumulativeDistinctCriticalProportion.ingham_tilted_fourth {κ B D : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) (hB : 0 ≤ B)
    (hD : Real.exp (B * (3 / 2)) * (3 / 2) ^ 4 * ((1 - κ) / (2 * Real.pi)) < D) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ B*Real.log T/Real.log (Real.log T) →
      (∑ i : Copies T, (i.1.1.re-1/2)^4 * Real.exp (v*|i.1.1.re-1/2|))/T ≤
        D*(Real.log (Real.log T))^4/(Real.log T)^3 :=
  eventually_ingham_tilted_fourth_of_offline_cap hB (fun _ h => hκ.strictTail_zero_height h) hD

/-- The Montgomery–Taylor specialization uses the existing cumulative
critical-line theorem with its exact window constant. -/
theorem montgomeryTaylor_ingham_tilted_fourth {B D : ℝ} (hB : 0 ≤ B)
    (hD : Real.exp (B * (3 / 2)) * (3 / 2) ^ 4 * ((1 - ThmD.HD 1) / (2 * Real.pi)) < D) :
    ∀ᶠ T : ℝ in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ B*Real.log T/Real.log (Real.log T) →
      (∑ i : Copies T, (i.1.1.re-1/2)^4 * Real.exp (v*|i.1.1.re-1/2|))/T ≤
        D*(Real.log (Real.log T))^4/(Real.log T)^3 :=
  montgomeryTaylor_distinctCriticalProportion.ingham_tilted_fourth hB hD

/-- The inclusive central threshold contains at least half of the whole
zero multiset. Riemann–von Mangoldt therefore forces at least one logarithm
in any uniform logarithmic-loss estimate, independently of its slope. -/
theorem one_le_logPower_of_uniformLogLossDensity {a b : ℝ}
    (hD : UniformLogLossDensity a b) : 1 ≤ b := by
  by_contra! hb
  obtain ⟨C,T₀,hC,hT₀,hw⟩ := hD
  obtain ⟨c,hc,hn⟩ := exists_count_normalization
  have hz := ((tendsto_rpow_neg_atTop (show 0 < 1-b by linarith)).comp Real.tendsto_log_atTop).const_mul (2*C)
  rw [show -(1-b) = b-1 by ring] at hz
  simp only [Function.comp_apply,mul_zero] at hz
  have hbad : ∀ᶠ T : ℝ in atTop, False := by
    filter_upwards [eventually_ge_atTop T₀,hn,hz.eventually_lt_const hc] with T hT hN hsmall
    have ht := hT₀.trans_le hT
    have ht0 := zero_lt_one.trans ht
    have hL := Real.log_pos ht
    have hh := hw T hT (1/2) (by norm_num)
    simp only [sub_self,mul_zero,Real.exp_zero,mul_one] at hh
    have hNupper : c*T*Real.log T ≤ (2*C)*T*(Real.log T)^b := by
      nlinarith only [hN,hh,twice_rightInclusive_half_add_strictTail T,strictTail_le_count T 0]
    have hr : (Real.log T)^b = (Real.log T)^(b-1)*Real.log T := by
      calc
        _ = (Real.log T)^((b-1)+(1:ℝ)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hL,Real.rpow_one]
    have hm : c*(T*Real.log T) ≤ ((2*C)*(Real.log T)^(b-1))*(T*Real.log T) := by
      rw [hr] at hNupper
      linarith only [hNupper]
    exact (not_lt_of_ge (le_of_mul_le_mul_right hm (mul_pos ht0 hL))) hsmall
  exact hbad.exists.choose_spec

/-- At a slope possessing the one-logarithm Selberg estimate, the full
range of compatible global logarithmic losses is exactly b ≥ 1. -/
theorem uniformLogLossDensity_iff_of_uniformSelbergDensity {a b : ℝ}
    (hD : UniformSelbergDensity a) : UniformLogLossDensity a b ↔ 1 ≤ b := by
  refine ⟨one_le_logPower_of_uniformLogLossDensity,?_⟩
  intro hb
  obtain ⟨C,T₀,hC,hT₀,hw⟩ := uniformLogLossDensity_of_uniformSelberg a hD
  refine ⟨C,max T₀ (Real.exp 1),hC,hT₀.trans_le (le_max_left _ _),?_⟩
  intro T hT σ hσ
  have ht := (le_max_left _ _).trans hT
  have ht0 := zero_lt_one.trans (hT₀.trans_le ht)
  have hL : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  apply (hw T ht σ hσ).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hb) (mul_nonneg hC ht0.le)

end RiemannResearch.Analysis.ActualZeroOrdinate
