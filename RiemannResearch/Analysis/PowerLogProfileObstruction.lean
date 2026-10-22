/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Power-log profile budgets and delayed increments

Analytic support for the positive cutoff obstruction in
`RH/MertensStretchedContinuation20260927.md`. Source: the user-requested audit
of the existing recurrence; proofs use Mathlib power/log asymptotics and elementary
logarithmic inequalities. No arithmetic lower bound or novelty claim is made.
-/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RiemannResearch.Analysis

/-- A bounded real-power/log monomial has lexicographically nonpositive exponents.
This is an asymptotic comparison theorem; it contains no arithmetic assumption. -/
theorem rpow_log_rpow_exponents_of_eventually_bounded
    (r s C : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop, T ^ r * (Real.log T) ^ s ≤ C) :
    r ≤ 0 ∧ (r = 0 → s ≤ 0) := by
  constructor
  · by_contra hr
    have hrpos : 0 < r := lt_of_not_ge hr
    have hhalf : 0 < r / 2 := by linarith only [hrpos]
    have hsmall := (isLittleO_log_rpow_rpow_atTop (-s) hhalf).bound
      (by norm_num : (0 : ℝ) < 1)
    have hlarge := (tendsto_rpow_atTop hhalf).eventually (eventually_gt_atTop C)
    obtain ⟨T, hTbound, hTsmall, hTlarge, hT, hlog⟩ :=
      (hbound.and (hsmall.and (hlarge.and ((eventually_ge_atTop (1 : ℝ)).and
        (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))))))).exists
    have hTpos : 0 < T := by linarith only [hT]
    have hlogpos : 0 < Real.log T := by linarith only [hlog]
    have hTsmall' : (Real.log T) ^ (-s) ≤ T ^ (r / 2) := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hlogpos.le (-s)),
        abs_of_nonneg (Real.rpow_nonneg hTpos.le (r / 2)), one_mul] using hTsmall
    have hC : 0 < C := lt_of_lt_of_le
      (mul_pos (Real.rpow_pos_of_pos hTpos r) (Real.rpow_pos_of_pos hlogpos s)) hTbound
    have hcancel : (Real.log T) ^ s * (Real.log T) ^ (-s) = 1 := by
      rw [← Real.rpow_add hlogpos]
      simp
    have hprod : T ^ r ≤ C * (Real.log T) ^ (-s) := by
      have hh := mul_le_mul_of_nonneg_right hTbound
        (Real.rpow_nonneg hlogpos.le (-s))
      simpa only [mul_assoc, hcancel, mul_one] using hh
    have hsplit : T ^ r = T ^ (r / 2) * T ^ (r / 2) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring
    have hprod' := hprod.trans (mul_le_mul_of_nonneg_left hTsmall' hC.le)
    rw [hsplit] at hprod'
    nlinarith only [hprod', hTlarge, Real.rpow_pos_of_pos hTpos (r / 2)]
  · intro hr
    by_contra hs
    have hspos : 0 < s := lt_of_not_ge hs
    have hlarge := ((tendsto_rpow_atTop hspos).comp Real.tendsto_log_atTop).eventually
      (eventually_gt_atTop C)
    obtain ⟨T, hTbound, hTlarge⟩ := (hbound.and hlarge).exists
    simp only [hr, Real.rpow_zero, one_mul] at hTbound
    exact (not_lt_of_ge hTbound) hTlarge

/-- The normalized eleventh-power budget forces the regular-profile exponent
boundary, including arbitrary negative logarithmic exponents. -/
theorem regular_profile_exponents_of_normalized_budget
    (β η C : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop,
      T ^ (11 * β - 1) * (Real.log T) ^ (11 * η - 1) ≤ C) :
    β ≤ (1 : ℝ) / 11 ∧ (β = (1 : ℝ) / 11 → η ≤ (1 : ℝ) / 11) := by
  obtain ⟨hβ, hη⟩ :=
    rpow_log_rpow_exponents_of_eventually_bounded (11 * β - 1) (11 * η - 1) C hbound
  refine ⟨by linarith only [hβ], ?_⟩
  intro hβeq
  have hh := hη (by rw [hβeq]; norm_num)
  linarith only [hh]

/-- The non-normalized eleventh-power budget has the same sharp exponent boundary. -/
theorem regular_profile_exponents_of_power_budget
    (β η C : ℝ)
    (hbound : ∀ᶠ T : ℝ in atTop,
      (T ^ β * (Real.log T) ^ η) ^ (11 : ℕ) ≤ C * T * Real.log T) :
    β ≤ (1 : ℝ) / 11 ∧ (β = (1 : ℝ) / 11 → η ≤ (1 : ℝ) / 11) := by
  apply regular_profile_exponents_of_normalized_budget β η C
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with T hTbound hT hlog
  have hTpos : 0 < T := by linarith only [hT]
  have hlogpos : 0 < Real.log T := by linarith only [hlog]
  have hpow : (T ^ β * (Real.log T) ^ η) ^ (11 : ℕ) =
      T ^ (11 * β) * (Real.log T) ^ (11 * η) := by
    rw [mul_pow, ← Real.rpow_natCast (T ^ β) 11,
      ← Real.rpow_natCast ((Real.log T) ^ η) 11,
      ← Real.rpow_mul hTpos.le, ← Real.rpow_mul hlogpos.le]
    congr 1 <;> congr 1 <;> ring
  rw [hpow] at hTbound
  rw [Real.rpow_sub hTpos, Real.rpow_sub hlogpos, Real.rpow_one, Real.rpow_one,
    div_mul_div_comm]
  apply (div_le_iff₀ (mul_pos hTpos hlogpos)).2
  simpa only [mul_assoc] using hTbound

/-- Multiplying the phase by an arbitrary positive constant does not change
the necessary regular-profile exponents. -/
theorem scaled_regular_profile_exponents_of_power_budget
    (b β η C : ℝ) (hb : 0 < b)
    (hbound : ∀ᶠ T : ℝ in atTop,
      (b * (T ^ β * (Real.log T) ^ η)) ^ (11 : ℕ) ≤ C * T * Real.log T) :
    β ≤ (1 : ℝ) / 11 ∧ (β = (1 : ℝ) / 11 → η ≤ (1 : ℝ) / 11) := by
  apply regular_profile_exponents_of_power_budget β η (C / b ^ (11 : ℕ))
  filter_upwards [hbound] with T hT
  have hbpow : 0 < b ^ (11 : ℕ) := pow_pos hb _
  have hh : (T ^ β * (Real.log T) ^ η) ^ (11 : ℕ) ≤
      (C * T * Real.log T) / b ^ (11 : ℕ) := by
    apply (le_div_iff₀ hbpow).2
    simpa only [mul_assoc, mul_pow, mul_comm, mul_left_comm] using hT
  convert hh using 1; ring

/-- Every positive-power regular phase eventually absorbs the logarithmic
prefactor appearing in the positive forcing term. -/
theorem regular_profile_eventually_superlog
    (b β η H : ℝ) (hb : 0 < b) (hβ : 0 < β) :
    ∀ᶠ T : ℝ in atTop,
      2 * (Real.log T + Real.log H) ≤ b * (T ^ β * (Real.log T) ^ η) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 - η) hβ).bound
    (show (0 : ℝ) < b / 4 by linarith only [hb])
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 |Real.log H|))]
    with T hTsmall hT hlog
  have hTpos : 0 < T := by linarith only [hT]
  have hlogpos : 0 < Real.log T := by
    have hh := (le_max_left (1 : ℝ) |Real.log H|).trans hlog
    linarith only [hh]
  have hTsmall' : (Real.log T) ^ (1 - η) ≤ (b / 4) * T ^ β := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlogpos.le (1 - η)),
      abs_of_nonneg (Real.rpow_nonneg hTpos.le β)] using hTsmall
  have hh := mul_le_mul_of_nonneg_right hTsmall'
    (Real.rpow_nonneg hlogpos.le η)
  rw [← Real.rpow_add hlogpos, show 1 - η + η = 1 by ring, Real.rpow_one] at hh
  have hH : Real.log H ≤ Real.log T :=
    (le_abs_self (Real.log H)).trans ((le_max_right (1 : ℝ) |Real.log H|).trans hlog)
  calc
    2 * (Real.log T + Real.log H) ≤ 4 * Real.log T := by linarith only [hH]
    _ ≤ b * (T ^ β * (Real.log T) ^ η) := by nlinarith only [hh]


/-- Exact classification of bounded power/log budgets. The converse concerns
this algebraic budget only, not the positive recurrence certificate. -/
theorem rpow_log_rpow_eventually_bounded_iff (r s : ℝ) :
    (∃ C : ℝ, ∀ᶠ T : ℝ in atTop, T ^ r * (Real.log T) ^ s ≤ C) ↔
      r < 0 ∨ (r = 0 ∧ s ≤ 0) := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨hr, hs⟩ := rpow_log_rpow_exponents_of_eventually_bounded r s C hC
    rcases lt_or_eq_of_le hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr ⟨hr, hs hr⟩
  · intro h
    refine ⟨1, ?_⟩
    rcases h with hr | ⟨rfl, hs⟩
    · have hsmall := (isLittleO_log_rpow_rpow_atTop s (show 0 < -r by linarith only [hr])).bound
        (by norm_num : (0 : ℝ) < 1)
      filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ),
        Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
        with T hTsmall hT hlog
      have hTpos : 0 < T := by linarith only [hT]
      have hlogpos : 0 < Real.log T := by linarith only [hlog]
      have hTsmall' : (Real.log T) ^ s ≤ T ^ (-r) := by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hlogpos.le s),
          abs_of_nonneg (Real.rpow_nonneg hTpos.le (-r)), one_mul] using hTsmall
      have hh := mul_le_mul_of_nonneg_left hTsmall' (Real.rpow_nonneg hTpos.le r)
      simpa only [← Real.rpow_add hTpos, add_neg_cancel, Real.rpow_zero] using hh
    · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
        with T hlog
      simpa only [Real.rpow_zero, one_mul] using
        (Real.rpow_le_one_of_one_le_of_nonpos hlog hs)

end RiemannResearch.Analysis

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

private theorem positive_gap_lower_bound (A B a d : ℝ)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hgain : (1 + a * d) * B ≤ A) :
    (a / (1 + a)) * A * d ≤ A - B := by
  have hBA : B ≤ A := by nlinarith only [hgain, mul_nonneg (mul_nonneg ha hd) hB]
  have hAB : 0 ≤ A - B := sub_nonneg.mpr hBA
  have had : a * d ≤ a := by nlinarith only [ha, hd1]
  have hmul := mul_le_mul_of_nonneg_right had hAB
  have hmain : a * A * d ≤ (A - B) * (1 + a) := by nlinarith only [hgain, hmul]
  have hden : 0 < 1 + a := by linarith
  have hh : (a * A * d) / (1 + a) ≤ A - B := (div_le_iff₀ hden).mpr hmain
  convert hh using 1; ring

private theorem exp_gap_lower_bound (s t a d : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hgap : a * d ≤ s - t) :
    (a / (1 + a)) * Real.exp s * d ≤ Real.exp s - Real.exp t := by
  have hexp : 1 + a * d ≤ Real.exp (s - t) := by
    linarith only [hgap, Real.add_one_le_exp (s - t)]
  have hgain := mul_le_mul_of_nonneg_right hexp (Real.exp_pos t).le
  have he : Real.exp (s - t) * Real.exp t = Real.exp s := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hgain
  exact positive_gap_lower_bound _ _ _ _ (Real.exp_pos _).le ha hd hd1 hgain

/-- Explicit finite lower shift for every regular stretched profile. The size
condition makes its logarithmic slope positive even for a negative log exponent.
It is an analytic property of the trial profile, not a lower bound for Mertens. -/
theorem regular_profile_lower_shift (beta eta T r : ℝ)
    (hbeta : 0 < beta) (hr : 1 < r) (hrT : r ≤ T)
    (hsize : 2 * |eta| ≤ beta * Real.log r) :
    (beta / (beta + 2)) * (T ^ beta * (Real.log T) ^ eta) * ((T - r) / T) ≤
      T ^ beta * (Real.log T) ^ eta - r ^ beta * (Real.log r) ^ eta := by
  have hr0 : 0 < r := by linarith
  have hT0 : 0 < T := lt_of_lt_of_le hr0 hrT
  have hlr : 0 < Real.log r := Real.log_pos hr
  have hlT : 0 < Real.log T := Real.log_pos (lt_of_lt_of_le hr hrT)
  have hlrT : Real.log r ≤ Real.log T := Real.log_le_log hr0 hrT
  have hllrT : Real.log (Real.log r) ≤ Real.log (Real.log T) :=
    Real.log_le_log hlr hlrT
  let u := Real.log T - Real.log r
  let v := Real.log (Real.log T) - Real.log (Real.log r)
  let d := (T - r) / T
  have hu : 0 ≤ u := sub_nonneg.mpr hlrT
  have hv : 0 ≤ v := sub_nonneg.mpr hllrT
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr hrT) hT0.le
  have hd1 : d ≤ 1 := by
    dsimp [d]
    apply (div_le_iff₀ hT0).mpr
    linarith
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hlT hlr)
  rw [Real.log_div hlT.ne' hlr.ne'] at hlogratio
  have hscaled := mul_le_mul_of_nonneg_left hlogratio hlr.le
  have he : Real.log r * (Real.log T / Real.log r - 1) = u := by
    dsimp [u]
    field_simp [hlr.ne']
  have hscaled' : Real.log r * v ≤ u := by
    simpa only [v, he] using hscaled
  have hsizev := mul_le_mul_of_nonneg_right hsize hv
  have hbetascale := mul_le_mul_of_nonneg_left hscaled' hbeta.le
  have hetav := mul_le_mul_of_nonneg_right (neg_abs_le eta) hv
  have hloggap : (beta / 2) * u ≤ beta * u + eta * v := by
    nlinarith only [hsizev, hbetascale, hetav]
  have hratio := Real.log_le_sub_one_of_pos (div_pos hr0 hT0)
  rw [Real.log_div hr0.ne' hT0.ne'] at hratio
  have hratiom := mul_le_mul_of_nonneg_left hratio hT0.le
  have he' : T * (r / T - 1) = r - T := by field_simp [hT0.ne']
  rw [he'] at hratiom
  have hdu : d ≤ u := by
    dsimp [d, u]
    apply (div_le_iff₀ hT0).mpr
    nlinarith only [hratiom]
  have hagap : (beta / 2) * d ≤
      (Real.log T * beta + Real.log (Real.log T) * eta) -
      (Real.log r * beta + Real.log (Real.log r) * eta) := by
    have hh := mul_le_mul_of_nonneg_left hdu (show 0 ≤ beta / 2 by linarith)
    dsimp [u, v] at hloggap
    nlinarith only [hh, hloggap]
  have hh := exp_gap_lower_bound
    (Real.log T * beta + Real.log (Real.log T) * eta)
    (Real.log r * beta + Real.log (Real.log r) * eta)
    (beta / 2) d (by linarith) hd hd1 hagap
  have hcoef : (beta / 2) / (1 + beta / 2) = beta / (beta + 2) := by
    have hb2 : beta + 2 ≠ 0 := by linarith
    have hhalf : 1 + beta / 2 ≠ 0 := by linarith
    field_simp [hb2, hhalf]; ring
  rw [hcoef] at hh
  rw [Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hlT,
    Real.rpow_def_of_pos hr0, Real.rpow_def_of_pos hlr]
  simp only [← Real.exp_add]
  exact hh

theorem regular_profile_lower_shift_scaled (b beta eta T r : ℝ)
    (hb : 0 ≤ b) (hbeta : 0 < beta) (hr : 1 < r) (hrT : r ≤ T)
    (hsize : 2 * |eta| ≤ beta * Real.log r) :
    (beta / (beta + 2)) * (b * (T ^ beta * (Real.log T) ^ eta)) * ((T - r) / T) ≤
      b * (T ^ beta * (Real.log T) ^ eta) - b * (r ^ beta * (Real.log r) ^ eta) := by
  have hh := mul_le_mul_of_nonneg_left
    (regular_profile_lower_shift beta eta T r hbeta hr hrT hsize) hb
  simpa only [mul_sub, mul_assoc, mul_left_comm, mul_comm] using hh

/-- The finite threshold holds automatically at infinity for any cutoff whose
remaining argument tends to infinity. -/
theorem regular_profile_lower_shift_eventually (b beta eta : ℝ) (r : ℝ → ℝ)
    (hb : 0 ≤ b) (hbeta : 0 < beta)
    (hr : Tendsto r atTop atTop) (hrT : ∀ᶠ T in atTop, r T ≤ T) :
    ∀ᶠ T in atTop,
      (beta / (beta + 2)) * (b * (T ^ beta * (Real.log T) ^ eta)) * ((T - r T) / T) ≤
        b * (T ^ beta * (Real.log T) ^ eta) -
          b * ((r T) ^ beta * (Real.log (r T)) ^ eta) := by
  have hlog := (Real.tendsto_log_atTop.comp hr).eventually
    (eventually_ge_atTop ((2 * |eta|) / beta))
  filter_upwards [hrT, hr.eventually (eventually_ge_atTop (2 : ℝ)), hlog] with T hrT hr2 hlog
  apply regular_profile_lower_shift_scaled b beta eta T (r T) hb hbeta
    (by linarith) hrT
  have hh := (div_le_iff₀ hbeta).mp hlog
  simpa only [Function.comp_apply, mul_comm] using hh

/-- The delayed recurrence uses `r = T - L - log 2`; its full profile shift
therefore dominates the cutoff length `L`. -/
theorem regular_profile_lower_cutoff_shift (b beta eta T L r : ℝ)
    (hb : 0 ≤ b) (hbeta : 0 < beta) (hL : 0 ≤ L)
    (hr : 1 < r) (hrdef : r = T - L - Real.log 2)
    (hsize : 2 * |eta| ≤ beta * Real.log r) :
    (beta / (beta + 2)) * (b * (T ^ beta * (Real.log T) ^ eta)) * L / T ≤
      b * (T ^ beta * (Real.log T) ^ eta) - b * (r ^ beta * (Real.log r) ^ eta) := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hrT : r ≤ T := by linarith
  have hT : 0 < T := by linarith only [hr, hrT]
  have hT1 : 1 < T := hr.trans_le hrT
  have hlT : 0 < Real.log T := Real.log_pos hT1
  have hcoef : 0 ≤ (beta / (beta + 2)) * (b * (T ^ beta * (Real.log T) ^ eta)) := by
    positivity
  have hgap : L / T ≤ (T - r) / T :=
    div_le_div_of_nonneg_right (by linarith) hT.le
  have hmul := mul_le_mul_of_nonneg_left hgap hcoef
  have hh := regular_profile_lower_shift_scaled b beta eta T r hb hbeta hr hrT hsize
  calc
    _ = (beta / (beta + 2)) * (b * (T ^ beta * (Real.log T) ^ eta)) * (L / T) := by ring
    _ ≤ (beta / (beta + 2)) * (b * (T ^ beta * (Real.log T) ^ eta)) * ((T - r) / T) := hmul
    _ ≤ _ := hh

end RiemannResearch.Analysis
