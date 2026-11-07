/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTProjectedMellin
import RiemannResearch.NumberTheory.DivisorEscapePrimeTail
import RiemannResearch.RH.QCRTBoundedCriterion
import RiemannResearch.Analysis.CofinalLogGrowth
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Canonical CRT zero-growth obstruction and cofinal subpolynomial RH criterion

Source: the user's CRT collocation handoff, Section 7. The actual projected
Mellin norm and LCM divisor-tail rate are supplied by checked constructions.
The canonical growth hypothesis remains explicit and is not proved here.
-/

noncomputable section
open Filter
open scoped Topology ENNReal BigOperators
namespace RiemannResearch.RH.QCRTZeroGrowth
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QMellinTransfer
open QCRTFiniteCollocation QCRTBoundedCriterion QCRTZeroObstruction QCRTProjectedMellin
open RiemannResearch.NumberTheory.DivisorEscapeTail
open RiemannResearch.Analysis.CofinalLogGrowth

/-- Offset indexing keeps every cutoff at least two. -/
def lcmStage (M : ℕ) : ℕ := Nat.lcmUpto (M + 2)

theorem lcmStage_ge (M : ℕ) : M + 2 ≤ lcmStage M :=
  Nat.le_of_dvd (Nat.lcmUpto_pos _) (positive_dvd_lcmUpto (M + 2) (M + 2) (by omega) le_rfl)

theorem lcmStage_two_le (M : ℕ) : 2 ≤ lcmStage M :=
  le_trans (by omega) (lcmStage_ge M)

def lcmLift (M : ℕ) : QHilbert := canonical (lcmStage M) (lcmStage_two_le M)
def lcmLeakage (M : ℕ) : ℝ := leakage (lcmStage M) (lcmStage_two_le M)

theorem lcmLeakage_nonneg (M : ℕ) : 0 ≤ lcmLeakage M := sq_nonneg _

theorem lcmLeakage_le_norm_sq (M : ℕ) : lcmLeakage M ≤ ‖lcmLift M‖^2 := by
  have he := canonical_norm (lcmStage M) (lcmStage_two_le M)
  have ht := target_norm_sq (lcmStage M) (by have := lcmStage_two_le M; omega)
  have hp := sq_nonneg ‖target (lcmStage M)‖
  change leakage (lcmStage M) (lcmStage_two_le M) ≤
    ‖(canonical (lcmStage M) (lcmStage_two_le M) : QHilbert)‖^2
  linarith

theorem qDivisor_norm_eq (L : ℕ) (hL : 0 < L) :
    ‖qDivisor L‖ = 1 / (L : ℝ) := by
  have h := qDivisor_norm_sq L hL
  have hp : 0 ≤ 1 / (L : ℝ) := by positivity
  have he : (1 / (L : ℝ)) ^ 2 = 1 / (L : ℝ) ^ 2 := by ring
  nlinarith [norm_nonneg (qDivisor L)]

/-- The actual multiples endpoint tends to zero without a growth assumption. -/
theorem lcm_endpoint_tendsto_zero (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Tendsto (fun M => ‖qMellin (qDivisor (lcmStage M)) s‖) atTop (𝓝 0) := by
  have hlarge : Tendsto (fun M : ℕ => (lcmStage M : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop_mono (fun M => le_trans (by omega : M ≤ M + 2) (lcmStage_ge M))
    exact tendsto_id
  have ht : Tendsto (fun M => ‖qMellinContinuous s hs‖ * (1 / (lcmStage M : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div, mul_zero] using
      (tendsto_inv_atTop_zero.comp hlarge).const_mul ‖qMellinContinuous s hs‖
  apply squeeze_zero (fun M => norm_nonneg _) ?_ ht
  intro M
  have h := (qMellinContinuous s hs).le_opNorm (qDivisor (lcmStage M))
  rw [qDivisor_norm_eq _ (by have := lcmStage_two_le M; omega)] at h
  exact h

/-- A right-half-strip zero forces an eventual positive power floor in the
actual complete leakage. No detector or tail-rate provider is assumed. -/
theorem canonical_leakage_power_floor
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re < 1)
    (hz : riemannZeta s = 0) :
    ∀ᶠ M : ℕ in atTop,
      ((2*s.re-1) / (4 * (escapeFactor s)^2 * zetaTwo * ‖s‖^2)) * ((M + 2 : ℕ) : ℝ)^(2*s.re-1) ≤
        lcmLeakage M := by
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hslt
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hbeta : 0 < 2*s.re-1 := by linarith
  have hevent := (lcm_endpoint_tendsto_zero s hs).eventually
    (gt_mem_nhds (show 0 < 1 / (2 * ‖s‖) by positivity))
  filter_upwards [hevent] with M hsmall
  let L := lcmStage M
  let z : QHilbert := lcmLift M - target L
  have hL : 2 ≤ L := lcmStage_two_le M
  have hzproj : conditionalProjection L z = 0 :=
    canonical_leakage_projection_zero L hL
  have he := canonical_mellin_balance L hL s hs hs1 hz
  have hn : 1 / ‖s‖ ≤ ‖qMellin (qDivisor L) s‖ + ‖qMellin z s‖ := by
    calc
      _ = ‖(1 : ℂ) / s‖ := by rw [norm_div, norm_one]
      _ = ‖qMellin (qDivisor L) s - qMellin z s‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hhalf : 1 / (2 * ‖s‖) ≤ ‖qMellin z s‖ := by
    change ‖qMellin (qDivisor L) s‖ < 1 / (2 * ‖s‖) at hsmall
    have hid : 1 / ‖s‖ = 2 * (1 / (2 * ‖s‖)) := by ring
    rw [hid] at hn
    linarith
  have hlow : 1 / (4 * ‖s‖^2) ≤ ‖qMellin z s‖^2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ 1 / (2 * ‖s‖) by positivity) hhalf 2
    simpa only [div_pow, mul_pow, one_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hbound := mellin_sq_le_sharp_escapeTail s hs hslt.le L (by omega) z hzproj
  have htail : tail (2*s.re) L ≤ ((M + 2 : ℕ) : ℝ)^(1-2*s.re)/(2*s.re-1) :=
    tail_lcmUpto_le _ (by linarith) (M + 2) (by omega)
  have hwhole : 1 / (4 * ‖s‖^2) ≤
      ((escapeFactor s)^2*zetaTwo * (((M + 2 : ℕ) : ℝ)^(1-2*s.re)/(2*s.re-1))) * ‖z‖^2 := by
    exact hlow.trans (hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htail (by positivity)) (sq_nonneg ‖z‖)))
  have hM : (0 : ℝ) < (M + 2 : ℕ) := by positivity
  have hpow : ((M + 2 : ℕ) : ℝ)^(2*s.re-1) *
      ((M + 2 : ℕ) : ℝ)^(1-2*s.re) = 1 := by
    rw [← Real.rpow_add hM]
    rw [show (2*s.re-1)+(1-2*s.re) = 0 by ring, Real.rpow_zero]
  have hp := mul_le_mul_of_nonneg_left hwhole
    (Real.rpow_nonneg (le_of_lt hM) (2*s.re-1))
  have hrearr : ((M + 2 : ℕ) : ℝ)^(2*s.re-1) *
      (((escapeFactor s)^2*zetaTwo * (((M + 2 : ℕ) : ℝ)^(1-2*s.re)/(2*s.re-1))) * ‖z‖^2) =
      ((escapeFactor s)^2*zetaTwo/(2*s.re-1)) * ‖z‖^2 := by
    calc
      _ = ((escapeFactor s)^2*zetaTwo/(2*s.re-1)) * ‖z‖^2 *
          (((M + 2 : ℕ) : ℝ)^(2*s.re-1) * ((M + 2 : ℕ) : ℝ)^(1-2*s.re)) := by ring
      _ = _ := by rw [hpow, mul_one]
  rw [hrearr] at hp
  change ((2*s.re-1) / (4 * (escapeFactor s)^2 * zetaTwo * ‖s‖^2)) *
    ((M + 2 : ℕ) : ℝ)^(2*s.re-1) ≤ ‖z‖^2
  have heq : ((2*s.re-1) / (4 * (escapeFactor s)^2 * zetaTwo * ‖s‖^2)) *
      ((M + 2 : ℕ) : ℝ)^(2*s.re-1) =
      ((2*s.re-1)*((M + 2 : ℕ) : ℝ)^(2*s.re-1))/(4*(escapeFactor s)^2*zetaTwo*‖s‖^2) := by ring
  rw [heq]
  apply (div_le_iff₀ (show 0 < 4 * (escapeFactor s)^2 * zetaTwo * ‖s‖^2 by positivity)).mpr
  have hpdiv : ((M + 2 : ℕ) : ℝ)^(2*s.re-1) / (4*‖s‖^2) ≤
      ((escapeFactor s)^2*zetaTwo*‖z‖^2)/(2*s.re-1) := by
    calc
      _ = ((M + 2 : ℕ) : ℝ)^(2*s.re-1) * (1/(4*‖s‖^2)) := by ring
      _ ≤ ((escapeFactor s)^2*zetaTwo/(2*s.re-1)) * ‖z‖^2 := hp
      _ = _ := by ring
  have hpfirst := (le_div_iff₀ hbeta).mp hpdiv
  have hpsecond : (((M + 2 : ℕ) : ℝ)^(2*s.re-1) * (2*s.re-1))/(4*‖s‖^2) ≤
      (escapeFactor s)^2*zetaTwo*‖z‖^2 := by
    calc
      _ = (((M + 2 : ℕ) : ℝ)^(2*s.re-1)/(4*‖s‖^2)) * (2*s.re-1) := by ring
      _ ≤ _ := hpfirst
  have hpthird := (div_le_iff₀ (show 0 < 4*‖s‖^2 by positivity)).mp hpsecond
  nlinarith


theorem cutoff_tendsto_atTop :
    Tendsto (fun M : ℕ => ((M + 2 : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_mono (f := fun M : ℕ => M) (fun M => by omega)
  exact tendsto_id

/-- The canonical norm need be subpolynomial only cofinally. All analytic
sampler and Euler-tail estimates are discharged for the actual family. -/
theorem riemannHypothesis_of_cofinal_norm_growth
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ M, N ≤ M ∧
      Real.log (1 + ‖lcmLift M‖) / Real.log ((M + 2 : ℕ) : ℝ) < ε) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have ha : 0 < 2*s.re-1 := by linarith
  apply no_positive_power_floor_of_cofinally_small
    (fun M : ℕ => ((M + 2 : ℕ) : ℝ)) (fun M => ‖lcmLift M‖^2)
    1 ((2*s.re-1)/(4*(escapeFactor s)^2*zetaTwo*‖s‖^2)) (2*s.re-1)
    cutoff_tendsto_atTop (fun M => sq_nonneg _) le_rfl (by positivity) ha
    (cofinally_small_square_log_ratio _ _
      (Eventually.of_forall (fun M : ℕ => show (1 : ℝ) < (M + 2 : ℕ) by
        exact_mod_cast (show 1 < M + 2 by omega)))
      (fun M => norm_nonneg _) hsub)
  filter_upwards [canonical_leakage_power_floor s hs hslt hz] with M hM
  exact hM.trans ((lcmLeakage_le_norm_sq M).trans (by linarith))

/-- The zero-liminf criterion uses extended nonnegative values, avoiding the
artificial default real liminf of an unbounded sequence. -/
theorem riemannHypothesis_of_liminf_norm_log_eq_zero
    (hsub : Filter.liminf (fun M => ENNReal.ofReal
      (Real.log (1 + ‖lcmLift M‖) / Real.log ((M + 2 : ℕ) : ℝ))) atTop = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_norm_growth
    (cofinally_small_log_ratio_of_liminf_eq_zero _ _ hsub)

/-- The same checked criterion for the handoff's complete residual norm. -/
theorem riemannHypothesis_of_liminf_residual_log_eq_zero
    (hsub : Filter.liminf (fun M => ENNReal.ofReal
      (Real.log (1 + ‖qOne - lcmLift M‖) / Real.log ((M + 2 : ℕ) : ℝ))) atTop = 0) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have ha : 0 < 2*s.re-1 := by linarith
  apply no_positive_square_power_floor_of_liminf_norm_log_eq_zero
    (fun M : ℕ => ((M + 2 : ℕ) : ℝ)) (fun M => ‖qOne - lcmLift M‖)
    1 ((2*s.re-1)/(4*(escapeFactor s)^2*zetaTwo*‖s‖^2)) (2*s.re-1)
    cutoff_tendsto_atTop (fun M => norm_nonneg _) le_rfl (by positivity) ha hsub
  filter_upwards [canonical_leakage_power_floor s hs hslt hz] with M hM
  have he := canonical_error (lcmStage M) (lcmStage_two_le M)
  change ‖qOne - lcmLift M‖^2 = 1/(lcmStage M : ℝ) ^ 2 + lcmLeakage M at he
  have hp : 0 ≤ 1/(lcmStage M : ℝ) ^ 2 := by positivity
  linarith


/-- A zero at real part beta forces logarithmic norm-growth exponent at
least beta-1/2, with an arbitrary positive epsilon loss. -/
theorem canonical_norm_log_growth_floor
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re < 1)
    (hz : riemannZeta s = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop,
      s.re - 1 / 2 - ε ≤
        Real.log (1 + ‖lcmLift M‖) / Real.log ((M + 2 : ℕ) : ℝ) := by
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have ha : 0 < 2 * s.re - 1 := by linarith
  have h := eventual_norm_log_ratio_floor
    (fun M : ℕ => ((M + 2 : ℕ) : ℝ)) (fun M => ‖lcmLift M‖)
    1 ((2*s.re-1)/(4*(escapeFactor s)^2*zetaTwo*‖s‖^2)) (2*s.re-1) ε
    cutoff_tendsto_atTop (fun M => norm_nonneg _) le_rfl (by positivity) hε
    (by
      filter_upwards [canonical_leakage_power_floor s hs hslt hz] with M hM
      exact hM.trans ((lcmLeakage_le_norm_sq M).trans (by linarith)))
  have he : (2 * s.re - 1) / 2 - ε = s.re - 1 / 2 - ε := by ring
  simpa only [he] using h

/-- Any cofinal upper growth exponent alpha excludes zeros strictly to the
right of Re(s)=1/2+alpha. The upper growth hypothesis remains explicit. -/
theorem zeta_ne_zero_of_cofinal_norm_exponent (α : ℝ) (hα : 0 ≤ α)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ M, N ≤ M ∧
      Real.log (1 + ‖lcmLift M‖) / Real.log ((M + 2 : ℕ) : ℝ) < α + ε)
    (s : ℂ) (hs : (1 / 2 : ℝ) + α < s.re) (hslt : s.re < 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  let ε : ℝ := (s.re - 1 / 2 - α) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlower := canonical_norm_log_growth_floor s (by linarith) hslt hz ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlower
  obtain ⟨M, hM, hsmall⟩ := hupper ε hε N
  have hbig := hN M hM
  dsimp [ε] at hbig hsmall
  linarith


/-- A right-half-strip zero leaves a positive floor in the product of the
complete divisor escape tail and the actual squared canonical norm. -/
theorem eventual_tail_norm_product_floor
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re < 1)
    (hz : riemannZeta s = 0) :
    ∀ᶠ M : ℕ in atTop,
      1 ≤ (4 * (escapeFactor s)^2 * zetaTwo * ‖s‖^2) *
        (tail (2*s.re) (lcmStage M) * ‖lcmLift M‖^2) := by
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hslt
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hevent := (lcm_endpoint_tendsto_zero s hs).eventually
    (gt_mem_nhds (show 0 < 1 / (2 * ‖s‖) by positivity))
  filter_upwards [hevent] with M hsmall
  let L := lcmStage M
  let z : QHilbert := lcmLift M - target L
  have hL : 2 ≤ L := lcmStage_two_le M
  have hzproj : conditionalProjection L z = 0 := canonical_leakage_projection_zero L hL
  have he := canonical_mellin_balance L hL s hs hs1 hz
  have hn : 1 / ‖s‖ ≤ ‖qMellin (qDivisor L) s‖ + ‖qMellin z s‖ := by
    calc
      _ = ‖(1 : ℂ) / s‖ := by rw [norm_div, norm_one]
      _ = ‖qMellin (qDivisor L) s - qMellin z s‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hhalf : 1 / (2 * ‖s‖) ≤ ‖qMellin z s‖ := by
    change ‖qMellin (qDivisor L) s‖ < 1 / (2 * ‖s‖) at hsmall
    have hid : 1 / ‖s‖ = 2 * (1 / (2 * ‖s‖)) := by ring
    rw [hid] at hn
    linarith
  have hlow : 1 / (4 * ‖s‖^2) ≤ ‖qMellin z s‖^2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ 1 / (2 * ‖s‖) by positivity) hhalf 2
    simpa only [div_pow, mul_pow, one_pow, show (2 : ℝ)^2 = 4 by norm_num] using h
  have hbound := mellin_sq_le_sharp_escapeTail s hs hslt.le L (by omega) z hzproj
  have hzle : ‖z‖^2 ≤ ‖lcmLift M‖^2 := lcmLeakage_le_norm_sq M
  have hwhole : 1 / (4 * ‖s‖^2) ≤
      ((escapeFactor s)^2 * zetaTwo * tail (2*s.re) L) * ‖lcmLift M‖^2 :=
    hlow.trans (hbound.trans (mul_le_mul_of_nonneg_left hzle
      (by have hD := tail_nonneg (2*s.re) L; positivity)))
  have hh := (div_le_iff₀ (show 0 < 4 * ‖s‖^2 by positivity)).mp hwhole
  calc
    _ ≤ (((escapeFactor s)^2 * zetaTwo * tail (2*s.re) L) * ‖lcmLift M‖^2) *
        (4 * ‖s‖^2) := hh
    _ = _ := by ring

/-- A cofinal norm bound at the critical power excludes the zero itself.
This is stronger than the zero-free conclusion from a logarithmic exponent
alone, which only excludes strictly larger real parts. -/
theorem zeta_ne_zero_of_cofinal_critical_power_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re < 1)
    (C : ℝ)
    (hbound : ∀ N : ℕ, ∃ M, N ≤ M ∧
      ‖lcmLift M‖ ≤ C * ((M + 2 : ℕ) : ℝ)^(s.re - 1 / 2)) :
    riemannZeta s ≠ 0 := by
  intro hz
  let K : ℝ := (∑' n : ℕ, (n : ℝ)^(-(2*s.re))) * (Real.log 4 + 1) *
    (1 + 2 / (1 - (2 : ℝ)^(1-2*s.re)))
  let B : ℝ := 4 * (escapeFactor s)^2 * zetaTwo * ‖s‖^2
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hq : (2 : ℝ)^(1-2*s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK : 0 < K := by
    have hseries := power_series_pos (2*s.re) (by linarith)
    dsimp [K]
    positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun M : ℕ => Real.log ((M + 2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp cutoff_tendsto_atTop
  have hsmall := (hlog.const_div_atTop (B*K*C^2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventual_tail_norm_product_floor s hs hslt hz)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (eventually_tail_lcmUpto_le_log (2*s.re) (by linarith) 1 (by norm_num))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hsmall
  obtain ⟨M, hM, hnorm⟩ := hbound (max N₁ (max N₂ N₃))
  have hfloor := hN₁ M (le_trans (le_max_left _ _) hM)
  have htail := hN₂ (M + 2) (by omega)
  have hbudget := hN₃ M (by omega)
  let x : ℝ := ((M + 2 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 < x := by dsimp [x]; exact_mod_cast (show 1 < M+2 by omega)
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hD : 0 ≤ tail (2*s.re) (lcmStage M) := tail_nonneg _ _
  change tail (2*s.re) (lcmStage M) ≤ K * x^(1-2*s.re) / Real.log x at htail
  change ‖lcmLift M‖ ≤ C*x^(s.re-1/2) at hnorm
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hupper := mul_le_mul htail hn2 (sq_nonneg ‖lcmLift M‖)
    (show 0 ≤ K*x^(1-2*s.re)/Real.log x by positivity)
  have hupperB := mul_le_mul_of_nonneg_left hupper hB.le
  have hpow : x^(1-2*s.re) * (x^(s.re-1/2))^2 = 1 := by
    rw [pow_two, ← Real.rpow_add hx, ← Real.rpow_add hx]
    rw [show (1-2*s.re)+((s.re-1/2)+(s.re-1/2)) = 0 by ring, Real.rpow_zero]
  have he : B * ((K*x^(1-2*s.re)/Real.log x) * (C*x^(s.re-1/2))^2) =
      B*K*C^2/Real.log x := by
    calc
      _ = (B*K*C^2/Real.log x) * (x^(1-2*s.re) * (x^(s.re-1/2))^2) := by ring
      _ = _ := by rw [hpow, mul_one]
  rw [he] at hupperB
  change 1 ≤ B * (tail (2*s.re) (lcmStage M) * ‖lcmLift M‖^2) at hfloor
  change B*K*C^2/Real.log x < 1 at hbudget
  exact (not_lt_of_ge (hfloor.trans hupperB)) hbudget


/-- A zero forces the extra square-root logarithmic factor in the actual
canonical norm: its squared norm has a positive log-enhanced power floor. -/
theorem canonical_norm_sq_log_power_floor
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hslt : s.re < 1)
    (hz : riemannZeta s = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      c * ((M + 2 : ℕ) : ℝ)^(2*s.re-1) * Real.log ((M + 2 : ℕ) : ℝ) ≤
        ‖lcmLift M‖^2 := by
  let K : ℝ := (∑' n : ℕ, (n : ℝ)^(-(2*s.re))) * (Real.log 4 + 1) *
    (1 + 2 / (1 - (2 : ℝ)^(1-2*s.re)))
  let B : ℝ := 4 * (escapeFactor s)^2 * zetaTwo * ‖s‖^2
  have hZ := zetaTwo_pos
  have hA := escapeFactor_pos s
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hq : (2 : ℝ)^(1-2*s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK : 0 < K := by
    have hseries := power_series_pos (2*s.re) (by linarith)
    dsimp [K]
    positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_tail_lcmUpto_le_log (2*s.re) (by linarith) 1 (by norm_num))
  refine ⟨1/(B*K), by positivity, ?_⟩
  filter_upwards [eventual_tail_norm_product_floor s hs hslt hz,
    eventually_ge_atTop N] with M hfloor hNM
  have htail := hN (M+2) (by omega)
  let x : ℝ := ((M+2 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 < x := by dsimp [x]; exact_mod_cast (show 1 < M+2 by omega)
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  change tail (2*s.re) (lcmStage M) ≤ K*x^(1-2*s.re)/Real.log x at htail
  change 1 ≤ B * (tail (2*s.re) (lcmStage M) * ‖lcmLift M‖^2) at hfloor
  have hupper : 1 ≤ B * ((K*x^(1-2*s.re)/Real.log x) * ‖lcmLift M‖^2) :=
    hfloor.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right htail (sq_nonneg _)) hB.le)
  have hmult := mul_le_mul_of_nonneg_left hupper
    (show 0 ≤ x^(2*s.re-1)*Real.log x by positivity)
  have hpow : x^(2*s.re-1)*x^(1-2*s.re) = 1 := by
    rw [← Real.rpow_add hx, show (2*s.re-1)+(1-2*s.re) = 0 by ring, Real.rpow_zero]
  have he : (x^(2*s.re-1)*Real.log x) *
      (B * ((K*x^(1-2*s.re)/Real.log x) * ‖lcmLift M‖^2)) =
      B*K*‖lcmLift M‖^2 := by
    calc
      _ = B*K*‖lcmLift M‖^2 * (x^(2*s.re-1)*x^(1-2*s.re)) *
          (Real.log x / Real.log x) := by ring
      _ = _ := by rw [hpow, div_self (ne_of_gt hlogx)]; ring
  rw [mul_one, he] at hmult
  change (1/(B*K))*x^(2*s.re-1)*Real.log x ≤ ‖lcmLift M‖^2
  calc
    _ = (x^(2*s.re-1)*Real.log x)/(B*K) := by ring
    _ ≤ _ := (div_le_iff₀ (mul_pos hB hK)).mpr (by nlinarith [hmult])

end RiemannResearch.RH.QCRTZeroGrowth
