/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.Analysis.NonnegativeDeficit
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Cofinal logarithmic growth excludes an eventual positive power floor

Source: the user's CRT collocation and zero-growth handoff, 6 November 2026,
Section 7. The extended nonnegative liminf prevents unbounded real sequences
from receiving the default finite real liminf. No arithmetic growth estimate
is asserted: this module supplies only the exact analytic contradiction.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
namespace RiemannResearch.Analysis.CofinalLogGrowth
open SubpolynomialWindow NonnegativeDeficit

/-- An eventual positive power floor forces a positive logarithmic floor.
Only the constant-error term is discarded asymptotically. -/
theorem eventual_log_ratio_floor (x E : ℕ → ℝ) (K c a : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ E n + K) :
    ∀ᶠ n in atTop, a/2 ≤ Real.log (1 + E n) / Real.log (x n) := by
  have hlog : Tendsto (fun n => Real.log (x n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hconst : Tendsto
      (fun n => (Real.log K - Real.log c) / Real.log (x n))
      atTop (𝓝 0) := hlog.const_div_atTop _
  have hsmall := hconst.eventually (gt_mem_nhds (by linarith : 0 < a/2))
  have hx1 : ∀ᶠ n in atTop, 1 < x n := hx.eventually (eventually_gt_atTop 1)
  filter_upwards [hx1, hfloor, hsmall] with n hn hfn hcn
  have h := exponent_le_log_ratio (x n) (E n) K c a hn (hE n) hK hc hfn
  have he : (Real.log (1 + E n) + Real.log K - Real.log c) / Real.log (x n) =
      Real.log (1 + E n) / Real.log (x n) +
        (Real.log K - Real.log c) / Real.log (x n) := by ring
  rw [he] at h
  linarith

/-- Zero logarithmic growth is required only cofinally, not as a full limit. -/
theorem no_positive_power_floor_of_cofinally_small (x E : ℕ → ℝ) (K c a : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      Real.log (1 + E n) / Real.log (x n) < ε)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ E n + K) : False := by
  have h := eventual_log_ratio_floor x E K c a hx hE hK hc ha hfloor
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨n, hn, hsmall⟩ := hsub (a/2) (by linarith) N
  exact (not_lt_of_ge (hN n hn)) hsmall

/-- The positive power floor yields a genuinely positive extended liminf. -/
theorem log_liminf_pos_of_power_floor (x E : ℕ → ℝ) (K c a : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ E n + K) :
    0 < Filter.liminf
      (fun n => ENNReal.ofReal (Real.log (1 + E n) / Real.log (x n))) atTop := by
  apply liminf_pos_of_eventual_floor
    (c := ENNReal.ofReal (a/2)) (ENNReal.ofReal_pos.mpr (by linarith))
  filter_upwards [eventual_log_ratio_floor x E K c a hx hE hK hc ha hfloor]
    with n hn
  exact ENNReal.ofReal_le_ofReal hn

/-- The handoff's cofinal subpolynomial criterion in extended-liminf form.
The constant K and the coefficient c remain explicit. -/
theorem no_positive_power_floor_of_liminf_eq_zero (x E : ℕ → ℝ) (K c a : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hsub : Filter.liminf
      (fun n => ENNReal.ofReal (Real.log (1 + E n) / Real.log (x n))) atTop = 0)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ E n + K) : False := by
  have h := log_liminf_pos_of_power_floor x E K c a hx hE hK hc ha hfloor
  rw [hsub] at h
  exact (lt_irrefl _) h


/-- Squaring a nonnegative quantity costs at most a factor two in relative
logarithmic growth. -/
theorem square_log_ratio_le_two (x F : ℝ) (hx : 1 < x) (hF : 0 ≤ F) :
    Real.log (1 + F^2) / Real.log x ≤
      2 * (Real.log (1 + F) / Real.log x) := by
  have hineq : 1 + F^2 ≤ (1 + F) ^ 2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + F^2) hineq
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hratio := mul_le_mul_of_nonneg_right hlog
    (inv_nonneg.mpr (Real.log_pos hx).le)
  calc
    _ ≤ (2 * Real.log (1 + F)) / Real.log x := by
      simpa only [div_eq_mul_inv] using hratio
    _ = _ := by ring

/-- The cofinal logarithmic condition is preserved when a norm is squared.
The denominator need only be eventually positive. -/
theorem cofinally_small_square_log_ratio (x F : ℕ → ℝ)
    (hx : ∀ᶠ n in atTop, 1 < x n) (hF : ∀ n, 0 ≤ F n)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      Real.log (1 + F n) / Real.log (x n) < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      Real.log (1 + (F n) ^ 2) / Real.log (x n) < ε := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hx
  intro ε hε N
  obtain ⟨n, hn, hsmall⟩ := hsub (ε/2) (by linarith) (max N N₀)
  refine ⟨n, (le_max_left N N₀).trans hn, ?_⟩
  have hn₀ : N₀ ≤ n := (le_max_right N N₀).trans hn
  have hbound := square_log_ratio_le_two (x n) (F n) (hN₀ n hn₀) (hF n)
  linarith

/-- An extended zero liminf implies the unambiguous cofinal real criterion. -/
theorem cofinally_small_log_ratio_of_liminf_eq_zero (x F : ℕ → ℝ)
    (hsub : Filter.liminf
      (fun n => ENNReal.ofReal (Real.log (1 + F n) / Real.log (x n))) atTop = 0) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧
      Real.log (1 + F n) / Real.log (x n) < ε := by
  have hcofinal := (liminf_eq_zero_iff_cofinallySmall
    (fun n => ENNReal.ofReal (Real.log (1 + F n) / Real.log (x n)))).mp hsub
  intro ε hε N
  obtain ⟨n, hn, hsmall⟩ := hcofinal (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) N
  refine ⟨n, hn, ?_⟩
  by_contra h
  have hle := ENNReal.ofReal_le_ofReal (le_of_not_gt h)
  exact (not_lt_of_ge hle) hsmall

/-- The user's norm criterion rules out a positive-power floor on its squared
energy, even if small relative logarithmic growth occurs only cofinally. -/
theorem no_positive_square_power_floor_of_liminf_norm_log_eq_zero
    (x F : ℕ → ℝ) (K c a : ℝ) (hx : Tendsto x atTop atTop)
    (hF : ∀ n, 0 ≤ F n) (hK : 1 ≤ K) (hc : 0 < c) (ha : 0 < a)
    (hsub : Filter.liminf
      (fun n => ENNReal.ofReal (Real.log (1 + F n) / Real.log (x n))) atTop = 0)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ (F n) ^ 2 + K) : False := by
  exact no_positive_power_floor_of_cofinally_small x (fun n => (F n) ^ 2)
    K c a hx (fun n => sq_nonneg _) hK hc ha
    (cofinally_small_square_log_ratio x F
      (hx.eventually (eventually_gt_atTop 1)) hF
      (cofinally_small_log_ratio_of_liminf_eq_zero x F hsub)) hfloor


/-- Every exponent strictly below a positive power floor is an eventual
logarithmic lower bound; no fixed loss in the exponent is necessary. -/
theorem eventual_log_ratio_floor_below (x E : ℕ → ℝ) (K c a b : ℝ)
    (hx : Tendsto x atTop atTop)
    (hE : ∀ n, 0 ≤ E n) (hK : 1 ≤ K) (hc : 0 < c) (hba : b < a)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ E n + K) :
    ∀ᶠ n in atTop, b ≤ Real.log (1 + E n) / Real.log (x n) := by
  have hlog : Tendsto (fun n => Real.log (x n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hconst : Tendsto
      (fun n => (Real.log K - Real.log c) / Real.log (x n))
      atTop (𝓝 0) := hlog.const_div_atTop _
  have hsmall := hconst.eventually (gt_mem_nhds (sub_pos.mpr hba))
  have hx1 : ∀ᶠ n in atTop, 1 < x n := hx.eventually (eventually_gt_atTop 1)
  filter_upwards [hx1, hfloor, hsmall] with n hn hfn hcn
  have h := exponent_le_log_ratio (x n) (E n) K c a hn (hE n) hK hc hfn
  have he : (Real.log (1 + E n) + Real.log K - Real.log c) / Real.log (x n) =
      Real.log (1 + E n) / Real.log (x n) +
        (Real.log K - Real.log c) / Real.log (x n) := by ring
  rw [he] at h
  linarith

/-- Squared-energy power floors give the sharp norm-growth exponent,
with an arbitrary positive epsilon loss. -/
theorem eventual_norm_log_ratio_floor (x F : ℕ → ℝ) (K c a ε : ℝ)
    (hx : Tendsto x atTop atTop)
    (hF : ∀ n, 0 ≤ F n) (hK : 1 ≤ K) (hc : 0 < c) (hε : 0 < ε)
    (hfloor : ∀ᶠ n in atTop, c * (x n) ^ a ≤ (F n) ^ 2 + K) :
    ∀ᶠ n in atTop, a / 2 - ε ≤ Real.log (1 + F n) / Real.log (x n) := by
  have h := eventual_log_ratio_floor_below x (fun n => (F n) ^ 2)
    K c a (a - 2 * ε) hx (fun n => sq_nonneg _) hK hc (by linarith) hfloor
  filter_upwards [h, hx.eventually (eventually_gt_atTop 1)] with n hn hxn
  have hsq := square_log_ratio_le_two (x n) (F n) hxn (hF n)
  linarith

end RiemannResearch.Analysis.CofinalLogGrowth
