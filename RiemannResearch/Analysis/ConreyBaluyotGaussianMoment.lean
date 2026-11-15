/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GaussianWindow
import RiemannResearch.Analysis.ConreyBaluyotMomentEndpoints
import RiemannResearch.RH.WeilExplicitFormula.RvM.ZetaGrowth
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual mollified Gaussian moments and explicit central-moment excess

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Section 3.3, equations (3.3.1)--(3.3.5), pp. 115--116:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the smoothed moment and the analytic strategy, not a
novelty claim. The user-provided finite-moment handoff identifies this step.

All coefficients and the exact floor cutoff are those of the actual finite
mollifier. Integrability is proved for every real sigma, y and epsilon on
any line l >= 1/4 avoiding l = 1. Its polynomial majorant is nonuniform
and is used only to justify the Gaussian integral, never as a small moment
provider. Exact window and source-tail identities precede the estimates.

The central-moment estimate is a conditional research reduction. The
substantive premise is a bound on the actual whole-line Gaussian moment
throughout the padded center interval. No arithmetic or RH hypothesis is
discharged by proving this transfer. For nonnegative r, the explicit excess
can be passed directly to the established prescribed-line counting theorem.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

theorem continuous_mollifiedZeta_vertical_of_ne_one (σ y ε : ℝ) {l : ℝ}
    (hl : l ≠ 1) :
    Continuous (fun t : ℝ => mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : (l : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro he
    apply hl
    have hr := congrArg Complex.re he
    simpa using hr
  exact ContinuousAt.comp (g := mollifiedZeta σ y ε)
    (f := fun t : ℝ => (l : ℂ) + (t : ℂ) * I)
    (analyticAt_mollifiedZeta σ y ε hs).continuousAt (by fun_prop)

/-- Every literal finite mollifier has a vertical bound, with no normalization hypothesis. -/
theorem nonstandardMollifier_vertical_norm_le (σ y ε : ℝ) {l : ℝ}
    (hl : 0 ≤ l) (t : ℝ) :
    ‖nonstandardMollifier σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ≤
      ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊, ‖mollifierCoefficient σ y n‖ := by
  unfold nonstandardMollifier
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := by omega
  have hp : 1 ≤ ‖(n : ℂ) ^ ((l : ℂ) + (t : ℂ) * I)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    apply Real.one_le_rpow (by exact_mod_cast hn1)
    simpa using hl
  rw [norm_div]
  exact div_le_self (norm_nonneg _) hp

/-- A nonuniform polynomial majorant suffices for Gaussian integrability.
The parameters and the exact cutoff are arbitrary; the line avoids the pole. -/
theorem exists_mollifiedZeta_vertical_quadratic_bound (σ y ε : ℝ) {l : ℝ}
    (hl : 1 / 4 ≤ l) (hl1 : l ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2‖ ≤ C * (1 + t ^ 2) := by
  let F : ℝ → ℂ := fun t => mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)
  have hc : Continuous F := continuous_mollifiedZeta_vertical_of_ne_one σ y ε hl1
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hc.continuousOn
  let B : ℝ := ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊, ‖mollifierCoefficient σ y n‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => norm_nonneg _)
  let K := (13 / 2 : ℝ) * B
  have hK : 0 ≤ K := mul_nonneg (by norm_num) hB
  have hg : ∀ t : ℝ, 1 ≤ |t| → ‖F t‖ ≤ K * |t| := by
    intro t ht
    have hz : ‖riemannZeta ((l : ℂ) + (t : ℂ) * I)‖ ≤ 13 / 2 * |t| := by
      have hz' := Zeta23.RvM.riemannZeta_linear_growth
        (δ := (1 / 4 : ℝ)) (by norm_num)
        (s := (l : ℂ) + (t : ℂ) * I) (by simpa using hl) (by simpa using ht)
      norm_num at hz' ⊢
      exact hz'
    have hm := nonstandardMollifier_vertical_norm_le σ y ε (by linarith : 0 ≤ l) t
    change ‖riemannZeta _ * nonstandardMollifier σ y ε _‖ ≤ K * |t|
    rw [norm_mul]
    calc
      _ ≤ (13 / 2 * |t|) * B := mul_le_mul hz hm (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [K]; ring
  refine ⟨D ^ 2 + K ^ 2, by positivity, ?_⟩
  intro t
  change ‖‖F t‖ ^ 2‖ ≤ (D ^ 2 + K ^ 2) * (1 + t ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases ht : |t| ≤ 1
  · have hbound := hD t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hs : ‖F t‖ ^ 2 ≤ D ^ 2 := by nlinarith [norm_nonneg (F t)]
    nlinarith [sq_nonneg K, mul_nonneg (sq_nonneg D) (sq_nonneg t),
      mul_nonneg (sq_nonneg K) (sq_nonneg t)]
  · have hbound := hg t (le_of_not_ge ht)
    have hs : ‖F t‖ ^ 2 ≤ K ^ 2 * t ^ 2 := by
      have hs' := mul_self_le_mul_self (norm_nonneg (F t)) hbound
      nlinarith [sq_abs t]
    nlinarith [sq_nonneg D, sq_nonneg K, mul_nonneg (sq_nonneg D) (sq_nonneg t)]

def mollifiedGaussianMoment (σ y ε l Δ u : ℝ) : ℝ :=
  Real.gaussianMoment (1 / Δ ^ 2)
    (fun t => ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2) u

/-- Actual whole-line Gaussian integrability, including low heights, is proved. -/
theorem integrable_mollifiedGaussianMoment (σ y ε : ℝ) {l Δ : ℝ}
    (hl : 1 / 4 ≤ l) (hl1 : l ≠ 1) (hΔ : 0 < Δ) (u : ℝ) :
    Integrable (fun t : ℝ => Real.gaussianDensity (1 / Δ ^ 2) (t - u) *
      ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_mollifiedZeta_vertical_quadratic_bound σ y ε hl hl1
  exact Real.integrable_gaussianDensity_mul (by positivity) hC
    ((continuous_mollifiedZeta_vertical_of_ne_one σ y ε hl1).norm.pow 2) hb u

/-- Exact comparison with the source's scale-normalized whole-line integral. -/
theorem mollifiedGaussianMoment_eq_integral (σ y ε l : ℝ) {Δ : ℝ}
    (hΔ : 0 < Δ) (u : ℝ) :
    mollifiedGaussianMoment σ y ε l Δ u = (1 / (Δ * Real.sqrt Real.pi)) *
      ∫ t : ℝ, Real.exp (-((t - u) / Δ) ^ 2) *
        ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  unfold mollifiedGaussianMoment Real.gaussianMoment
  simp_rw [Real.gaussianDensity_inv_sq hΔ]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

/-- Explicit loss in the central uncentered moment; it is nonnegative for r ≥ 0. -/
def gaussianMomentExcess (T H r δ : ℝ) : ℝ :=
  (2 * H + (T + 2 * H) * r + δ * T) / (1 - δ)

theorem gaussianMomentExcess_nonneg {T H r δ : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    0 ≤ gaussianMomentExcess T H r δ := by
  unfold gaussianMomentExcess
  exact div_nonneg (by positivity) (by linarith)

theorem gaussianMomentExcess_identity {T H r δ : ℝ} (hδ : δ < 1) :
    ((T + 2 * H) * (1 + r)) / (1 - δ) = T + gaussianMomentExcess T H r δ := by
  unfold gaussianMomentExcess
  field_simp [ne_of_gt (show 0 < 1 - δ by linarith)]
  ring

/-- The exact central smoothing identity keeps its missing Gaussian mass. -/
theorem mollifiedSecondMoment_gaussian_identity (σ y ε l Δ H : ℝ) {T : ℝ}
    (hT : 0 < T) :
    mollifiedSecondMoment σ y ε l T (2 * T) =
      (∫ u in (T - H)..(2 * T + H), Real.truncatedGaussianMoment (1 / Δ ^ 2)
        (fun t => ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2) T (2 * T) u) +
      ∫ t in T..2 * T, (1 - Real.gaussianWindow (1 / Δ ^ 2) (T - H) (2 * T + H) t) *
        ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  exact Real.gaussianWindow_moment_identity _ _ _ _ _ _
    ((continuousOn_mollifiedZeta_vertical σ y ε l hT (by linarith)).norm.pow 2)

/-- The full Gaussian moment keeps the complete source tail outside the dyadic interval. -/
theorem mollifiedGaussianMoment_source_tail_identity (σ y ε : ℝ) {l Δ T : ℝ}
    (hl : 1 / 4 ≤ l) (hl1 : l ≠ 1) (hΔ : 0 < Δ) (hT : 0 ≤ T) (u : ℝ) :
    mollifiedGaussianMoment σ y ε l Δ u =
      Real.truncatedGaussianMoment (1 / Δ ^ 2)
        (fun t => ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2) T (2 * T) u +
      ∫ t in (Ioc T (2 * T))ᶜ, Real.gaussianDensity (1 / Δ ^ 2) (t - u) *
        ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  exact Real.gaussianMoment_eq_truncated_add (by linarith)
    (integrable_mollifiedGaussianMoment σ y ε hl hl1 hΔ u)

/-- Conditional research reduction. A bound for the actual whole-line smoothed
moment supplies the precise central moment required by the dyadic count theorem. -/
theorem mollifiedSecondMoment_le_of_gaussianMoment (σ y ε : ℝ) {l T Δ H r : ℝ}
    (hl : 1 / 4 ≤ l) (hl1 : l ≠ 1) (hT : 0 ≤ T) (hΔ : 0 < Δ) (hH : 0 ≤ H)
    (hsmall : Real.sqrt 2 * Real.exp (-(H / Δ) ^ 2 / 2) < 1)
    (hm : ∀ u ∈ Icc (T - H) (2 * T + H), mollifiedGaussianMoment σ y ε l Δ u ≤ 1 + r) :
    mollifiedSecondMoment σ y ε l T (2 * T) ≤
      T + gaussianMomentExcess T H r (Real.sqrt 2 * Real.exp (-(H / Δ) ^ 2 / 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_mollifiedZeta_vertical_quadratic_bound σ y ε hl hl1
  have hexp : -(1 / Δ ^ 2) * H ^ 2 / 2 = -(H / Δ) ^ 2 / 2 := by field_simp
  have hi := Real.integral_le_of_gaussianMoment (a := 1 / Δ ^ 2) (H := H) (u := T) (v := 2 * T)
    (by positivity) hH (by linarith) hC
    ((continuous_mollifiedZeta_vertical_of_ne_one σ y ε hl1).norm.pow 2)
    (fun t => sq_nonneg _) hb (by simpa only [hexp] using hsmall) hm
  rw [hexp] at hi
  have he : ((2 * T - T + 2 * H) * (1 + r)) / (1 - Real.sqrt 2 * Real.exp (-(H / Δ) ^ 2 / 2)) =
      T + gaussianMomentExcess T H r (Real.sqrt 2 * Real.exp (-(H / Δ) ^ 2 / 2)) := by
    rw [show 2 * T - T + 2 * H = T + 2 * H by ring]
    exact gaussianMomentExcess_identity hsmall
  exact hi.trans_eq he

/-- Baluyot's logarithmic padding has a scale-independent Gaussian loss.
No separate small-loss hypothesis is needed once `log T ≥ 2`. -/
theorem mollifiedSecondMoment_le_of_log_padded_gaussianMoment (σ y ε : ℝ)
    {l T Δ r : ℝ} (hl : 1 / 4 ≤ l) (hl1 : l ≠ 1) (hT : 0 < T)
    (hΔ : 0 < Δ) (hlog : 2 ≤ Real.log T)
    (hm : ∀ u ∈ Icc (T - Δ * Real.log T) (2 * T + Δ * Real.log T),
      mollifiedGaussianMoment σ y ε l Δ u ≤ 1 + r) :
    mollifiedSecondMoment σ y ε l T (2 * T) ≤
      T + gaussianMomentExcess T (Δ * Real.log T) r
        (Real.sqrt 2 * Real.exp (-(Real.log T) ^ 2 / 2)) := by
  have hsmall : Real.sqrt 2 * Real.exp (-(Real.log T) ^ 2 / 2) < 1 := by
    simpa using Real.gaussian_loss_lt_one (a := 1) (H := Real.log T) (by nlinarith)
  have hquot : (Δ * Real.log T) / Δ = Real.log T := by field_simp
  simpa only [hquot] using mollifiedSecondMoment_le_of_gaussianMoment σ y ε
    hl hl1 hT.le hΔ (mul_nonneg hΔ.le (by linarith))
    (by simpa only [hquot] using hsmall) hm

end RiemannResearch.Analysis.ConreyBaluyot
