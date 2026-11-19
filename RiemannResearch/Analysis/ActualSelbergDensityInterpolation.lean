/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamLittlewoodDensity
import RiemannResearch.Analysis.ActualSelbergDensityConventions
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform zero density at the limiting slope with a logarithmic loss

Baluyot, *On the Zeros of Riemann's Zeta-function* (2017), Theorem 1.2.1,
gives the single-logarithm estimate at each fixed slope below 8 / 7.
<https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320>

The Gabriel–Littlewood estimate in Chourasiya and Simonič,
<https://arxiv.org/abs/2507.15184>, is already available for the inclusive
count. Its exponent lies below the tangent of slope 4 / 3. Interpolation gives
the limiting slope 8 / 7 with any fixed positive logarithmic loss. Constants
and height thresholds may depend on the loss.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Power form of the existing exponential-tail interface. -/
theorem uniformLogLossDensity_iff_power (a k : ℝ) :
    UniformLogLossDensity a k ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
        rightInclusiveCount T σ ≤ C * (T ^ (1 - a * (σ - 1 / 2)) * Real.log T ^ k) := by
  have eqn (C T σ : ℝ) (hT : 1 < T) :
      C * (T ^ (1 - a * (σ - 1 / 2)) * Real.log T ^ k) =
      C * T * Real.log T ^ k * Real.exp (-(a * Real.log T) * (σ - 1 / 2)) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hT),
      show Real.log T * (1 - a * (σ - 1 / 2)) =
        Real.log T + (-(a * Real.log T) * (σ - 1 / 2)) by ring,
      Real.exp_add, Real.exp_log (zero_lt_one.trans hT)]
    ring
  constructor
  · rintro ⟨C, H, hC, hH, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [eventually_ge_atTop H] with T hT σ hσ
    rw [eqn C T σ (hH.trans_le hT)]
    exact h T hT σ hσ
  · rintro ⟨C, hC, h⟩
    obtain ⟨H, hh⟩ := eventually_atTop.1 h
    refine ⟨C, max H 2, hC, (by linarith only [le_max_right H (2 : ℝ)]), ?_⟩
    intro T hT σ hσ
    rw [← eqn C T σ (by linarith only [hT, le_max_right H (2 : ℝ)])]
    exact hh T ((le_max_left _ _).trans hT) σ hσ

private theorem density_profile_exp {T : ℝ} (hT : 1 < T) (b k : ℝ) :
    T ^ b * Real.log T ^ k =
      Real.exp (Real.log T * b + Real.log (Real.log T) * k) := by
  rw [Real.exp_add, Real.rpow_def_of_pos (zero_lt_one.trans hT),
    Real.rpow_def_of_pos (Real.log_pos hT)]

/-- The tangent has two surplus logarithms, using the repository's proved
Gabriel–Littlewood estimate uniformly on the closed half-strip. -/
theorem ingham_tangent_density_log_loss : UniformLogLossDensity (4 / 3) 3 := by
  rw [uniformLogLossDensity_iff_power]
  obtain ⟨C, hC, hc⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨C, hC.le, ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1))] with T hT
  intro σ hσ
  have ht2 : 2 ≤ T := (le_max_left _ _).trans hT
  have ht : 1 < T := by linarith
  have hL : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  let q := 3 * (1 - σ) / (2 - σ)
  have den : 0 < 2 - σ := by linarith [hσ.2]
  have hq : q ≤ 1 := (div_le_iff₀ den).mpr (by linarith [hσ.1])
  have htan : q ≤ 1 - 4 / 3 * (σ - 1 / 2) := by
    apply (div_le_iff₀ den).mpr
    nlinarith [sq_nonneg (σ - 1 / 2)]
  apply (hc T ht2 σ hσ).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  refine (min_le_right _ _).trans ?_
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le ht.le htan)
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hq] : 2 + q ≤ 3))
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (Real.rpow_nonneg (by linarith) _)

/-- Geometric interpolation preserves uniformity in height and real part. -/
theorem UniformLogLossDensity.interpolate {a b m n : ℝ}
    (ha : UniformLogLossDensity a m) (hb : UniformLogLossDensity b n)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    UniformLogLossDensity ((1 - r) * a + r * b) ((1 - r) * m + r * n) := by
  rw [uniformLogLossDensity_iff_power] at ha hb ⊢
  obtain ⟨A, hA, hAt⟩ := ha
  obtain ⟨B, hB, hBt⟩ := hb
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  filter_upwards [hAt, hBt, eventually_gt_atTop (1 : ℝ)] with T hat hbt ht
  intro σ hσ
  specialize hat σ hσ
  specialize hbt σ hσ
  rw [density_profile_exp ht] at hat hbt ⊢
  let u := Real.log T * (1 - a * (σ - 1 / 2)) + Real.log (Real.log T) * m
  let v := Real.log T * (1 - b * (σ - 1 / 2)) + Real.log (Real.log T) * n
  have hid : Real.log T * (1 - ((1 - r) * a + r * b) * (σ - 1 / 2)) +
      Real.log (Real.log T) * ((1 - r) * m + r * n) = (1 - r) * u + r * v := by
    dsimp [u, v]
    ring
  rw [hid]
  rcases le_total u v with huv | hvu
  · have hc : u ≤ (1 - r) * u + r * v := by
      nlinarith only [mul_nonneg hr.1 (sub_nonneg.mpr huv)]
    exact hat.trans (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr hc)
      (Real.exp_pos u).le (hA.trans (le_max_left _ _)))
  · have hc : v ≤ (1 - r) * u + r * v := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hvu)]
    exact hbt.trans (mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr hc)
      (Real.exp_pos v).le (hA.trans (le_max_left _ _)))

theorem UniformLogLossDensity.weaken {a b k j : ℝ}
    (h : UniformLogLossDensity a k) (hab : b ≤ a) (hkj : k ≤ j) :
    UniformLogLossDensity b j := by
  rw [uniformLogLossDensity_iff_power] at h ⊢
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop (max 2 (Real.exp 1))] with T ht hT σ hσ
  have h1 : 1 ≤ T := by linarith only [hT, le_max_left (2 : ℝ) (Real.exp 1)]
  have hL : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  apply (ht σ hσ).trans
  apply mul_le_mul_of_nonneg_left _ hC
  have hx := sub_le_sub_left (mul_le_mul_of_nonneg_right hab (sub_nonneg.mpr hσ.1)) 1
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le h1 hx)
    (Real.rpow_le_rpow_of_exponent_le hL hkj)
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (Real.rpow_nonneg (zero_le_one.trans h1) _)

/-- Every slope strictly below the interpolated edge is available with two
times the mixing parameter as log loss. -/
theorem ConreyBaluyotDensityHypothesis.interpolated_profile
    (h : ConreyBaluyotDensityHypothesis) {b r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hb : b < (1 - r) * (8 / 7) + r * (4 / 3)) : UniformLogLossDensity b (1 + 2 * r) := by
  have hdiv : (b - r * (4 / 3)) / (1 - r) < 8 / 7 :=
    (div_lt_iff₀ (by linarith)).mpr (by linarith)
  obtain ⟨a, ha, ha'⟩ := exists_between
    (show max 0 ((b - r * (4 / 3)) / (1 - r)) < 8 / 7 from max_lt (by norm_num) hdiv)
  have ha0 := (le_max_left _ _).trans_lt ha
  have hlow := (div_lt_iff₀ (show 0 < 1 - r by linarith)).mp ((le_max_right _ _).trans_lt ha)
  have H := (uniformLogLossDensity_of_uniformSelberg a (h a ha0 ha')).interpolate ingham_tangent_density_log_loss
    (show r ∈ Icc (0 : ℝ) 1 from ⟨hr0.le, hr1.le⟩)
  exact H.weaken (by nlinarith only [hlow]) (by linarith)

/-- Exact slope 8 / 7 with any fixed positive extra log power. -/
theorem ConreyBaluyotDensityHypothesis.endpoint_log_loss
    (h : ConreyBaluyotDensityHypothesis) {ε : ℝ} (hε : 0 < ε) :
    UniformLogLossDensity (8 / 7) (1 + ε) := by
  let r := min (ε / 2) (1 / 2)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr' : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have H := h.interpolated_profile (b := 8 / 7) hr hr' (by linarith)
  exact H.weaken le_rfl (by dsimp [r]; linarith only [min_le_left (ε / 2) (1 / 2)])

/-- The only window still requiring a clean endpoint estimate. Here the
scaled displacement is at most (21/2) log log T. -/
def SelbergEndpointWindow : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (1/2 : ℝ) 1,
    Real.log T * (σ-1/2) ≤ (21/2) * Real.log (Real.log T) →
    rightInclusiveCount T σ ≤ C * (T ^ (1-(8/7)*(σ-1/2)) * Real.log T)

/-- The proved Gabriel–Littlewood estimate gives the clean Selberg endpoint
outside the displayed window, including the coincident crossover. -/
theorem endpoint_density_outside_window :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (1/2 : ℝ) 1,
      (21/2)*Real.log (Real.log T) ≤ Real.log T*(σ-1/2) →
      rightInclusiveCount T σ ≤ C * (T ^ (1-(8/7)*(σ-1/2)) * Real.log T) := by
  obtain ⟨C,hC,h⟩ := (uniformLogLossDensity_iff_power _ _).mp ingham_tangent_density_log_loss
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with T hd ht σ hσ hx
  apply (hd σ hσ).trans
  apply mul_le_mul_of_nonneg_left _ hC
  conv_rhs => rw [← Real.rpow_one (Real.log T)]
  rw [density_profile_exp ht, density_profile_exp ht, Real.exp_le_exp]
  linarith only [hx]

/-- Exact equivalence for the CCDF with a single logarithm. The interior
window is an open estimate when no provider is supplied. -/
theorem endpoint_density_iff_window : UniformSelbergDensity (8/7) ↔ SelbergEndpointWindow := by
  constructor
  · rintro ⟨C,H,hC,hH,hd⟩
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_ge_atTop H] with T ht σ hσ _
    simpa only [mul_assoc] using hd T ht σ hσ
  · rintro ⟨A,hA,ha⟩
    obtain ⟨B,hB,hb⟩ := endpoint_density_outside_window
    have h : ∀ᶠ T : ℝ in atTop, SelbergDensityBound T (max A B) (8/7) := by
      filter_upwards [ha,hb,eventually_gt_atTop (1:ℝ)] with T a b ht
      intro σ hσ
      rw [mul_assoc]
      have hx : 0 ≤ T ^ (1-(8/7)*(σ-1/2)) * Real.log T :=
        mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans ht).le _) (Real.log_pos ht).le
      rcases le_total (Real.log T*(σ-1/2)) ((21/2)*Real.log (Real.log T)) with hlow | hhigh
      · exact (a σ hσ hlow).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx)
      · exact (b σ hσ hhigh).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)
    obtain ⟨H,h⟩ := eventually_atTop.1 h
    exact ⟨max A B, max 2 H, hA.trans (le_max_left _ _),
      by linarith only [le_max_left (2:ℝ) H], fun T ht => h T ((le_max_right _ _).trans ht)⟩

/-- A uniform moving-slope input reaches the exact clean endpoint if its
slope deficit times log log T stays bounded. -/
theorem endpoint_density_of_moving_slope {g : ℝ → ℝ} {M C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ T : ℝ in atTop, 0 ≤ g T ∧ g T * Real.log (Real.log T) ≤ M ∧
      SelbergDensityBound T C ((8/7)-g T)) : UniformSelbergDensity (8/7) := by
  apply endpoint_density_iff_window.mpr
  refine ⟨C*Real.exp ((21/2)*M), mul_nonneg hC (Real.exp_pos _).le, ?_⟩
  filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T hd ht σ hσ hx
  apply (hd.2.2 σ hσ).trans
  rw [mul_assoc]
  have hg := mul_le_mul_of_nonneg_left hx hd.1
  have hcomp : Real.log T*(1-((8/7)-g T)*(σ-1/2)) ≤
      (21/2)*M + Real.log T*(1-(8/7)*(σ-1/2)) := by nlinarith only [hg, hd.2.1]
  have hpow : T ^ (1-((8/7)-g T)*(σ-1/2)) ≤ Real.exp ((21/2)*M) * T^(1-(8/7)*(σ-1/2)) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans ht), Real.rpow_def_of_pos (zero_lt_one.trans ht),
      ← Real.exp_add, Real.exp_le_exp]
    exact hcomp
  calc
    _ ≤ C * ((Real.exp ((21/2)*M) * T^(1-(8/7)*(σ-1/2))) * Real.log T) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (Real.log_pos ht).le) hC
    _ = _ := by ring

end RiemannResearch.Analysis.ActualZeroOrdinate
