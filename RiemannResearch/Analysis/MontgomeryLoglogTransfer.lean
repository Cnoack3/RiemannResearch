/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroCoshMass
import RiemannResearch.Analysis.ActualZeroFMZComparison
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.ActualZeroHorizontalMomentRate
import RiemannResearch.Analysis.MontgomeryHorizontalBessel
import RiemannResearch.Analysis.MontgomeryHorizontalLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Horizontal energy and the Montgomery form factors at shrinking frequencies

For the phase frequency `u = α log T`, reflection expresses the positive
Montgomery budget exactly in terms of two cosh masses and the horizontal
second moment. The unconditional zero-density profile in `ActualZeroLoglogRate`
and the local Cauchy bound in `MontgomeryHorizontalBessel` then compare the
complex-zero and raw-ordinate square-root form factors when
`u² (log log T)² / log T → 0`.

The complex-zero statistic follows Baluyot, Goldston, Suriajaya and
Turnage-Butterbaugh, https://doi.org/10.4064/aa230612-20-3.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open ActualZeroOrdinate ActualZeroCoshMass MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- Reflection gives an exact formula for the positive Montgomery budget. -/
theorem horizontalBudget_eq_coshMass (T u : ℝ) :
    horizontalBudget T u = horizontalEnergy T + coshMass T (2 * u) - 2 * coshMass T u := by
  let g := fun ρ : ℂ => (Real.exp (u * (ρ.re - 1 / 2)) - 1) ^ 2 + (ρ.re - 1 / 2) ^ 2
  have hp (ρ : ℂ) : (g ρ + g (reflect ρ)) / 2 =
      (ρ.re - 1 / 2) ^ 2 + coshDefect (2 * u) ρ - 2 * coshDefect u ρ := by
    dsimp only [g, coshDefect]
    rw [reflect_re, show 1 - ρ.re - 1 / 2 = -(ρ.re - 1 / 2) by ring]
    simp only [mul_neg, Real.cosh_eq]
    rw [show (2 * u) * (ρ.re - 1 / 2) = u * (ρ.re - 1 / 2) + u * (ρ.re - 1 / 2) by ring,
      show -(u * (ρ.re - 1 / 2) + u * (ρ.re - 1 / 2)) =
        -(u * (ρ.re - 1 / 2)) + -(u * (ρ.re - 1 / 2)) by ring]
    simp only [Real.exp_add]
    ring
  calc
    horizontalBudget T u = realSum T g := by rw [realSum_eq_copies]; rfl
    _ = (realSum T g + realSum T (fun ρ => g (reflect ρ))) / 2 := by
      rw [realSum_reflect]; ring
    _ = realSum T (fun ρ => (g ρ + g (reflect ρ)) / 2) := by
      simp_rw [div_eq_mul_inv]
      rw [realSum_mul_const]
      exact congrArg (fun x : ℝ => x * (2 : ℝ)⁻¹) (realSum_add T g (fun ρ => g (reflect ρ))).symm
    _ = _ := by
      simp_rw [hp]
      unfold horizontalEnergy coshMass realSum
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by ring

/-- Direct bound using only the unweighted second moment. -/
theorem horizontalBudget_le_horizontalEnergy (T u : ℝ) :
    horizontalBudget T u ≤ (1 + 4 * (Real.cosh u - 1)) * horizontalEnergy T := by
  have h := coshMass_le_horizontalEnergy_sharp T (2 * u)
  have he : |2 * u| / 2 = |u| := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [he, Real.cosh_abs] at h
  rw [horizontalBudget_eq_coshMass]
  linarith [coshMass_nonneg T u]

private theorem coshMass_le_of_strictTail (T u M q : ℝ) (hM : 0 ≤ M) (hu : |u| < q)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2), strictTail T t ≤ M * Real.exp (-q * t)) :
    coshMass T u ≤ M * u ^ 2 / (q ^ 2 - u ^ 2) := by
  have he : coshMass T u = badWeightedSum T 0 (fun t => Real.cosh (|u| * t) - 1) := by
    rw [coshMass, badWeightedSum_eq_realSum]
    congr 1
    funext ρ
    by_cases h : ρ.re - 1 / 2 = 0
    · simp only [coshDefect, h, abs_zero, mul_zero, Real.cosh_zero, sub_self,
        lt_self_iff_false, if_false]
    · rw [if_pos (abs_pos.mpr h), ← abs_mul, Real.cosh_abs]
      rfl
  rw [he]
  have hb := badCoshSum_le_of_expTail_closed T 0 |u| M q
    (by norm_num) (by norm_num) (abs_nonneg u) hu htail
  calc
    _ ≤ M * ((|u| / 2) * ((1 - Real.exp (-(q - |u|) / 2)) / (q - |u|) -
          (1 - Real.exp (-(q + |u|) / 2)) / (q + |u|))) := by
      simpa only [mul_zero, Real.cosh_zero, sub_self, zero_mul, Real.exp_zero,
        zero_add, mul_assoc] using hb
    _ ≤ M * (|u| ^ 2 / (q ^ 2 - |u| ^ 2)) :=
      mul_le_mul_of_nonneg_left (coshTail_closed_le_rational |u| q (abs_nonneg _) hu) hM
    _ = _ := by rw [sq_abs]; ring

/-- Finite transfer from an exponential profile of the two-sided actual-zero count. -/
theorem horizontalBudget_le_of_strictTail (T u M q : ℝ) (hM : 0 ≤ M) (hq : 0 < q)
    (hu : |u| ≤ q / 4)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2), strictTail T t ≤ M * Real.exp (-q * t)) :
    horizontalBudget T u ≤ 8 * M * (1 + u ^ 2) / q ^ 2 := by
  have h2 : |2 * u| ≤ q / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
  have hsq := (sq_le_sq₀ (abs_nonneg (2 * u)) (by positivity : 0 ≤ q / 2)).mpr h2
  rw [sq_abs] at hsq
  have hd : 0 < q ^ 2 - (2 * u) ^ 2 := by nlinarith [sq_pos_of_pos hq]
  have hc := coshMass_le_of_strictTail T (2 * u) M q hM (by linarith) htail
  have hb : coshMass T (2 * u) ≤ 8 * M * u ^ 2 / q ^ 2 := by
    apply hc.trans
    rw [div_le_div_iff₀ hd (sq_pos_of_pos hq)]
    have hprod := mul_nonneg (mul_nonneg hM (sq_nonneg u))
      (show 0 ≤ q ^ 2 - 2 * (2 * u) ^ 2 by nlinarith [sq_nonneg q])
    nlinarith only [hprod]
  have hE := horizontalEnergy_le_of_exponential_strictTail T M q hM hq htail
  rw [horizontalBudget_eq_coshMass]
  rw [le_div_iff₀ (sq_pos_of_pos hq)] at hb hE ⊢
  nlinarith only [hb, hE, hM, mul_nonneg (coshMass_nonneg T u) (sq_nonneg q)]

/-- Uniform unconditional budget through a growing interval of physical frequencies. -/
theorem eventually_horizontalBudget_loglog_band :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, |u| ≤ horizontalTailDecay T / 4 →
      horizontalBudget T u / T ≤ C * (1 + u ^ 2) * horizontalLogRate T := by
  obtain ⟨K, hK, hprofile⟩ := eventually_rightStrictTail_loglog_bound
  refine ⟨1024 * K, by positivity, ?_⟩
  filter_upwards [hprofile, eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T ht hT hl
  have hTp : 0 < T := by linarith
  have hL := Real.log_pos hT
  have hq : 0 < horizontalTailDecay T := by unfold horizontalTailDecay; positivity
  intro u hu
  have h := horizontalBudget_le_of_strictTail T u (2 * (K * T * Real.log T)) (horizontalTailDecay T)
    (by positivity) hq hu (fun t hm => by
      rw [strictTail_eq_twice_right T t hm.1]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (ht t hm) (by norm_num : (0 : ℝ) ≤ 2))
  refine (div_le_div_of_nonneg_right h hTp.le).trans (le_of_eq ?_)
  unfold horizontalTailDecay horizontalLogRate
  field_simp
  ring

/-- The frequency hypothesis is a little-oh condition on the unscaled phase frequency. -/
theorem horizontalBudget_div_height_tendsto_zero_of_loglog (u : ℝ → ℝ)
    (hu : Tendsto (fun T => (u T) ^ 2 * horizontalLogRate T) atTop (𝓝 0)) :
    Tendsto (fun T => horizontalBudget T (u T) / T) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := eventually_horizontalBudget_loglog_band
  have hmajor : Tendsto (fun T => C * (1 + (u T) ^ 2) * horizontalLogRate T) atTop (𝓝 0) := by
    have hh := (horizontalLogRate_tendsto_zero.add hu).const_mul C
    convert hh using 1
    · funext T
      ring
    · simp
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact div_nonneg (horizontalBudget_nonneg T _) hT
  · filter_upwards [hbound, hu.eventually_le_const (by norm_num : (0 : ℝ) < 1),
      Real.tendsto_log_atTop.eventually_ge_atTop 1024,
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
      with T hb hs hL hl
    apply hb
    change 0 < Real.log (Real.log T) at hl
    have hLpos : 0 < Real.log T := by linarith
    have hD : 0 < horizontalTailDecay T := by unfold horizontalTailDecay; positivity
    have hR : 0 < horizontalLogRate T := by unfold horizontalLogRate; positivity
    by_contra! hn
    have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ horizontalTailDecay T / 4)
      (abs_nonneg (u T))).mpr hn
    rw [sq_abs] at hsq
    have hp := mul_lt_mul_of_pos_right hsq hR
    have he : (horizontalTailDecay T / 4) ^ 2 * horizontalLogRate T = Real.log T / 1024 := by
      unfold horizontalTailDecay horizontalLogRate
      field_simp [hl.ne', hLpos.ne'] <;> ring
    rw [he] at hp
    linarith

/-- The actual complex-zero and raw-ordinate square-root form factors agree
asymptotically at every moving frequency in the stated range. -/
theorem sqrt_formFactor_difference_tendsto_zero_of_loglog (α : ℝ → ℝ)
    (hα : Tendsto (fun T => (α T * Real.log T) ^ 2 * horizontalLogRate T) atTop (𝓝 0)) :
    Tendsto (fun T => |Real.sqrt (sharpFormFactor T (α T)) -
      Real.sqrt (formFactor T (α T))|) atTop (𝓝 0) :=
  sqrt_horizontal_difference_tendsto_zero α
    (horizontalBudget_div_height_tendsto_zero_of_loglog (fun T => α T * Real.log T) hα)

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
