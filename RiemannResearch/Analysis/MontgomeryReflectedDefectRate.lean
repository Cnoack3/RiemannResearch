/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCoshMass
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.CoshTaylorRemainder
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryLoglogTransfer
import RiemannResearch.Analysis.MontgomeryReflectedBessel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quartic phase-frequency bound for the reflected Montgomery defect

The exact reflection split in `MontgomeryReflectedBessel` allows the two
shift terms to be estimated by a second moment and the phase coefficient by
a fourth moment. The unconditional log-loss density input and the sharper
Selberg density premise give separate bounds for the same actual-zero
defect. Frequencies here are unscaled phases `u = α log T`.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

open ActualZeroOrdinate ActualZeroCoshMass MontgomeryHorizontalTransfer MontgomeryFormFactor

private theorem cosh_double (x : ℝ) : Real.cosh (2 * x) = 2 * Real.cosh x ^ 2 - 1 := by
  rw [two_mul x, Real.cosh_eq, Real.cosh_eq, neg_add, Real.exp_add, Real.exp_add]
  have hp : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith only [hp]

private theorem cosh_defect_sq_le_taylor (x : ℝ) :
    (Real.cosh x - 1) ^ 2 ≤ (1 / 2) * Real.coshTaylorRemainder 1 (2 * x) := by
  have he : Real.coshTaylorRemainder 1 (2 * x) =
      Real.cosh (2 * x) - (1 + (2 * x) ^ 2 / 2) := by
    norm_num [Real.coshTaylorRemainder, Real.coshTaylorHead, Real.coshTaylorTerm, Finset.sum_range_succ]
    <;> ring
  rw [he, cosh_double]
  nlinarith only [Real.sq_div_two_le_cosh_sub_one x]

private theorem sq_mul_exp_half_le_cosh_defect (x : ℝ) :
    x ^ 2 * Real.exp (x / 2) ≤ 8 * (Real.cosh x - 1) := by
  have hs : x ^ 2 / 8 ≤ Real.cosh (x / 2) - 1 := by
    nlinarith only [Real.sq_div_two_le_cosh_sub_one (x / 2)]
  have he : Real.exp (x / 2) / 2 ≤ Real.cosh (x / 2) + 1 := by
    rw [Real.cosh_eq]
    linarith only [Real.exp_pos (-(x / 2))]
  have hc : Real.cosh x - 1 = 2 * (Real.cosh (x / 2) - 1) * (Real.cosh (x / 2) + 1) := by
    conv_lhs => rw [show x = 2 * (x / 2) by ring, cosh_double]
    ring
  have hb := mul_le_mul hs he (by positivity : 0 ≤ Real.exp (x / 2) / 2)
    (show 0 ≤ Real.cosh (x / 2) - 1 by linarith only [hs, sq_nonneg x])
  nlinarith only [hc, hb]

private theorem reflected_budget_term_le (u v x : ℝ) (hv : 0 < v) (hu : |u| ≤ v / 4) :
    (Real.cosh (u * x) - 1) ^ 2 + x ^ 2 *
      (Real.exp (2 * (u * x)) + Real.exp (2 * (u * -x))) ≤
        ((1 / 2) * (|2 * u| / v) ^ 4 + 16 / v ^ 2) * (Real.cosh (v * x) - 1) := by
  let w := v * |x|
  have habs : Real.cosh w = Real.cosh (v * x) := by
    dsimp [w]
    rw [show v * |x| = |v * x| by rw [abs_mul, abs_of_pos hv], Real.cosh_abs]
  have h2u : |2 * u| ≤ v / 2 := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have htay := Real.coshTaylorRemainder_frequency_le 1 (2 * u) v |x| hv
    (h2u.trans (by linarith)) (abs_nonneg x)
  change Real.coshTaylorRemainder 1 ((2 * u) * |x|) ≤
    (|2 * u| / v) ^ (2 * (1 + 1)) * (Real.cosh w - 1) at htay
  rw [habs] at htay
  have hsame : Real.coshTaylorRemainder 1 ((2 * u) * x) =
      Real.coshTaylorRemainder 1 ((2 * u) * |x|) := by
    rw [← Real.coshTaylorRemainder_abs 1 ((2 * u) * x),
      ← Real.coshTaylorRemainder_abs 1 ((2 * u) * |x|)]
    simp only [abs_mul, abs_abs]
  have hquad := (cosh_defect_sq_le_taylor (u * x)).trans
    (mul_le_mul_of_nonneg_left (show Real.coshTaylorRemainder 1 (2 * (u * x)) ≤
      (|2 * u| / v) ^ 4 * (Real.cosh (v * x) - 1) by
        rw [← mul_assoc, hsame]
        exact htay) (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hphase (t : ℝ) (ht : |t| = |x|) : Real.exp (2 * (u * t)) ≤ Real.exp (w / 2) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |(2 * u) * t| := by rw [mul_assoc]; exact le_abs_self _
      _ = |2 * u| * |x| := by rw [abs_mul, ht]
      _ ≤ _ := by
        dsimp [w]
        nlinarith only [mul_le_mul_of_nonneg_right h2u (abs_nonneg x)]
  have hw : w ^ 2 = v ^ 2 * x ^ 2 := by dsimp [w]; rw [mul_pow, sq_abs]
  have hsqx : x ^ 2 * Real.exp (w / 2) ≤ 8 / v ^ 2 * (Real.cosh (v * x) - 1) := by
    have h := sq_mul_exp_half_le_cosh_defect w
    rw [hw, habs] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hv)]
    nlinarith only [h]
  have hp := mul_le_mul_of_nonneg_left (hphase x rfl) (sq_nonneg x)
  have hm := mul_le_mul_of_nonneg_left (hphase (-x) (abs_neg x)) (sq_nonneg x)
  calc
    _ = (Real.cosh (u * x) - 1) ^ 2 +
        (x ^ 2 * Real.exp (2 * (u * x)) + x ^ 2 * Real.exp (2 * (u * -x))) := by ring
    _ ≤ (1 / 2) * ((|2 * u| / v) ^ 4 * (Real.cosh (v * x) - 1)) +
        (8 / v ^ 2 * (Real.cosh (v * x) - 1) + 8 / v ^ 2 * (Real.cosh (v * x) - 1)) :=
      add_le_add hquad (add_le_add (hp.trans hsqx) (hm.trans hsqx))
    _ = _ := by ring

/-- Finite quartic control of the entire reflected horizontal budget from an
actual two-sided exponential tail. -/
theorem reflectedHorizontalBudget_le_of_strictTail (T u M q : ℝ) (hM : 0 ≤ M) (hq : 0 < q)
    (hu : |u| ≤ q / 8)
    (htail : ∀ t ∈ Icc (0 : ℝ) (1 / 2), strictTail T t ≤ M * Real.exp (-q * t)) :
    reflectedHorizontalBudget T u ≤ 128 * M * (u ^ 4 / q ^ 4 + 1 / q ^ 2) := by
  let v := q / 2
  let A := (1 / 2) * (|2 * u| / v) ^ 4 + 16 / v ^ 2
  have hv : 0 < v := by dsimp [v]; positivity
  have hvq : v < q := by dsimp [v]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsum : reflectedHorizontalBudget T u ≤ A * coshMass T v := by
    unfold reflectedHorizontalBudget coshMass
    rw [realSum_eq_copies, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact reflected_budget_term_le u v (i.1.1.re - 1 / 2) hv (by dsimp [v]; linarith)
  have hc := coshMass_le_of_strictTail T v M q hM (by rw [abs_of_pos hv]; exact hvq) htail
  have hrat : M * v ^ 2 / (q ^ 2 - v ^ 2) = M / 3 := by
    rw [show q ^ 2 - v ^ 2 = 3 * q ^ 2 / 4 by dsimp [v]; ring]
    dsimp only [v]
    field_simp [hq.ne']
    <;> ring
  have hscale : A = 128 * (u ^ 4 / q ^ 4) + 64 / q ^ 2 := by
    have hpow : |2 * u| ^ 4 = (2 * u) ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (2 * u) ^ 4)]
    dsimp only [A, v]
    rw [div_pow, hpow]
    field_simp [hq.ne']
    <;> ring
  calc
    _ ≤ A * (M * v ^ 2 / (q ^ 2 - v ^ 2)) := hsum.trans (mul_le_mul_of_nonneg_left hc hA)
    _ = (128 * (u ^ 4 / q ^ 4) + 64 / q ^ 2) * (M / 3) := by rw [hrat, hscale]
    _ ≤ _ := by
      have h₁ : 0 ≤ M * (u ^ 4 / q ^ 4) := by positivity
      have h₂ : 0 ≤ M * (1 / q ^ 2) := by positivity
      have hm₁ := mul_le_mul_of_nonneg_right (by norm_num : (128 / 3 : ℝ) ≤ 128) h₁
      have hm₂ := mul_le_mul_of_nonneg_right (by norm_num : (64 / 3 : ℝ) ≤ 128) h₂
      calc
        _ = (128 / 3) * (M * (u ^ 4 / q ^ 4)) + (64 / 3) * (M * (1 / q ^ 2)) := by ring
        _ ≤ 128 * (M * (u ^ 4 / q ^ 4)) + 128 * (M * (1 / q ^ 2)) := add_le_add hm₁ hm₂
        _ = _ := by ring

/-- The phase-frequency part of the unconditional reflected defect. -/
def horizontalQuarticRate (T : ℝ) : ℝ :=
  (Real.log (Real.log T)) ^ 4 / (Real.log T) ^ 3

/-- The Cauchy density input gives an unconditional quartic transfer scale. -/
theorem eventually_horizontalDefect_reflected_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α : ℝ,
      let u := α * Real.log T
      |u| ≤ horizontalTailDecay T / 8 →
      horizontalDefect T α ≤ C * (horizontalLogRate T + u ^ 4 * horizontalQuarticRate T) := by
  obtain ⟨K, hK, htail⟩ := eventually_rightStrictTail_loglog_bound
  obtain ⟨D, hD, hdef⟩ := exists_horizontalDefect_le_reflected_budget
  refine ⟨256 * D * K * 4096, by positivity, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (9 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with T ht hT hℓ
  intro α u hu
  have hTp : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (by linarith)
  have hq : 0 < horizontalTailDecay T := by unfold horizontalTailDecay; positivity
  have hr := reflectedHorizontalBudget_le_of_strictTail T u (2 * (K * T * Real.log T))
    (horizontalTailDecay T) (by positivity) hq hu (fun t hmem => by
      rw [strictTail_eq_twice_right T t hmem.1]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (ht t hmem) (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ D * reflectedHorizontalBudget T u / T := hdef T α hT
    _ ≤ D * (128 * (2 * (K * T * Real.log T)) *
        (u ^ 4 / horizontalTailDecay T ^ 4 + 1 / horizontalTailDecay T ^ 2)) / T :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hD.le) hTp.le
    _ = (256 * D * K) * (64 * horizontalLogRate T + 4096 * (u ^ 4 * horizontalQuarticRate T)) := by
      unfold horizontalTailDecay horizontalLogRate horizontalQuarticRate
      field_simp [hTp.ne', hL.ne', ne_of_gt hℓ]
      <;> ring
    _ ≤ _ := by
      rw [show 256 * D * K * 4096 * (horizontalLogRate T + u ^ 4 * horizontalQuarticRate T) =
        (256 * D * K) * (4096 * (horizontalLogRate T + u ^ 4 * horizontalQuarticRate T)) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hR : 0 ≤ horizontalLogRate T := by unfold horizontalLogRate; positivity
      linarith only [hR]

/-- A uniform Selberg provider supplies the sharper quartic phase scale. -/
theorem eventually_horizontalDefect_reflected_selberg {a : ℝ}
    (ha : 0 < a) (hS : UniformSelbergDensity a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α : ℝ,
      let u := α * Real.log T
      |u| ≤ a * Real.log T / 8 →
        horizontalDefect T α ≤ C *
          (1 / (a ^ 2 * Real.log T) + u ^ 4 / (a ^ 4 * (Real.log T) ^ 3)) := by
  obtain ⟨K, H, hK, hH, htail⟩ := hS
  obtain ⟨D, hD, hdef⟩ := exists_horizontalDefect_le_reflected_budget
  refine ⟨256 * D * (K + 1), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop H, eventually_ge_atTop (9 : ℝ)] with T hTH hT
  intro α u hu
  have hTp : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos (hH.trans_le hTH)
  have hr := reflectedHorizontalBudget_le_of_strictTail T u (2 * K * T * Real.log T)
    (a * Real.log T) (by positivity) (mul_pos ha hL) hu (fun t hmem =>
      strictTail_of_selbergDensity T K a t hTp hmem (htail T hTH))
  calc
    _ ≤ D * reflectedHorizontalBudget T u / T := hdef T α hT
    _ ≤ D * (128 * (2 * K * T * Real.log T) *
        (u ^ 4 / (a * Real.log T) ^ 4 + 1 / (a * Real.log T) ^ 2)) / T :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hD.le) hTp.le
    _ = (256 * D * K) *
        (1 / (a ^ 2 * Real.log T) + u ^ 4 / (a ^ 4 * (Real.log T) ^ 3)) := by
      field_simp [hTp.ne', hL.ne', ha.ne']
      <;> ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity : 0 ≤ 256 * D))
        (by positivity)


/-- Reflection gives square-root agreement whenever the quartic phase
budget vanishes. The budget assumption already enforces the frequency band. -/
theorem sqrt_formFactor_difference_tendsto_zero_of_reflectedLoglog
    (α : ℝ → ℝ)
    (hsmall : Tendsto (fun T => (α T * Real.log T) ^ 4 * horizontalQuarticRate T)
      atTop (𝓝 0)) :
    Tendsto (fun T => |Real.sqrt (sharpFormFactor T (α T)) -
      Real.sqrt (formFactor T (α T))|) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := eventually_horizontalDefect_reflected_loglog
  have hq := (horizontalLogRate_tendsto_zero.add hsmall).const_mul C
  simp only [add_zero, mul_zero] at hq
  have hlim : Tendsto (fun T => Real.sqrt (C *
      (horizontalLogRate T + (α T * Real.log T) ^ 4 * horizontalQuarticRate T))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hq
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ hlim
  filter_upwards [hb, hsmall.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    Real.tendsto_log_atTop.eventually_ge_atTop ((64 : ℝ) ^ 4),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with T ht hs hL hℓ
  let L := Real.log T
  let ℓ := Real.log L
  let u := α T * L
  change 64 ^ 4 ≤ L at hL
  change 0 < ℓ at hℓ
  have hL₀ : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hR : 0 < horizontalQuarticRate T := by unfold horizontalQuarticRate; positivity
  have hband : |u| ≤ horizontalTailDecay T / 8 := by
    by_contra! h
    have hcut : 0 ≤ horizontalTailDecay T / 8 := by unfold horizontalTailDecay; positivity
    have hs₂ := (sq_lt_sq₀ hcut (abs_nonneg u)).2 h
    have hpow : (horizontalTailDecay T / 8) ^ 4 < |u| ^ 4 := by
      have hs₄ := (sq_lt_sq₀ (sq_nonneg (horizontalTailDecay T / 8))
        (sq_nonneg |u|)).2 hs₂
      simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by decide] using hs₄
    have hu4 : |u| ^ 4 = u ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ u ^ 4)]
    rw [hu4] at hpow
    have hw := mul_lt_mul_of_pos_right hpow hR
    have he : (horizontalTailDecay T / 8) ^ 4 * horizontalQuarticRate T =
        L / (64 : ℝ) ^ 4 := by
      unfold horizontalTailDecay horizontalQuarticRate
      change (L / (8 * ℓ) / 8) ^ 4 * (ℓ ^ 4 / L ^ 3) = _
      field_simp [hL₀.ne', hℓ.ne']
      <;> ring
    rw [he] at hw
    have hone : 1 ≤ L / (64 : ℝ) ^ 4 := (le_div_iff₀ (by norm_num)).2 (by simpa using hL)
    exact (not_lt_of_ge hs) (hone.trans_lt hw)
  exact (sqrt_horizontal_error T (α T)).trans (Real.sqrt_le_sqrt (ht (α T) hband))

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
