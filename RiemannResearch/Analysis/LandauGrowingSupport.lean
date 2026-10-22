/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Deterministic dimension-weighted Landau error envelopes

The complete three-term fixed-c=2 remainder is transformed exactly to an
exponential envelope. Polynomial-times-exponential decay proves uniform
vanishing at every fixed square-root-log support coefficient and below
the strict polynomial exponent 2/7. The exact endpoint envelope divided
by log height also tends to zero, retaining the zero-count logarithmic gain.
The leading budget exp(7*ell/2-L)/L -> 0 exactly characterizes convergence
of the complete normalized envelope. It permits exp(ell)=o((exp(L)*L)^(2/7))
and every fixed logarithmic support gain b<2/7. These are elementary
support conditions, independent of any zero-density provider.
This module is scalar analysis; ActualLandauOperatorResidual specializes it to actual
zeta zeros with the arithmetic main matrix retained. Source: the proved
ActualUniformRationalLandau provider and the repository support argument.
-/

noncomputable section
open Filter

namespace RiemannResearch.Analysis.LandauGrowth

/-- Complete dimension-weighted fixed-c=2 Landau remainder after the
exponential height factor. Its three summands are retained exactly. -/
def matrixEnvelope (L ell : ℝ) : ℝ :=
  Real.exp (7 * ell / 2 - L) +
    L ^ 2 * Real.exp (5 * ell / 2 - L) +
    L * Real.exp (2 * ell - L)

theorem matrixEnvelope_nonneg {L : ℝ} (hL : 0 ≤ L) (ell : ℝ) :
    0 ≤ matrixEnvelope L ell := by
  unfold matrixEnvelope
  positivity

theorem matrixEnvelope_le {L ell : ℝ} (hL : 0 ≤ L) (hell : ell ≤ L / 8) :
    matrixEnvelope L ell ≤ (1 + L ^ 2 + L) * Real.exp (-L / 2) := by
  have h1 : Real.exp (7 * ell / 2 - L) ≤ Real.exp (-L / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (5 * ell / 2 - L) ≤ Real.exp (-L / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (2 * ell - L) ≤ Real.exp (-L / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold matrixEnvelope
  calc
    _ ≤ Real.exp (-L / 2) + L ^ 2 * Real.exp (-L / 2) +
        L * Real.exp (-L / 2) := add_le_add
      (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg L)))
      (mul_le_mul_of_nonneg_left h3 hL)
    _ = _ := by ring

theorem polynomial_exp_majorant_tendsto_zero :
    Tendsto (fun L : ℝ => (1 + L ^ 2 + L) * Real.exp (-L / 2))
      atTop (nhds 0) := by
  have hhalf : Tendsto (fun L : ℝ => L / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hhalf
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hhalf
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hhalf
  have h := h0.add ((h2.const_mul 4).add (h1.const_mul 2))
  convert h using 1
  · funext L
    change (1 + L ^ 2 + L) * Real.exp (-L / 2) =
      (L / 2) ^ 0 * Real.exp (-(L / 2)) +
        (4 * ((L / 2) ^ 2 * Real.exp (-(L / 2))) +
          2 * ((L / 2) ^ 1 * Real.exp (-(L / 2))))
    rw [show -(L / 2) = -L / 2 by ring]
    simp only [pow_zero, pow_one, one_mul]
    ring
  · norm_num

/-- No zero-density premise is needed for this deterministic Landau envelope.
An eventual logarithmic support budget supplies a uniform vanishing bound. -/
theorem matrixEnvelope_tendsto_zero (ell : ℝ → ℝ)
    (hell : ∀ᶠ L : ℝ in atTop, ell L ≤ L / 8) :
    Tendsto (fun L : ℝ => matrixEnvelope L (ell L)) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact matrixEnvelope_nonneg hL (ell L)
  · filter_upwards [hell, eventually_ge_atTop (0 : ℝ)] with L he hL
    exact matrixEnvelope_le hL he
  · exact polynomial_exp_majorant_tendsto_zero

theorem sqrt_support_eventually_le (c : ℝ) :
    ∀ᶠ L : ℝ in atTop, c * Real.sqrt L ≤ L / 8 := by
  filter_upwards [eventually_ge_atTop (64 * |c| ^ 2),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  have hs0 := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL0
  have hc0 := abs_nonneg c
  have hs : 8 * |c| ≤ Real.sqrt L := by
    by_contra hn
    have hh : Real.sqrt L < 8 * |c| := lt_of_not_ge hn
    have hp := mul_pos (sub_pos.mpr hh)
      (by nlinarith : 0 < 8 * |c| + Real.sqrt L)
    nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hs) hs0
  have hc := mul_le_mul_of_nonneg_right (le_abs_self c) hs0
  nlinarith

theorem matrixEnvelope_sqrt_tendsto_zero (c : ℝ) :
    Tendsto (fun L : ℝ => matrixEnvelope L (c * Real.sqrt L)) atTop (nhds 0) :=
  matrixEnvelope_tendsto_zero _ (sqrt_support_eventually_le c)

theorem matrixEnvelope_mono {L a b : ℝ} (hL : 0 ≤ L) (hab : a ≤ b) :
    matrixEnvelope L a ≤ matrixEnvelope L b := by
  unfold matrixEnvelope
  apply add_le_add
  · apply add_le_add
    · exact Real.exp_le_exp.mpr (by linarith)
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        (sq_nonneg L)
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hL

theorem mul_rpow_div_eq_exp {Y d : ℝ} (hY : 0 < Y) (hd : 0 < d) (a : ℝ) :
    d * d ^ a / Y = Real.exp ((a + 1) * Real.log d - Real.log Y) := by
  rw [Real.rpow_def_of_pos hd, Real.exp_sub,
    show (a + 1) * Real.log d = Real.log d + Real.log d * a by ring,
    Real.exp_add, Real.exp_log hd, Real.exp_log hY]

/-- Exact change from the three rpow summands to their dimension-weighted
exponential envelope. No summand is removed. -/
theorem matrixEnvelope_eq_rpow {Y d : ℝ} (hY : 0 < Y) (hd : 0 < d) :
    matrixEnvelope (Real.log Y) (Real.log d) =
      d * (d ^ (5 / 2 : ℝ) + d ^ (3 / 2 : ℝ) * (Real.log Y) ^ 2 +
        d * Real.log Y) / Y := by
  have h1 := mul_rpow_div_eq_exp hY hd (5 / 2 : ℝ)
  have h2 := mul_rpow_div_eq_exp hY hd (3 / 2 : ℝ)
  have h3 := mul_rpow_div_eq_exp hY hd (1 : ℝ)
  norm_num at h1 h2 h3
  unfold matrixEnvelope
  rw [show 7 * Real.log d / 2 = (7 / 2 : ℝ) * Real.log d by ring,
    show 5 * Real.log d / 2 = (5 / 2 : ℝ) * Real.log d by ring,
    ← h1, ← h2, ← h3]
  ring

theorem polynomial_exp_div_majorant_tendsto_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun L : ℝ => (1 + L ^ 2 + L) * Real.exp (-L / a)) atTop (nhds 0) := by
  have hscale : Tendsto (fun L : ℝ => L / a) atTop atTop := tendsto_id.atTop_div_const ha
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hscale
  have h := h0.add ((h2.const_mul (a ^ 2)).add (h1.const_mul a))
  convert h using 1
  · funext L
    change (1 + L ^ 2 + L) * Real.exp (-L / a) =
      (L / a) ^ 0 * Real.exp (-(L / a)) +
        (a ^ 2 * ((L / a) ^ 2 * Real.exp (-(L / a))) +
          a * ((L / a) ^ 1 * Real.exp (-(L / a))))
    rw [show -(L / a) = -L / a by ring]
    simp only [pow_zero, pow_one, one_mul]
    field_simp [ha.ne'] <;> ring
  · norm_num

theorem matrixEnvelope_linear_le {L ell theta : ℝ} (hL : 0 ≤ L)
    (htheta0 : 0 ≤ theta) (hell : ell ≤ theta * L) :
    matrixEnvelope L ell ≤ (1 + L ^ 2 + L) *
      Real.exp (-(1 - 7 * theta / 2) * L) := by
  have h1 : Real.exp (7 * ell / 2 - L) ≤ Real.exp (-(1 - 7 * theta / 2) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : Real.exp (5 * ell / 2 - L) ≤ Real.exp (-(1 - 7 * theta / 2) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h3 : Real.exp (2 * ell - L) ≤ Real.exp (-(1 - 7 * theta / 2) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  unfold matrixEnvelope
  calc
    _ ≤ Real.exp (-(1 - 7 * theta / 2) * L) +
        L ^ 2 * Real.exp (-(1 - 7 * theta / 2) * L) +
        L * Real.exp (-(1 - 7 * theta / 2) * L) :=
      add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (sq_nonneg L)))
        (mul_le_mul_of_nonneg_left h3 hL)
    _ = _ := by ring

theorem matrixEnvelope_linear_tendsto_zero (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta : theta < 2 / 7) :
    Tendsto (fun L : ℝ => matrixEnvelope L (theta * L)) atTop (nhds 0) := by
  have ha : 0 < 1 - 7 * theta / 2 := by linarith
  have hmajor := polynomial_exp_div_majorant_tendsto_zero
    (1 / (1 - 7 * theta / 2)) (by positivity)
  have heq (L : ℝ) : -L / (1 / (1 - 7 * theta / 2)) =
      -(1 - 7 * theta / 2) * L := by field_simp [ha.ne']
  simp_rw [heq] at hmajor
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact matrixEnvelope_nonneg hL _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact matrixEnvelope_linear_le hL htheta0 (le_refl _)
  · exact hmajor

theorem matrixEnvelope_critical_div_eq (a : ℝ) {L : ℝ} (hL : 0 < L) :
    matrixEnvelope L (a + (2 / 7 : ℝ) * L) / L =
      Real.exp (7 * a / 2) / L +
        Real.exp (5 * a / 2) * (L * Real.exp (-2 * L / 7)) +
        Real.exp (2 * a) * Real.exp (-3 * L / 7) := by
  unfold matrixEnvelope
  rw [show 7 * (a + (2 / 7 : ℝ) * L) / 2 - L = 7 * a / 2 by ring,
    show 5 * (a + (2 / 7 : ℝ) * L) / 2 - L = 5 * a / 2 + (-2 * L / 7) by ring,
    show 2 * (a + (2 / 7 : ℝ) * L) - L = 2 * a + (-3 * L / 7) by ring,
    Real.exp_add, Real.exp_add]
  field_simp [hL.ne'] <;> ring

theorem matrixEnvelope_critical_div_tendsto_zero (a : ℝ) :
    Tendsto (fun L : ℝ => matrixEnvelope L (a + (2 / 7 : ℝ) * L) / L)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun L : ℝ => Real.exp (7 * a / 2) / L) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hscale₁ : Tendsto (fun L : ℝ => L / (7 / 2 : ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hp₁ := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale₁).const_mul
    (7 / 2 : ℝ)
  have h₁ : Tendsto (fun L : ℝ => L * Real.exp (-2 * L / 7)) atTop (nhds 0) := by
    convert hp₁ using 1
    · funext L
      change L * Real.exp (-2 * L / 7) =
        (7 / 2 : ℝ) * ((L / (7 / 2 : ℝ)) ^ 1 * Real.exp (-(L / (7 / 2 : ℝ))))
      rw [show -(L / (7 / 2 : ℝ)) = -2 * L / 7 by ring]
      simp only [pow_one]
      ring
    · norm_num
  have hscale₂ : Tendsto (fun L : ℝ => L / (7 / 3 : ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hp₂ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale₂
  have h₂ : Tendsto (fun L : ℝ => Real.exp (-3 * L / 7)) atTop (nhds 0) := by
    convert hp₂ using 1
    funext L
    change Real.exp (-3 * L / 7) =
      (L / (7 / 3 : ℝ)) ^ 0 * Real.exp (-(L / (7 / 3 : ℝ)))
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have hsum : Tendsto (fun L : ℝ =>
      Real.exp (7 * a / 2) / L +
        Real.exp (5 * a / 2) * (L * Real.exp (-2 * L / 7)) +
        Real.exp (2 * a) * Real.exp (-3 * L / 7))
      atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hinv.add (h₁.const_mul (Real.exp (5 * a / 2)))).add
        (h₂.const_mul (Real.exp (2 * a)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact (matrixEnvelope_critical_div_eq a hL).symm


/-- Elementary explicit bound used to turn the leading budget into a coarse
support bound. It does not use a zeta estimate. -/
theorem log_le_one_sixth_of_large {L : ℝ} (hL : 144 ≤ L) :
    Real.log L ≤ L / 6 := by
  have hL0 : 0 < L := by linarith
  have hs0 := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL0.le
  have hs : 12 ≤ Real.sqrt L := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hs) hs0
  have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hL0)
  rw [Real.log_sqrt hL0.le] at hh
  nlinarith

/-- Exact division of the complete three-term envelope by log height. -/
theorem matrixEnvelope_div_eq {L ell : ℝ} (hL : L ≠ 0) :
    matrixEnvelope L ell / L =
      Real.exp (7 * ell / 2 - L) / L +
        L * Real.exp (5 * ell / 2 - L) +
        Real.exp (2 * ell - L) := by
  unfold matrixEnvelope
  field_simp [hL]

/-- Once the leading dimension budget vanishes, both other envelope terms
vanish automatically. This permits the full little-o endpoint
exp(ell)=o((exp(L)*L)^(2/7)). -/
theorem matrixEnvelope_div_tendsto_zero_of_leading_budget
    {α : Type*} (F : Filter α) (L ell : α → ℝ)
    (hL : Tendsto L F atTop)
    (hleading : Tendsto (fun t => Real.exp (7 * ell t / 2 - L t) / L t)
      F (nhds 0)) :
    Tendsto (fun t => matrixEnvelope (L t) (ell t) / L t) F (nhds 0) := by
  have hsupport : ∀ᶠ t in F, ell t ≤ L t / 3 := by
    filter_upwards [hL.eventually_ge_atTop 144,
      hleading.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with t hlarge hsmall
    have hpos : 0 < L t := by linarith
    have he : Real.exp (7 * ell t / 2 - L t) ≤ L t := by
      exact (div_le_one hpos).mp hsmall
    have hlog := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hlog
    have hh := log_le_one_sixth_of_large hlarge
    linarith
  have hscale₁ : Tendsto (fun t => L t / 6) F atTop :=
    hL.atTop_div_const (by norm_num)
  have hp₁ := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    hscale₁).const_mul (6 : ℝ)
  have h₁ : Tendsto (fun t => L t * Real.exp (-L t / 6)) F (nhds 0) := by
    convert hp₁ using 1
    · funext t
      change L t * Real.exp (-L t / 6) =
        6 * ((L t / 6) ^ 1 * Real.exp (-(L t / 6)))
      simp only [pow_one]
      rw [show -(L t / 6) = -L t / 6 by ring]
      ring
    · norm_num
  have hscale₂ : Tendsto (fun t => L t / 3) F atTop :=
    hL.atTop_div_const (by norm_num)
  have hp₂ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale₂
  have h₂ : Tendsto (fun t => Real.exp (-L t / 3)) F (nhds 0) := by
    convert hp₂ using 1
    funext t
    change Real.exp (-L t / 3) =
      (L t / 3) ^ 0 * Real.exp (-(L t / 3))
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have hmajor : Tendsto (fun t => Real.exp (7 * ell t / 2 - L t) / L t +
      L t * Real.exp (-L t / 6) + Real.exp (-L t / 3)) F (nhds 0) := by
    simpa only [add_zero] using (hleading.add h₁).add h₂
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [hL.eventually_gt_atTop 0] with t ht
    exact div_nonneg (matrixEnvelope_nonneg ht.le _) ht.le
  · filter_upwards [hsupport, hL.eventually_gt_atTop 0] with t hs ht
    rw [matrixEnvelope_div_eq ht.ne']
    apply add_le_add
    · apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) ht.le
    · exact Real.exp_le_exp.mpr (by linarith)

/-- The leading budget is the exact convergence criterion for this complete
nonnegative envelope. This is a limitation of the available majorant, not a
necessity theorem for the actual signed residual. -/
theorem matrixEnvelope_div_tendsto_zero_iff_leading_budget
    {α : Type*} (F : Filter α) (L ell : α → ℝ)
    (hL : Tendsto L F atTop) :
    Tendsto (fun t => matrixEnvelope (L t) (ell t) / L t) F (nhds 0) ↔
      Tendsto (fun t => Real.exp (7 * ell t / 2 - L t) / L t) F (nhds 0) := by
  constructor
  · intro hm
    refine squeeze_zero' ?_ ?_ hm
    · filter_upwards [hL.eventually_gt_atTop 0] with t ht
      exact div_nonneg (Real.exp_pos _).le ht.le
    · filter_upwards [hL.eventually_gt_atTop 0] with t ht
      apply div_le_div_of_nonneg_right _ ht.le
      unfold matrixEnvelope
      have h₁ : 0 ≤ (L t) ^ 2 * Real.exp (5 * ell t / 2 - L t) := by positivity
      have h₂ : 0 ≤ L t * Real.exp (2 * ell t - L t) := by positivity
      linarith
  · exact matrixEnvelope_div_tendsto_zero_of_leading_budget F L ell hL

/-- Elementary logarithmic support gives a vanishing leading budget.
The only hypotheses describe growth of the support; no zeta information is
used in this scalar theorem. No lower restriction on b is needed. -/
theorem leading_budget_tendsto_zero_log_support
    {α : Type*} (F : Filter α) (L ell : α → ℝ) (a b : ℝ)
    (hL : Tendsto L F atTop) (hb : b < 2 / 7)
    (hsupport : ∀ᶠ t in F,
      ell t ≤ a + (2 / 7 : ℝ) * L t + b * Real.log (L t)) :
    Tendsto (fun t => Real.exp (7 * ell t / 2 - L t) / L t) F (nhds 0) := by
  let g : ℝ := 1 - 7 * b / 2
  have hg : 0 < g := by dsimp [g]; linarith
  have hlog := Real.tendsto_log_atTop.comp hL
  have hscale₀ : Tendsto (fun t => Real.log (L t) / (1 / g)) F atTop :=
    hlog.atTop_div_const (by positivity)
  have hscale : Tendsto (fun t => g * Real.log (L t)) F atTop := by
    convert hscale₀ using 1
    funext t
    field_simp [hg.ne']
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hscale
  have hdecay : Tendsto (fun t => Real.exp (-g * Real.log (L t))) F (nhds 0) := by
    convert hp using 1
    funext t
    change Real.exp (-g * Real.log (L t)) =
      (g * Real.log (L t)) ^ 0 * Real.exp (-(g * Real.log (L t)))
    simp only [pow_zero, one_mul]
    congr 1
    ring
  have hmajor : Tendsto (fun t =>
      Real.exp (7 * a / 2) * Real.exp (-g * Real.log (L t))) F (nhds 0) := by
    simpa only [mul_zero] using hdecay.const_mul (Real.exp (7 * a / 2))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [hL.eventually_gt_atTop 0] with t ht
    exact div_nonneg (Real.exp_pos _).le ht.le
  · filter_upwards [hsupport, hL.eventually_gt_atTop 0] with t hs ht
    calc
      _ = Real.exp (7 * ell t / 2 - L t - Real.log (L t)) := by
        conv_rhs => rw [Real.exp_sub, Real.exp_log ht]
      _ ≤ Real.exp (7 * a / 2 + (-g * Real.log (L t))) := by
        apply Real.exp_le_exp.mpr
        dsimp [g]
        nlinarith
      _ = _ := Real.exp_add _ _

end RiemannResearch.Analysis.LandauGrowth
