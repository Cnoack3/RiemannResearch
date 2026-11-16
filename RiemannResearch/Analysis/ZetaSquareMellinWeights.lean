/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.SymmetricZetaRatio
import RiemannResearch.Analysis.DampedGammaStripBounds
import RiemannResearch.Analysis.VerticalResidueShift
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Hardy.EFContour.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr

/-!
# Full-line weights for the two zeta-square Mellin contours

The quarter-line chi bounds hold at every height, including zero.
They yield uniform translated bounds on a dyadic t-window for every
vertical integration variable v. A polynomially weighted Gamma norm
is integrable, so these bounds avoid a separate near/far decomposition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis.SymmetricZetaRatio

theorem continuous_chiFE_vertical {σ : ℝ} (hσ : σ < 1) :
    Continuous (fun t : ℝ => Zeta23.XiPrime.chiFE ((σ : ℂ) + I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hr : (((σ : ℂ) + I * t)).re < 3 := by simp; linarith
  have h1 : (σ : ℂ) + I * t ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  exact (Zeta23.XiPrime.Hardy.EFContour.chiFE_analyticAt'
    (Zeta23.XiPrime.Hardy.EFContour.Gammaℝ_one_sub_ne_zero_of_re hr h1)).continuousAt.comp
      (f := fun t : ℝ => (σ : ℂ) + I * t) (by fun_prop)

private theorem continuous_weighted_bound_of_tail {f : ℝ → ℂ} {w : ℝ → ℝ}
    (hf : Continuous f) (hw : Continuous w) (hwpos : ∀ t, 0 < w t)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 1 ≤ |t| → ‖f t‖ ≤ C * w t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖f t‖ ≤ D * w t := by
  have hc : Continuous (fun t : ℝ => ‖f t‖ / w t) :=
    hf.norm.div hw (fun t => (hwpos t).ne')
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hc.continuousOn
  refine ⟨max C M, hC.trans (le_max_left _ _), ?_⟩
  intro t
  by_cases ht : 1 ≤ |t|
  · exact (hbound t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hwpos t).le)
  · have hmem : t ∈ Icc (-1 : ℝ) 1 := (abs_le.mp (le_of_lt (lt_of_not_ge ht)))
    have hq : ‖f t‖ / w t ≤ M :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hM t hmem)
    exact ((div_le_iff₀ (hwpos t)).mp hq).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hwpos t).le)

private theorem exp_five_div_sq_le_global {t : ℝ} (ht : 1 ≤ |t|) :
    Real.exp (5 / t ^ 2) ≤ Real.exp 5 := by
  have ht2 : (1 : ℝ) ≤ t ^ 2 := by
    simpa only [one_pow, sq_abs] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht 2
  apply Real.exp_le_exp.mpr
  exact (div_le_iff₀ (by linarith : 0 < t ^ 2)).mpr (by nlinarith)

/-- Global left-line growth, including the real-axis point. -/
theorem exists_chiFE_neg_quarter_global_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖Zeta23.XiPrime.chiFE ((-1 / 4 : ℂ) + I * t)‖ ≤
        C * (1 + |t|) ^ (3 / 4 : ℝ) := by
  refine continuous_weighted_bound_of_tail
    (f := fun t : ℝ => Zeta23.XiPrime.chiFE ((-1/4 : ℂ) + I * t))
    (w := fun t : ℝ => (1+|t|) ^ (3/4 : ℝ))
    (by convert continuous_chiFE_vertical (σ := -1/4) (by norm_num) using 1; norm_num)
    ((show Continuous (fun t : ℝ => 1+|t|) from
      continuous_const.add continuous_abs).rpow_const
      (fun t => Or.inl (by positivity)))
    (fun t => Real.rpow_pos_of_pos (by positivity) _)
    (C := 2 * Real.pi ^ (-3/4 : ℝ) * Real.exp 5) (by positivity) ?_
  intro t ht
  apply (norm_chiFE_neg_quarter_le ht).trans
  gcongr
  · exact Real.exp_le_exp.mp (exp_five_div_sq_le_global ht)
  · linarith [abs_nonneg t]

/-- Global right-line decay, including the real-axis point. -/
theorem exists_chiFE_three_quarters_global_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖Zeta23.XiPrime.chiFE ((3 / 4 : ℂ) + I * t)‖ ≤
        C * (1 + |t|) ^ (-1 / 4 : ℝ) := by
  refine continuous_weighted_bound_of_tail
    (f := fun t : ℝ => Zeta23.XiPrime.chiFE ((3/4 : ℂ) + I * t))
    (w := fun t : ℝ => (1+|t|) ^ (-1/4 : ℝ))
    (by convert continuous_chiFE_vertical (σ := 3/4) (by norm_num) using 1; norm_num)
    ((show Continuous (fun t : ℝ => 1+|t|) from
      continuous_const.add continuous_abs).rpow_const
      (fun t => Or.inl (by positivity)))
    (fun t => Real.rpow_pos_of_pos (by positivity) _)
    (C := Real.pi ^ (1/4 : ℝ) * Real.exp 5 * (1/4 : ℝ) ^ (-1/4 : ℝ))
    (by positivity) ?_
  intro t ht
  have hp : (|t|/2) ^ (-1/4 : ℝ) ≤
      ((1/4 : ℝ) * (1+|t|)) ^ (-1/4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  calc
    _ ≤ Real.pi ^ (1/4 : ℝ) *
        (Real.exp (5/t^2) * (|t|/2) ^ (-1/4 : ℝ)) :=
      norm_chiFE_three_quarters_le ht
    _ ≤ Real.pi ^ (1/4 : ℝ) *
        (Real.exp 5 * ((1/4 : ℝ) * (1+|t|)) ^ (-1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (exp_five_div_sq_le_global ht) hp
          (by positivity) (by positivity)) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/4) (by positivity : 0 ≤ 1+|t|)]
      ring

/-- Left-line estimate on the entire vertical integration line. -/
theorem exists_chiFE_neg_quarter_translated_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U t v : ℝ, 1 ≤ U → t ∈ Icc U (2*U) →
      ‖Zeta23.XiPrime.chiFE ((-1/4 : ℂ) + I * ((t+v : ℝ) : ℂ))‖ ≤
        C * U ^ (3/4 : ℝ) * (1+|v|) ^ (3/4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_chiFE_neg_quarter_global_bound
  refine ⟨C * (3 : ℝ) ^ (3/4 : ℝ), by positivity, ?_⟩
  intro U t v hU ht
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hab : 1 + |t+v| ≤ (3*U) * (1+|v|) := by
    have hh := abs_add_le t v
    rw [abs_of_nonneg ht0] at hh
    nlinarith [abs_nonneg v, mul_nonneg (by linarith : 0 ≤ U-1) (abs_nonneg v), ht.2]
  calc
    _ ≤ C * (1+|t+v|) ^ (3/4 : ℝ) := hbound (t+v)
    _ ≤ C * ((3*U) * (1+|v|)) ^ (3/4 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hab (by norm_num)) hC
    _ = (C * (3 : ℝ) ^ (3/4 : ℝ)) * U ^ (3/4 : ℝ) *
        (1+|v|) ^ (3/4 : ℝ) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 3*U) (by positivity : 0 ≤ 1+|v|),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by linarith : 0 ≤ U)]
      ring

/-- Right-line decay remains uniform even when t+v crosses zero. -/
theorem exists_chiFE_three_quarters_translated_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U t v : ℝ, 1 ≤ U → U ≤ t →
      ‖Zeta23.XiPrime.chiFE ((3/4 : ℂ) + I * ((t+v : ℝ) : ℂ))‖ ≤
        C * U ^ (-1/4 : ℝ) * (1+|v|) ^ (1/4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_chiFE_three_quarters_global_bound
  refine ⟨C, hC, ?_⟩
  intro U t v hU ht
  have hbase : U / (1+|v|) ≤ 1+|t+v| := by
    apply (div_le_iff₀ (by positivity : 0 < 1+|v|)).mpr
    have hab := abs_add_le (t+v) (-v)
    simp only [add_neg_cancel_right, abs_neg] at hab
    have ht0 : 0 ≤ t := by linarith
    rw [abs_of_nonneg ht0] at hab
    nlinarith [abs_nonneg (t+v), abs_nonneg v,
      mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v)]
  have hp : (1+|t+v|) ^ (-1/4 : ℝ) ≤
      (U / (1+|v|)) ^ (-1/4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
  calc
    _ ≤ C * (1+|t+v|) ^ (-1/4 : ℝ) := hbound (t+v)
    _ ≤ C * (U / (1+|v|)) ^ (-1/4 : ℝ) :=
      mul_le_mul_of_nonneg_left hp hC
    _ = C * U ^ (-1/4 : ℝ) * (1+|v|) ^ (1/4 : ℝ) := by
      rw [Real.div_rpow (by linarith : 0 ≤ U) (by positivity : 0 ≤ 1+|v|),
        div_eq_mul_inv, ← Real.rpow_neg (by positivity : 0 ≤ 1+|v|)]
      norm_num
      ring


private theorem sq_rpow_eq_rpow_double {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    (x ^ r) ^ 2 = x ^ (r * 2) := by
  rw [← Real.rpow_natCast (x ^ r) 2, ← Real.rpow_mul hx]
  norm_num

/-- A common quadratic vertical weight controls the squared left chi factor. -/
theorem exists_chiFE_neg_quarter_square_translated_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U t v : ℝ, 1 ≤ U → t ∈ Icc U (2 * U) →
      ‖Zeta23.XiPrime.chiFE ((-1/4 : ℂ) + I * ((t+v : ℝ) : ℂ)) ^ 2‖ ≤
        C * U ^ (3/2 : ℝ) * (1+|v|)^2 := by
  obtain ⟨C, hC, hb⟩ := exists_chiFE_neg_quarter_translated_bound
  refine ⟨C^2, sq_nonneg C, ?_⟩
  intro U t v hU ht
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hb U t v hU ht) 2
  rw [mul_pow, mul_pow,
    sq_rpow_eq_rpow_double (by linarith : 0 ≤ U),
    sq_rpow_eq_rpow_double (by positivity : 0 ≤ 1+|v|)] at hh
  simp only [norm_pow]
  norm_num at hh ⊢
  apply hh.trans
  gcongr
  calc
    (1+|v|) ^ (3/2 : ℝ) ≤ (1+|v|) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by norm_num)
    _ = _ := Real.rpow_natCast _ 2

/-- A common quadratic vertical weight controls the squared right chi factor. -/
theorem exists_chiFE_three_quarters_square_translated_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U t v : ℝ, 1 ≤ U → U ≤ t →
      ‖Zeta23.XiPrime.chiFE ((3/4 : ℂ) + I * ((t+v : ℝ) : ℂ)) ^ 2‖ ≤
        C * U ^ (-1/2 : ℝ) * (1+|v|)^2 := by
  obtain ⟨C, hC, hb⟩ := exists_chiFE_three_quarters_translated_bound
  refine ⟨C^2, sq_nonneg C, ?_⟩
  intro U t v hU ht
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hb U t v hU ht) 2
  rw [mul_pow, mul_pow,
    sq_rpow_eq_rpow_double (by linarith : 0 ≤ U),
    sq_rpow_eq_rpow_double (by positivity : 0 ≤ 1+|v|)] at hh
  simp only [norm_pow]
  norm_num at hh ⊢
  apply hh.trans
  gcongr
  calc
    (1+|v|) ^ (1/2 : ℝ) ≤ (1+|v|) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by norm_num)
    _ = _ := Real.rpow_natCast _ 2

end RiemannResearch.Analysis.SymmetricZetaRatio
