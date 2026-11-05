/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeFractionalMellin
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Multiplicities of finite and limiting conductor readouts
Equation (16), counting analytic multiplicity. The full Mellin integrals
are divided by any fixed nonzero scalar, in particular by their mass on
the vertical line used to define a probability law. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RiemannResearch.RH.PrimeTreeMellinLaws

private theorem unit_order (H V : ℂ → ℂ) (s : ℂ) (hs1 : s ≠ 1)
    (hV : AnalyticAt ℂ V s) (hne : V s ≠ 0) (he : H =ᶠ[𝓝 s] riemannZeta * V) :
    analyticOrderAt H s = analyticOrderAt riemannZeta s := by
  have hz : AnalyticAt ℂ riemannZeta s := by
    apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ)) _ (isOpen_compl_singleton.mem_nhds hs1)
    exact fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hz hV,
    analyticOrderAt_eq_zero.mpr (Or.inr hne), add_zero]

private theorem strip_nhds (s : ℂ) (hs : 0 < s.re) (hlt : s.re < 1) :
    ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re ∧ z.re < 1 :=
  ((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hs, hlt⟩

theorem fract_order (c s : ℂ) (hc : c ≠ 0) (hs : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (fun z => mellin (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) (-z) / c) s =
      analyticOrderAt riemannZeta s := by
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; norm_num at hlt
  let V (z : ℂ) := -z⁻¹ / c
  apply unit_order _ V s h₁
  · exact (analyticAt_id.inv h₀).neg.div analyticAt_const hc
  · exact div_ne_zero (neg_ne_zero.mpr (inv_ne_zero h₀)) hc
  · filter_upwards [strip_nhds s hs hlt] with z hz
    rw [mellin_fract_zeta z hz.1 hz.2]
    simp only [Pi.mul_apply, V, div_eq_mul_inv]
    ring

theorem staircase_order (D : ℕ) (hD : 1 < D) (c s : ℂ) (hc : c ≠ 0)
    (hs : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (fun z => mellin (fun x : ℝ => (staircase D x : ℂ)) (-z) / c) s =
      analyticOrderAt riemannZeta s := by
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; norm_num at hlt
  have hd : 0 < D := by omega
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hDr : (1 : ℝ) < D := by exact_mod_cast hD
  let B (z : ℂ) := (1 - (D : ℂ) ^ (z - 1))
  have hB : Differentiable ℂ B := by
    intro z
    have hcons : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) z := by fun_prop
    have hlin : DifferentiableAt ℂ (fun q : ℂ => q - 1) z := by fun_prop
    exact hcons.sub (hlin.const_cpow (Or.inl hDc))
  have hne : B s ≠ 0 := by
    intro ee
    have hh := (sub_eq_zero.mp ee).symm
    have hn : ‖(D : ℂ) ^ (s - 1)‖ < 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hDr)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hDr (by simpa using sub_neg.mpr hlt)
    simpa [hh] using hn
  let V (z : ℂ) := B z * (-z⁻¹ / c)
  apply unit_order _ V s h₁
  · exact (hB.analyticAt s).mul ((analyticAt_id.inv h₀).neg.div analyticAt_const hc)
  · exact mul_ne_zero hne (div_ne_zero (neg_ne_zero.mpr (inv_ne_zero h₀)) hc)
  · filter_upwards [strip_nhds s hs hlt] with z hz
    have hz₁ : z ≠ 1 := by rintro rfl; simpa using hz.2
    rw [mellin_staircase_zeta D hd z hz.1 hz₁]
    simp only [Pi.mul_apply, V, B, div_eq_mul_inv]
    ring

end RiemannResearch.RH.PrimeTreeMellinLaws
