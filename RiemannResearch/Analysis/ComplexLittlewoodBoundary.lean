/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexIntegralLogLift
import RiemannResearch.Analysis.ComplexLogRectangleBoundary
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ResidueCalcOnRectangles
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# The full signed Littlewood rectangle boundary identity

Chourasiya--Simonic, arXiv:2507.15184v2, equation (32), supports the statement:
https://arxiv.org/html/2507.15184v2. The proof here uses interval integration
by parts, constructed logarithm lifts and the normalized rectangle contour.
All four signed terms remain. The weight vanishes at the starting corner,
so no false closure of the logarithm around interior zeros is required.
Analyticity on the closed rectangle and nonvanishing on its border are the
explicit domain conditions; quantitative boundary estimates are separate.
-/

noncomputable section
open Complex Set MeasureTheory intervalIntegral

namespace Complex

/-- The three corner matches suffice. No bottom-left closure is required. -/
theorem weightedRectangleIntegral_eq_logLifts (F : ℂ → ℂ)
    (B U R L : ℝ → ℂ) (α β H T : ℝ)
    (hB : ∀ u ∈ Set.uIcc α β, HasDerivAt B
      (logDeriv F ((u : ℂ) + (H : ℂ) * I)) u)
    (hU : ∀ u ∈ Set.uIcc α β, HasDerivAt U
      (logDeriv F ((u : ℂ) + (T : ℂ) * I)) u)
    (hR : ∀ t ∈ Set.uIcc H T, HasDerivAt R
      (I * logDeriv F ((β : ℂ) + (t : ℂ) * I)) t)
    (hL : ∀ t ∈ Set.uIcc H T, HasDerivAt L
      (I * logDeriv F ((α : ℂ) + (t : ℂ) * I)) t)
    (hBi : IntervalIntegrable (fun u => logDeriv F ((u : ℂ) + (H : ℂ) * I)) volume α β)
    (hUi : IntervalIntegrable (fun u => logDeriv F ((u : ℂ) + (T : ℂ) * I)) volume α β)
    (hRi : IntervalIntegrable (fun t => I * logDeriv F ((β : ℂ) + (t : ℂ) * I)) volume H T)
    (hLi : IntervalIntegrable (fun t => I * logDeriv F ((α : ℂ) + (t : ℂ) * I)) volume H T)
    (hBR : B β = R H) (hRU : R T = U β) (hUL : U α = L T) :
    RectangleIntegral
      (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv F s)
      ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I) =
      -(∫ u in α..β, B u) + (∫ u in α..β, U u)-
        I * (∫ t in H..T, R t) + I * (∫ t in H..T, L t) := by
  let z : ℂ := (α : ℂ) + (H : ℂ) * I
  let gb : ℝ → ℂ := fun u => (u : ℂ) + (H : ℂ) * I - z
  let gu : ℝ → ℂ := fun u => (u : ℂ) + (T : ℂ) * I - z
  let gr : ℝ → ℂ := fun t => (β : ℂ) + (t : ℂ) * I - z
  let gl : ℝ → ℂ := fun t => (α : ℂ) + (t : ℂ) * I - z
  have hgb : ∀ u ∈ Set.uIcc α β, HasDerivAt gb 1 u := by
    intro u hu
    simpa [gb] using ((Complex.hasDerivAt_ofReal u).add_const ((H : ℂ) * I)).sub_const z
  have hgu : ∀ u ∈ Set.uIcc α β, HasDerivAt gu 1 u := by
    intro u hu
    simpa [gu] using ((Complex.hasDerivAt_ofReal u).add_const ((T : ℂ) * I)).sub_const z
  have hgr : ∀ t ∈ Set.uIcc H T, HasDerivAt gr I t := by
    intro t ht
    simpa [gr] using (((Complex.hasDerivAt_ofReal t).mul_const I).const_add (β : ℂ)).sub_const z
  have hgl : ∀ t ∈ Set.uIcc H T, HasDerivAt gl I t := by
    intro t ht
    simpa [gl] using (((Complex.hasDerivAt_ofReal t).mul_const I).const_add (α : ℂ)).sub_const z
  have eb := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgb hB
    intervalIntegrable_const hBi
  have eu := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgu hU
    intervalIntegrable_const hUi
  have er := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgr hR
    intervalIntegrable_const hRi
  have el := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgl hL
    intervalIntegrable_const hLi
  simp only [one_mul] at eb eu
  rw [intervalIntegral.integral_const_mul] at er el
  have er' : I * (∫ t in H..T, gr t * logDeriv F ((β : ℂ) + (t : ℂ) * I)) =
      gr T * R T - gr H * R H - I * (∫ t in H..T, R t) := by
    calc
      _ = ∫ t in H..T, I * (gr t * logDeriv F ((β : ℂ) + (t : ℂ) * I)) :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ t in H..T, gr t * (I * logDeriv F ((β : ℂ) + (t : ℂ) * I)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := er
  have el' : I * (∫ t in H..T, gl t * logDeriv F ((α : ℂ) + (t : ℂ) * I)) =
      gl T * L T - gl H * L H - I * (∫ t in H..T, L t) := by
    calc
      _ = ∫ t in H..T, I * (gl t * logDeriv F ((α : ℂ) + (t : ℂ) * I)) :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ t in H..T, gl t * (I * logDeriv F ((α : ℂ) + (t : ℂ) * I)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := el
  simp only [RectangleIntegral, HIntegral, VIntegral, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, zero_add, mul_one, smul_eq_mul]
  change (∫ u in α..β, gb u * logDeriv F ((u : ℂ) + (H : ℂ) * I))-
      (∫ u in α..β, gu u * logDeriv F ((u : ℂ) + (T : ℂ) * I)) +
      I * (∫ t in H..T, gr t * logDeriv F ((β : ℂ) + (t : ℂ) * I))-
      I * (∫ t in H..T, gl t * logDeriv F ((α : ℂ) + (t : ℂ) * I)) = _
  rw [eb, eu, er', el', hBR, hRU, hUL]
  simp [gb, gu, gr, gl, z]
  ring

theorem weightedRectangleIntegral_im_eq_logRectangleBoundary (F : ℂ → ℂ)
    (B U R L : ℝ → ℂ) (α β H T : ℝ)
    (hcomplex : RectangleIntegral
      (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv F s)
      ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I) =
      -(∫ u in α..β, B u) + (∫ u in α..β, U u)-
        I * (∫ t in H..T, R t) + I * (∫ t in H..T, L t))
    (hBi : IntervalIntegrable B volume α β) (hUi : IntervalIntegrable U volume α β)
    (hRi : IntervalIntegrable R volume H T) (hLi : IntervalIntegrable L volume H T)
    (hRre : ∀ t ∈ Set.uIcc H T, (R t).re = Real.log ‖F ((β : ℂ) + (t : ℂ) * I)‖)
    (hLre : ∀ t ∈ Set.uIcc H T, (L t).re = Real.log ‖F ((α : ℂ) + (t : ℂ) * I)‖) :
    (RectangleIntegral
      (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv F s)
      ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I)).im =
      logRectangleBoundary F (fun u => (B u).im) (fun u => (U u).im) α β H T := by
  have eb : (∫ u in α..β, (B u).im) = (∫ u in α..β, B u).im :=
    Complex.imCLM.intervalIntegral_comp_comm hBi
  have eu : (∫ u in α..β, (U u).im) = (∫ u in α..β, U u).im :=
    Complex.imCLM.intervalIntegral_comp_comm hUi
  have er : (∫ t in H..T, (R t).re) = (∫ t in H..T, R t).re :=
    Complex.reCLM.intervalIntegral_comp_comm hRi
  have el : (∫ t in H..T, (L t).re) = (∫ t in H..T, L t).re :=
    Complex.reCLM.intervalIntegral_comp_comm hLi
  have erlog : (∫ t in H..T, (R t).re) =
      (∫ t in H..T, Real.log ‖F ((β : ℂ) + (t : ℂ) * I)‖) := by
    apply intervalIntegral.integral_congr
    exact hRre
  have ellog : (∫ t in H..T, (L t).re) =
      (∫ t in H..T, Real.log ‖F ((α : ℂ) + (t : ℂ) * I)‖) := by
    apply intervalIntegral.integral_congr
    exact hLre
  rw [hcomplex]
  simp only [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  unfold logRectangleBoundary
  rw [← eb, ← eu, ← er, ← el, erlog, ellog]
  ring

end Complex

noncomputable section
open Complex Set MeasureTheory intervalIntegral

namespace Complex

theorem rectangleIntegral'_re_eq_im_div (f : ℂ → ℂ) (z w : ℂ) :
    (RectangleIntegral' f z w).re = (RectangleIntegral f z w).im / (2 * Real.pi) := by
  unfold RectangleIntegral'
  rw [smul_eq_mul]
  have he : (1 / (2 * (Real.pi : ℂ) * I)) * RectangleIntegral f z w =
      RectangleIntegral f z w / (2 * (Real.pi : ℂ) * I) := by
    rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]
    exact mul_comm _ _
  rw [he, Complex.div_re]
  simp [Complex.normSq_apply]
  field_simp [Real.pi_ne_zero]

theorem exists_logRectangleBoundary_eq_contour {F : ℂ → ℂ} {a b H T : ℝ}
    (hab : a ≤ b) (hHT : H ≤ T)
    (hf : AnalyticOnNhd ℂ F
      (Rectangle ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I)))
    (hborder : ∀ s ∈ RectangleBorder
      ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I), F s ≠ 0) :
    ∃ B U : ℝ → ℂ, Continuous B ∧ Continuous U ∧
      (∀ x ∈ Icc a b, exp (B x) = F ((x : ℂ) + (H : ℂ) * I)) ∧
      (∀ x ∈ Icc a b, exp (U x) = F ((x : ℂ) + (T : ℂ) * I)) ∧
      (RectangleIntegral'
        (fun s => (s - ((a : ℂ) + (H : ℂ) * I)) * logDeriv F s)
        ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I)).re =
      logRectangleBoundary F (fun x => (B x).im) (fun x => (U x).im) a b H T /
        (2 * Real.pi) := by
  let z : ℂ := (a : ℂ) + (H : ℂ) * I
  let w : ℂ := (b : ℂ) + (T : ℂ) * I
  have hBmem : ∀ x ∈ uIcc a b, (x : ℂ) + (H : ℂ) * I ∈ RectangleBorder z w := by
    intro x hx
    exact Or.inl (Or.inl (Or.inl ⟨by simpa [z, w] using hx, by simp [z]⟩))
  have hUmem : ∀ x ∈ uIcc a b, (x : ℂ) + (T : ℂ) * I ∈ RectangleBorder z w := by
    intro x hx
    exact Or.inl (Or.inr ⟨by simpa [z, w] using hx, by simp [w]⟩)
  have hRmem : ∀ y ∈ uIcc H T, (b : ℂ) + (y : ℂ) * I ∈ RectangleBorder z w := by
    intro y hy
    exact Or.inr ⟨by simp [w], by simpa [z, w] using hy⟩
  have hLmem : ∀ y ∈ uIcc H T, (a : ℂ) + (y : ℂ) * I ∈ RectangleBorder z w := by
    intro y hy
    exact Or.inl (Or.inl (Or.inr ⟨by simp [z], by simpa [z, w] using hy⟩))
  have hanalytic : ∀ x ∈ Icc a b, ∀ y ∈ Icc H T,
      AnalyticAt ℂ F ((x : ℂ) + (y : ℂ) * I) := by
    intro x hx y hy
    apply hf
    apply (mem_Rect (by simpa [z, w] using hab) (by simpa [z, w] using hHT) _).mpr
    simpa [z, w] using (show a ≤ x ∧ x ≤ b ∧ H ≤ y ∧ y ≤ T from
      ⟨hx.1, hx.2, hy.1, hy.2⟩)
  have hBn : ∀ x ∈ Icc a b, F ((x : ℂ) + (H : ℂ) * I) ≠ 0 := by
    intro x hx
    exact hborder _ (hBmem x (by simpa [uIcc_of_le hab] using hx))
  have hUn : ∀ x ∈ Icc a b, F ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro x hx
    exact hborder _ (hUmem x (by simpa [uIcc_of_le hab] using hx))
  have hRn : ∀ y ∈ Icc H T, F ((b : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy
    exact hborder _ (hRmem y (by simpa [uIcc_of_le hHT] using hy))
  have hLn : ∀ y ∈ Icc H T, F ((a : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy
    exact hborder _ (hLmem y (by simpa [uIcc_of_le hHT] using hy))
  obtain ⟨B, R, U, L, hBR, hRU, hUL, _⟩ :=
    exists_rectangle_fourSide_logLifts hab hHT hanalytic hBn hRn hUn hLn
  have hBd : ∀ x ∈ uIcc a b,
      HasDerivAt B.toFun (logDeriv F ((x : ℂ) + (H : ℂ) * I)) x := by
    simpa only [uIcc_of_le hab, logDeriv, Pi.div_apply] using B.hasDerivAt
  have hUd : ∀ x ∈ uIcc a b,
      HasDerivAt U.toFun (logDeriv F ((x : ℂ) + (T : ℂ) * I)) x := by
    simpa only [uIcc_of_le hab, logDeriv, Pi.div_apply] using U.hasDerivAt
  have hRd : ∀ y ∈ uIcc H T,
      HasDerivAt R.toFun (I * logDeriv F ((b : ℂ) + (y : ℂ) * I)) y := by
    intro y hy
    have hd := R.hasDerivAt y (by simpa [uIcc_of_le hHT] using hy)
    exact hd.congr_deriv (by simp only [logDeriv, Pi.div_apply, div_eq_mul_inv]; ring)
  have hLd : ∀ y ∈ uIcc H T,
      HasDerivAt L.toFun (I * logDeriv F ((a : ℂ) + (y : ℂ) * I)) y := by
    intro y hy
    have hd := L.hasDerivAt y (by simpa [uIcc_of_le hHT] using hy)
    exact hd.congr_deriv (by simp only [logDeriv, Pi.div_apply, div_eq_mul_inv]; ring)
  have hlog : ∀ s ∈ RectangleBorder z w, ContinuousAt (logDeriv F) s := by
    intro s hs
    have ha := hf s (rectangleBorder_subset_rectangle z w hs)
    simpa only [logDeriv] using ha.deriv.continuousAt.div ha.continuousAt (hborder s hs)
  have hBi : IntervalIntegrable (fun x => logDeriv F ((x : ℂ) + (H : ℂ) * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact ((hlog _ (hBmem x hx)).comp
      (f := fun u : ℝ => (u : ℂ) + (H : ℂ) * I) (x := x) (by fun_prop)).continuousWithinAt
  have hUi : IntervalIntegrable (fun x => logDeriv F ((x : ℂ) + (T : ℂ) * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact ((hlog _ (hUmem x hx)).comp
      (f := fun u : ℝ => (u : ℂ) + (T : ℂ) * I) (x := x) (by fun_prop)).continuousWithinAt
  have hRi : IntervalIntegrable (fun y => I * logDeriv F ((b : ℂ) + (y : ℂ) * I)) volume H T := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact (continuousAt_const.mul ((hlog _ (hRmem y hy)).comp
      (f := fun t : ℝ => (b : ℂ) + (t : ℂ) * I) (x := y) (by fun_prop))).continuousWithinAt
  have hLi : IntervalIntegrable (fun y => I * logDeriv F ((a : ℂ) + (y : ℂ) * I)) volume H T := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact (continuousAt_const.mul ((hlog _ (hLmem y hy)).comp
      (f := fun t : ℝ => (a : ℂ) + (t : ℂ) * I) (x := y) (by fun_prop))).continuousWithinAt
  have he := weightedRectangleIntegral_eq_logLifts F B.toFun U.toFun R.toFun L.toFun a b H T
    hBd hUd hRd hLd hBi hUi hRi hLi hBR.symm hRU.symm hUL.symm
  have him := weightedRectangleIntegral_im_eq_logRectangleBoundary F B.toFun U.toFun R.toFun L.toFun a b H T
    he (B.continuous.intervalIntegrable a b) (U.continuous.intervalIntegrable a b)
    (R.continuous.intervalIntegrable H T) (L.continuous.intervalIntegrable H T)
    (fun y hy => logLift_re_eq_log_norm (L := R.toFun)
      (p := fun t => F ((b : ℂ) + (t : ℂ) * I)) (t := y)
      (R.exp_eq y (by simpa [uIcc_of_le hHT] using hy)))
    (fun y hy => logLift_re_eq_log_norm (L := L.toFun)
      (p := fun t => F ((a : ℂ) + (t : ℂ) * I)) (t := y)
      (L.exp_eq y (by simpa [uIcc_of_le hHT] using hy)))
  refine ⟨B.toFun, U.toFun, B.continuous, U.continuous, B.exp_eq, U.exp_eq, ?_⟩
  rw [rectangleIntegral'_re_eq_im_div, him]

end Complex
