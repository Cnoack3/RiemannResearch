/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.Auxiliary
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-!
# Differentiable logarithm lifts on compact real intervals

The proof constructs a continuous clamped extension of p'/p, integrates it,
and uses the fundamental theorem of calculus to show exp L = p. Three
rectangle corner values match as complex numbers; the fourth imaginary value
may differ by winding. No logarithm-lift existence hypothesis is assumed.
The strategy supplies the compatible arguments in Chourasiya--Simonic,
arXiv:2507.15184v2, equation (32): https://arxiv.org/html/2507.15184v2.
-/

open Set MeasureTheory
open scoped Interval

namespace Complex

noncomputable def integralLogLift (q : ℝ → ℂ) (a : ℝ) (l0 : ℂ) (t : ℝ) :=
  l0 + ∫ u in a..t, q u

theorem integralLogLift_hasDerivAt {q : ℝ → ℂ} (hq : Continuous q)
    (a : ℝ) (l0 : ℂ) (t : ℝ) :
    HasDerivAt (integralLogLift q a l0) (q t) t := by
  exact (intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a t)
    (hq.stronglyMeasurableAtFilter volume (nhds t)) hq.continuousAt).const_add l0

@[simp] theorem integralLogLift_base (q : ℝ → ℂ) (a : ℝ) (l0 : ℂ) :
    integralLogLift q a l0 a = l0 := by
  simp [integralLogLift]

theorem exp_integralLogLift_eq {p p' q : ℝ → ℂ} {a b : ℝ} {l0 : ℂ}
    (_hab : a ≤ b) (hq : Continuous q)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (hne : ∀ t ∈ Icc a b, p t ≠ 0)
    (hquot : ∀ t ∈ Icc a b, q t = p' t / p t)
    (hbase : exp l0 = p a) :
    ∀ t ∈ Icc a b, exp (integralLogLift q a l0 t) = p t := by
  let L := integralLogLift q a l0
  let Q : ℝ → ℂ := fun t => p t * exp (-L t)
  have hL : ∀ t, HasDerivAt L (q t) t := integralLogLift_hasDerivAt hq a l0
  have hQ : ∀ t ∈ Icc a b, HasDerivAt Q 0 t := by
    intro t ht
    have hd := (hp t ht).mul ((hL t).neg.cexp)
    have heq : p' t * exp (-L t) + p t * (exp (-L t) * (-q t)) = 0 := by
      rw [hquot t ht]
      field_simp [hne t ht]
      ring
    exact hd.congr_deriv heq
  have hQa : Q a = 1 := by
    change p a * exp (-integralLogLift q a l0 a) = 1
    rw [integralLogLift_base, ← hbase, ← exp_add, add_neg_cancel, exp_zero]
  intro t ht
  have hQt : Q t - Q a = 0 := by
    have hzero := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hQ u (by
        rw [uIcc_of_le ht.1] at hu
        exact ⟨hu.1, hu.2.trans ht.2⟩))
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a t)
    simpa only [intervalIntegral.integral_zero] using hzero.symm
  have hQt1 : Q t = 1 := by
    rw [hQa] at hQt
    exact sub_eq_zero.mp hQt
  have he := congrArg (fun z : ℂ => z * exp (L t)) hQt1
  change (p t * exp (-L t)) * exp (L t) = 1 * exp (L t) at he
  simpa only [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] using he.symm

theorem exists_logLift_of_hasDerivAt {p p' : ℝ → ℂ} {a b : ℝ} {l0 : ℂ}
    (hab : a ≤ b) (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc a b))
    (hne : ∀ t ∈ Icc a b, p t ≠ 0) (hbase : exp l0 = p a) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L a = l0 ∧
      (∀ t ∈ Icc a b, exp (L t) = p t) ∧
      (∀ t ∈ Icc a b, HasDerivAt L (p' t / p t) t) := by
  let q : ℝ → ℂ := fun t => p' t / p t
  have hpc : ContinuousOn p (Icc a b) :=
    fun t ht => (hp t ht).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Icc a b) := hp'.div hpc hne
  let c : ℝ → ℝ := fun t => max a (min b t)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hc_mem : ∀ t, c t ∈ Icc a b :=
    fun t => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hc_eq : ∀ t ∈ Icc a b, c t = t := by
    intro t ht
    dsimp [c]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  let q0 : ℝ → ℂ := fun t => q (c t)
  have hq0 : Continuous q0 := hqc.comp_continuous hc hc_mem
  have hquot : ∀ t ∈ Icc a b, q0 t = p' t / p t := by
    intro t ht
    dsimp [q0]
    rw [hc_eq t ht]
  let L := integralLogLift q0 a l0
  have hL : ∀ t, HasDerivAt L (q0 t) t := integralLogLift_hasDerivAt hq0 a l0
  refine ⟨L, continuous_iff_continuousAt.mpr (fun t => (hL t).continuousAt),
    integralLogLift_base q0 a l0, exp_integralLogLift_eq hab hq0 hp hne hquot hbase, ?_⟩
  intro t ht
  rw [← hquot t ht]
  exact hL t

theorem exists_logLift_of_nonzero {p p' : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc a b)) (hne : ∀ t ∈ Icc a b, p t ≠ 0) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L a = log (p a) ∧
      (∀ t ∈ Icc a b, exp (L t) = p t) ∧
      (∀ t ∈ Icc a b, HasDerivAt L (p' t / p t) t) := by
  exact exists_logLift_of_hasDerivAt hab hp hp' hne
    (exp_log (hne a ⟨le_rfl, hab⟩))

theorem logLift_re_eq_log_norm {L p : ℝ → ℂ} {t : ℝ}
    (h : exp (L t) = p t) : (L t).re = Real.log ‖p t‖ := by
  rw [← h, norm_exp, Real.log_exp]

end Complex

open Set

namespace Complex

theorem exists_logLift_at_right {p p' : ℝ → ℂ} {a b : ℝ} {l0 : ℂ}
    (hab : a ≤ b) (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (hp' : ContinuousOn p' (Icc a b))
    (hne : ∀ t ∈ Icc a b, p t ≠ 0) (hbase : exp l0 = p b) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L b = l0 ∧
      (∀ t ∈ Icc a b, exp (L t) = p t) ∧
      (∀ t ∈ Icc a b, HasDerivAt L (p' t / p t) t) := by
  obtain ⟨L, hLc, _, hLe, hLd⟩ := exists_logLift_of_nonzero hab hp hp' hne
  let c := l0 - L b
  have hce : exp c = 1 := by
    dsimp [c]
    rw [exp_sub, hbase, hLe b ⟨hab, le_rfl⟩]
    exact div_self (hne b ⟨hab, le_rfl⟩)
  refine ⟨fun t => c + L t, continuous_const.add hLc, ?_, ?_, ?_⟩
  · dsimp [c]
    exact sub_add_cancel _ _
  · intro t ht
    rw [exp_add, hce, one_mul]
    exact hLe t ht
  · intro t ht
    exact (hLd t ht).const_add c

theorem affine_path_hasDerivAt (v c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * v + c) v t := by
  simpa only [ofReal_one, one_mul] using
    ((Complex.hasDerivAt_ofReal t).mul_const v).add_const c

theorem analytic_affine_path_C1 {F : ℂ → ℂ} {a b : ℝ} (v c : ℂ)
    (hF : ∀ t ∈ Icc a b, AnalyticAt ℂ F ((t : ℂ) * v + c)) :
    (∀ t ∈ Icc a b, HasDerivAt (fun t : ℝ => F ((t : ℂ) * v + c))
      (deriv F ((t : ℂ) * v + c) * v) t) ∧
    ContinuousOn (fun t : ℝ => deriv F ((t : ℂ) * v + c) * v) (Icc a b) := by
  have hzc : Continuous (fun t : ℝ => (t : ℂ) * v + c) := by fun_prop
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (hF t ht).hasStrictDerivAt.hasDerivAt.comp t (affine_path_hasDerivAt v c t)
  · intro t ht
    have hd : ContinuousAt (fun u : ℝ => deriv F ((u : ℂ) * v + c)) t :=
      (hF t ht).deriv.continuousAt.comp (f := fun u : ℝ => (u : ℂ) * v + c)
        (x := t) hzc.continuousAt
    exact (hd.mul continuousAt_const).continuousWithinAt

theorem exists_affine_logLift {F : ℂ → ℂ} {a b : ℝ} {v c l0 : ℂ}
    (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, AnalyticAt ℂ F ((t : ℂ) * v + c))
    (hne : ∀ t ∈ Icc a b, F ((t : ℂ) * v + c) ≠ 0)
    (hbase : exp l0 = F ((a : ℂ) * v + c)) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L a = l0 ∧
      (∀ t ∈ Icc a b, exp (L t) = F ((t : ℂ) * v + c)) ∧
      (∀ t ∈ Icc a b,
        HasDerivAt L (deriv F ((t : ℂ) * v + c) * v / F ((t : ℂ) * v + c)) t) := by
  obtain ⟨hd, hc⟩ := analytic_affine_path_C1 v c hF
  exact exists_logLift_of_hasDerivAt hab hd hc hne hbase

theorem exists_affine_logLift_at_right {F : ℂ → ℂ} {a b : ℝ} {v c l0 : ℂ}
    (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, AnalyticAt ℂ F ((t : ℂ) * v + c))
    (hne : ∀ t ∈ Icc a b, F ((t : ℂ) * v + c) ≠ 0)
    (hbase : exp l0 = F ((b : ℂ) * v + c)) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L b = l0 ∧
      (∀ t ∈ Icc a b, exp (L t) = F ((t : ℂ) * v + c)) ∧
      (∀ t ∈ Icc a b,
        HasDerivAt L (deriv F ((t : ℂ) * v + c) * v / F ((t : ℂ) * v + c)) t) := by
  obtain ⟨hd, hc⟩ := analytic_affine_path_C1 v c hF
  exact exists_logLift_at_right hab hd hc hne hbase

structure IntervalLogLift (p p' : ℝ → ℂ) (a b : ℝ) where
  toFun : ℝ → ℂ
  continuous : Continuous toFun
  exp_eq : ∀ t ∈ Icc a b, exp (toFun t) = p t
  hasDerivAt : ∀ t ∈ Icc a b, HasDerivAt toFun (p' t / p t) t

theorem exists_compatible_fourSide_logLifts
    {pB pR pT pL pB' pR' pT' pL' : ℝ → ℂ} {a b H T : ℝ}
    (hab : a ≤ b) (hHT : H ≤ T)
    (hBd : ∀ x ∈ Icc a b, HasDerivAt pB (pB' x) x)
    (hRd : ∀ y ∈ Icc H T, HasDerivAt pR (pR' y) y)
    (hTd : ∀ x ∈ Icc a b, HasDerivAt pT (pT' x) x)
    (hLd : ∀ y ∈ Icc H T, HasDerivAt pL (pL' y) y)
    (hBc : ContinuousOn pB' (Icc a b))
    (hRc : ContinuousOn pR' (Icc H T))
    (hTc : ContinuousOn pT' (Icc a b))
    (hLc : ContinuousOn pL' (Icc H T))
    (hBn : ∀ x ∈ Icc a b, pB x ≠ 0)
    (hRn : ∀ y ∈ Icc H T, pR y ≠ 0)
    (hTn : ∀ x ∈ Icc a b, pT x ≠ 0)
    (hLn : ∀ y ∈ Icc H T, pL y ≠ 0)
    (hBR : pB b = pR H) (hRT : pR T = pT b)
    (hTL : pT a = pL T) (hLB : pL H = pB a) :
    ∃ B : IntervalLogLift pB pB' a b,
    ∃ R : IntervalLogLift pR pR' H T,
    ∃ U : IntervalLogLift pT pT' a b,
    ∃ L : IntervalLogLift pL pL' H T,
      R.toFun H = B.toFun b ∧ U.toFun b = R.toFun T ∧
      L.toFun T = U.toFun a ∧ (L.toFun H).re = (B.toFun a).re := by
  obtain ⟨B, hBcont, _, hBexp, hBderiv⟩ :=
    exists_logLift_of_nonzero hab hBd hBc hBn
  have hBRexp : exp (B b) = pR H :=
    (hBexp b ⟨hab, le_rfl⟩).trans hBR
  obtain ⟨R, hRcont, hRH, hRexp, hRderiv⟩ :=
    exists_logLift_of_hasDerivAt hHT hRd hRc hRn hBRexp
  have hRTexp : exp (R T) = pT b :=
    (hRexp T ⟨hHT, le_rfl⟩).trans hRT
  obtain ⟨U, hUcont, hUb, hUexp, hUderiv⟩ :=
    exists_logLift_at_right hab hTd hTc hTn hRTexp
  have hTLexp : exp (U a) = pL T :=
    (hUexp a ⟨le_rfl, hab⟩).trans hTL
  obtain ⟨L, hLcont, hLT, hLexp, hLderiv⟩ :=
    exists_logLift_at_right hHT hLd hLc hLn hTLexp
  refine ⟨⟨B, hBcont, hBexp, hBderiv⟩, ⟨R, hRcont, hRexp, hRderiv⟩,
    ⟨U, hUcont, hUexp, hUderiv⟩, ⟨L, hLcont, hLexp, hLderiv⟩,
    hRH, hUb, hLT, ?_⟩
  change (L H).re = (B a).re
  rw [logLift_re_eq_log_norm (hLexp H ⟨le_rfl, hHT⟩),
    logLift_re_eq_log_norm (hBexp a ⟨le_rfl, hab⟩), hLB]

theorem exists_rectangle_fourSide_logLifts {F : ℂ → ℂ} {a b H T : ℝ}
    (hab : a ≤ b) (hHT : H ≤ T)
    (hF : ∀ x ∈ Icc a b, ∀ y ∈ Icc H T,
      AnalyticAt ℂ F ((x : ℂ) + (y : ℂ) * I))
    (hBn : ∀ x ∈ Icc a b, F ((x : ℂ) + (H : ℂ) * I) ≠ 0)
    (hRn : ∀ y ∈ Icc H T, F ((b : ℂ) + (y : ℂ) * I) ≠ 0)
    (hTn : ∀ x ∈ Icc a b, F ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hLn : ∀ y ∈ Icc H T, F ((a : ℂ) + (y : ℂ) * I) ≠ 0) :
    ∃ B : IntervalLogLift
      (fun x => F ((x : ℂ) + (H : ℂ) * I))
      (fun x => deriv F ((x : ℂ) + (H : ℂ) * I)) a b,
    ∃ R : IntervalLogLift
      (fun y => F ((b : ℂ) + (y : ℂ) * I))
      (fun y => deriv F ((b : ℂ) + (y : ℂ) * I) * I) H T,
    ∃ U : IntervalLogLift
      (fun x => F ((x : ℂ) + (T : ℂ) * I))
      (fun x => deriv F ((x : ℂ) + (T : ℂ) * I)) a b,
    ∃ L : IntervalLogLift
      (fun y => F ((a : ℂ) + (y : ℂ) * I))
      (fun y => deriv F ((a : ℂ) + (y : ℂ) * I) * I) H T,
      R.toFun H = B.toFun b ∧ U.toFun b = R.toFun T ∧
      L.toFun T = U.toFun a ∧ (L.toFun H).re = (B.toFun a).re := by
  have hBanalytic : ∀ x ∈ Icc a b, AnalyticAt ℂ F ((x : ℂ) * 1 + (H : ℂ) * I) := by
    intro x hx
    simpa only [mul_one] using hF x hx H ⟨le_rfl, hHT⟩
  have hTanalytic : ∀ x ∈ Icc a b, AnalyticAt ℂ F ((x : ℂ) * 1 + (T : ℂ) * I) := by
    intro x hx
    simpa only [mul_one] using hF x hx T ⟨hHT, le_rfl⟩
  have hRanalytic : ∀ y ∈ Icc H T, AnalyticAt ℂ F ((y : ℂ) * I + (b : ℂ)) := by
    intro y hy
    simpa only [add_comm] using hF b ⟨hab, le_rfl⟩ y hy
  have hLanalytic : ∀ y ∈ Icc H T, AnalyticAt ℂ F ((y : ℂ) * I + (a : ℂ)) := by
    intro y hy
    simpa only [add_comm] using hF a ⟨le_rfl, hab⟩ y hy
  obtain ⟨hBd, hBc⟩ := analytic_affine_path_C1 1 ((H : ℂ) * I) hBanalytic
  obtain ⟨hTd, hTc⟩ := analytic_affine_path_C1 1 ((T : ℂ) * I) hTanalytic
  obtain ⟨hRd, hRc⟩ := analytic_affine_path_C1 I (b : ℂ) hRanalytic
  obtain ⟨hLd, hLc⟩ := analytic_affine_path_C1 I (a : ℂ) hLanalytic
  simp only [mul_one] at hBd hBc hTd hTc
  simp only [add_comm] at hRd hRc hLd hLc
  exact exists_compatible_fourSide_logLifts hab hHT hBd hRd hTd hLd
    hBc hRc hTc hLc hBn hRn hTn hLn rfl rfl rfl rfl

end Complex
