/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual Landau sums across height windows

Exact complete signed window increments come first. Reflection gives the sharper
cosh bound; the actual Riemann--von Mangoldt local count then controls arbitrary
short windows. All analytic multiplicities and both cutoff conventions remain.
Source: existing actual-zero reflection and RvM.zeta_local_zero_count providers;
the short-height bridge is the standard Landau contour argument.
-/

noncomputable section
open Zeta23 Complex
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Complete signed increment, retaining every actual zero and multiplicity. -/
theorem sum_sub_eq_window_sum (T R : ℝ) (hT : 0 ≤ T) (hTR : T ≤ R)
    (f : ℂ → ℂ) :
    sum R f - sum T f =
      ∑ ρ ∈ (zerosIn_finite T R).toFinset, (zeroMult ρ : ℂ) * f ρ := by
  classical
  have hu : cutoff R = cutoff T ∪ (zerosIn_finite T R).toFinset := by
    ext ρ
    simp only [cutoff, Set.Finite.mem_toFinset, Finset.mem_union,
      zerosIn_union hT hTR, Set.mem_union]
  have hd : Disjoint (cutoff T) (zerosIn_finite T R).toFinset := by
    rw [Finset.disjoint_left]
    intro ρ hρT hρW
    have hρT' := mem_cutoff.mp hρT
    have hρW' : ρ ∈ zerosIn T R := (zerosIn_finite T R).mem_toFinset.mp hρW
    exact (not_lt_of_ge hρT'.2.2) hρW'.2.1
  unfold sum
  rw [hu, Finset.sum_union hd]
  ring

theorem centeredExp_norm_le_strip {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ cutoff R) (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * (ρ - 1 / 2))‖ ≤ Real.exp (|u| / 2) := by
  rw [exp_centered_eq, norm_mul, ZeroOrdinate.phase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |u * (ρ.re - 1 / 2)| := le_abs_self _
    _ = |u| * |ρ.re - 1 / 2| := abs_mul _ _
    _ ≤ |u| / 2 := by
      have h := (displacement_lt_half hρ).le
      nlinarith [abs_nonneg u, mul_le_mul_of_nonneg_left h (abs_nonneg u)]

theorem landauSum_sub_eq_window_sum (T R u : ℝ) (hT : 0 ≤ T) (hTR : T ≤ R) :
    landauSum R u - landauSum T u =
      ∑ ρ ∈ (zerosIn_finite T R).toFinset,
        (zeroMult ρ : ℂ) * Complex.exp ((u : ℂ) * (ρ - 1 / 2)) :=
  sum_sub_eq_window_sum T R hT hTR _

/-- Actual height-transfer estimate without selecting good contour heights. -/
theorem landauSum_height_difference_norm_le (T R u : ℝ)
    (hT : 0 ≤ T) (hTR : T ≤ R) :
    ‖landauSum R u - landauSum T u‖ ≤
      Real.exp (|u| / 2) * (Ncount T R : ℝ) := by
  classical
  have hcount : (Ncount T R : ℝ) =
      ∑ ρ ∈ (zerosIn_finite T R).toFinset, (zeroMult ρ : ℝ) := by
    rw [Ncount, finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite T R),
      Nat.cast_sum]
  rw [landauSum_sub_eq_window_sum T R u hT hTR]
  calc
    _ ≤ ∑ ρ ∈ (zerosIn_finite T R).toFinset,
        ‖(zeroMult ρ : ℂ) * Complex.exp ((u : ℂ) * (ρ - 1 / 2))‖ :=
      _root_.norm_sum_le _ _
    _ = ∑ ρ ∈ (zerosIn_finite T R).toFinset,
        (zeroMult ρ : ℝ) * ‖Complex.exp ((u : ℂ) * (ρ - 1 / 2))‖ := by
      simp only [norm_mul, Complex.norm_natCast]
    _ ≤ ∑ ρ ∈ (zerosIn_finite T R).toFinset,
        (zeroMult ρ : ℝ) * Real.exp (|u| / 2) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hρ' : ρ ∈ zerosIn T R := (zerosIn_finite T R).mem_toFinset.mp hρ
      have hc : ρ ∈ cutoff R :=
        mem_cutoff.mpr ⟨hρ'.1, lt_of_le_of_lt hT hρ'.2.1, hρ'.2.2⟩
      exact mul_le_mul_of_nonneg_left (centeredExp_norm_le_strip hc u)
        (Nat.cast_nonneg _)
    _ = (Ncount T R : ℝ) * Real.exp (|u| / 2) := by
      rw [← Finset.sum_mul, ← hcount]
    _ = _ := mul_comm _ _

/-- The existing actual local count controls every window of height at most 2. -/
theorem exists_shortWindow_count_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ T R : ℝ, 0 ≤ T → T ≤ R → R ≤ T + 2 →
      (Ncount T R : ℝ) ≤ 2 * A * Real.log (T + 4) := by
  obtain ⟨A, hA, hcount⟩ := RvM.zeta_local_zero_count
  refine ⟨A, hA, ?_⟩
  intro T R hT hTR hR
  have hA0 : 0 ≤ A := by linarith
  have hmono : (Ncount T R : ℝ) ≤ (Ncount T (T + 2) : ℝ) := by
    exact_mod_cast Ncount_mono le_rfl hR
  have hadd : (Ncount T (T + 2) : ℝ) =
      (Ncount T (T + 1) : ℝ) + (Ncount (T + 1) (T + 2) : ℝ) := by
    exact_mod_cast Ncount_add (a := T) (b := T + 1) (c := T + 2)
      (by linarith) (by linarith)
  have hfirst : (Ncount T (T + 1) : ℝ) ≤ A * Real.log (T + 4) := by
    have hc := hcount T
    rw [abs_of_nonneg hT] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith : 0 < T + 3) (by linarith)) hA0)
  have hsecond : (Ncount (T + 1) (T + 2) : ℝ) ≤ A * Real.log (T + 4) := by
    have hc := hcount (T + 1)
    simpa only [abs_of_nonneg (by linarith : 0 ≤ T + 1),
      show (T + 1) + 1 = T + 2 by ring,
      show (T + 1) + 3 = T + 4 by ring] using hc
  rw [hadd] at hmono
  linarith

/-- Actual short-height transfer closes the arbitrary-cutoff bridge once the
separate contour estimate has been proved at nearby good heights. -/
theorem exists_landauSum_short_height_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ T R u : ℝ, 0 ≤ T → T ≤ R → R ≤ T + 2 →
      ‖landauSum R u - landauSum T u‖ ≤
        (2 * A * Real.log (T + 4)) * Real.exp (|u| / 2) := by
  obtain ⟨A, hA, hwindow⟩ := exists_shortWindow_count_bound
  refine ⟨A, hA, ?_⟩
  intro T R u hT hTR hR
  calc
    _ ≤ Real.exp (|u| / 2) * (Ncount T R : ℝ) :=
      landauSum_height_difference_norm_le T R u hT hTR
    _ ≤ Real.exp (|u| / 2) * (2 * A * Real.log (T + 4)) :=
      mul_le_mul_of_nonneg_left (hwindow T R hT hTR hR) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end RiemannResearch.Analysis.ActualZeroOrdinate


namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Full reflected window equality, before taking an absolute value. -/
theorem landauSum_sub_eq_reflected_window_sum (T R u : ℝ)
    (hT : 0 ≤ T) (hTR : T ≤ R) :
    landauSum R u - landauSum T u =
      ∑ ρ ∈ (Zeta23.zerosIn_finite T R).toFinset,
        (Zeta23.zeroMult ρ : ℂ) * ZeroOrdinate.phase u ρ.im *
          (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) := by
  rw [landauSum_eq_cosh, landauSum_eq_cosh, sum_sub_eq_window_sum T R hT hTR]
  apply Finset.sum_congr rfl
  intro ρ hρ
  ring

/-- Complete reflection improves the height transfer from exp to cosh. -/
theorem landauSum_height_difference_norm_le_cosh (T R u : ℝ)
    (hT : 0 ≤ T) (hTR : T ≤ R) :
    ‖landauSum R u - landauSum T u‖ ≤
      Real.cosh (|u| / 2) * (Zeta23.Ncount T R : ℝ) := by
  classical
  have hcount : (Zeta23.Ncount T R : ℝ) =
      ∑ ρ ∈ (Zeta23.zerosIn_finite T R).toFinset, (Zeta23.zeroMult ρ : ℝ) := by
    rw [Zeta23.Ncount,
      finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite T R), Nat.cast_sum]
  have hp : ∀ ρ ∈ (Zeta23.zerosIn_finite T R).toFinset,
      ‖ZeroOrdinate.phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)‖ ≤
        Real.cosh (|u| / 2) := by
    intro ρ hρ
    have hρ' : ρ ∈ Zeta23.zerosIn T R := (zerosIn_finite T R).mem_toFinset.mp hρ
    have hc : ρ ∈ cutoff R :=
      mem_cutoff.mpr ⟨hρ'.1, lt_of_le_of_lt hT hρ'.2.1, hρ'.2.2⟩
    have hcosh : 0 ≤ Real.cosh (u * (ρ.re - 1 / 2)) :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (Real.one_le_cosh _)
    rw [norm_mul, ZeroOrdinate.phase_norm, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hcosh]
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_of_nonneg (div_nonneg (abs_nonneg u) (by norm_num))]
    have h := (displacement_lt_half hc).le
    nlinarith [abs_nonneg u, mul_le_mul_of_nonneg_left h (abs_nonneg u)]
  rw [landauSum_sub_eq_reflected_window_sum T R u hT hTR]
  calc
    _ = ‖∑ ρ ∈ (Zeta23.zerosIn_finite T R).toFinset,
        (Zeta23.zeroMult ρ : ℂ) *
          (ZeroOrdinate.phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ))‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ρ hρ
      ring
    _ ≤ ∑ ρ ∈ (Zeta23.zerosIn_finite T R).toFinset,
        ‖(Zeta23.zeroMult ρ : ℂ) *
          (ZeroOrdinate.phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ))‖ :=
      _root_.norm_sum_le _ _
    _ = ∑ ρ ∈ (Zeta23.zerosIn_finite T R).toFinset,
        (Zeta23.zeroMult ρ : ℝ) *
          ‖ZeroOrdinate.phase u ρ.im * (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ)‖ := by
      simp only [norm_mul, Complex.norm_natCast]
    _ ≤ ∑ ρ ∈ (Zeta23.zerosIn_finite T R).toFinset,
        (Zeta23.zeroMult ρ : ℝ) * Real.cosh (|u| / 2) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact mul_le_mul_of_nonneg_left (hp ρ hρ) (Nat.cast_nonneg _)
    _ = (Zeta23.Ncount T R : ℝ) * Real.cosh (|u| / 2) := by
      rw [← Finset.sum_mul, ← hcount]
    _ = _ := mul_comm _ _

theorem exists_landauSum_short_height_cosh_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ T R u : ℝ, 0 ≤ T → T ≤ R → R ≤ T + 2 →
      ‖landauSum R u - landauSum T u‖ ≤
        (2 * A * Real.log (T + 4)) * Real.cosh (|u| / 2) := by
  obtain ⟨A, hA, hwindow⟩ := exists_shortWindow_count_bound
  refine ⟨A, hA, ?_⟩
  intro T R u hT hTR hR
  have hc : 0 ≤ Real.cosh (|u| / 2) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (Real.one_le_cosh _)
  calc
    _ ≤ Real.cosh (|u| / 2) * (Zeta23.Ncount T R : ℝ) :=
      landauSum_height_difference_norm_le_cosh T R u hT hTR
    _ ≤ Real.cosh (|u| / 2) * (2 * A * Real.log (T + 4)) :=
      mul_le_mul_of_nonneg_left (hwindow T R hT hTR hR) hc
    _ = _ := mul_comm _ _

end RiemannResearch.Analysis.ActualZeroOrdinate
