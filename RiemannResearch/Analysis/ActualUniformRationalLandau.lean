/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroLandauContour
import RiemannResearch.Analysis.ActualRationalLandauRightLine
import RiemannResearch.Analysis.ActualLandauLeftLine
import RiemannResearch.Analysis.ActualZetaGoodLandauHorizontals
import RiemannResearch.Analysis.ActualZeroHeightTransfer
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Complete actual uniform rational Landau estimate

This module proves an unconditional fixed-c=2 bound for the actual zeta zeros,
uniformly for T>=9 and 1<=m<n<=X. It retains the entire signed contour, analytic
multiplicities, the low-height sum, the nonresonant series, the arbitrary-cutoff
window and the exact endpoint correction (A+T-B)*main before taking norms.
The actual Re=2 coefficient is identified with the classical centered
von Mangoldt coefficient. No Landau or density estimate is assumed.

The resulting X-envelope is sufficient for log X=O(sqrt(log T)); the sharper
classical O(X*log(2XT)) estimate is a separate formalization target.
Source for the contour strategy: Gonek, Theorem 1 (1985),
https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf.
The quantitative proof uses only the actual imported contour, series, good-height,
Gamma and local-count providers; no published Landau bound is imported.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Complex Zeta23 MeasureTheory Set
open scoped BigOperators

namespace Complex

theorem norm_add_sub_add_sub_add_le (a b c d e f : ℂ) :
    ‖a + b - c + d - e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le a b
  have h2 := norm_sub_le (a + b) c
  have h3 := norm_add_le (a + b - c) d
  have h4 := norm_sub_le (a + b - c + d) e
  have h5 := norm_add_le (a + b - c + d - e) f
  linarith only [h1, h2, h3, h4, h5]

end Complex

namespace Real

theorem goodHeight_floor_choice (R : ℕ → ℝ)
    (hR : ∀ j : ℕ, (j : ℝ) + 7 ≤ R j ∧ R j ≤ (j : ℝ) + 8)
    {T : ℝ} (hT : 9 ≤ T) :
    1 ≤ Nat.floor T - 6 ∧ ((Nat.floor T - 6 : ℕ) : ℝ) ≤ T ∧
      T ≤ R (Nat.floor T - 6) ∧ R (Nat.floor T - 6) ≤ T + 2 := by
  let j : ℕ := Nat.floor T - 6
  change 1 ≤ j ∧ (j : ℝ) ≤ T ∧ T ≤ R j ∧ R j ≤ T + 2
  have hT0 : 0 ≤ T := by linarith
  have hk : 9 ≤ Nat.floor T := (Nat.le_floor_iff hT0).2 (by simpa using hT)
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hkj : j + 6 = Nat.floor T := by dsimp [j]; omega
  have hkjR : (Nat.floor T : ℝ) = (j : ℝ) + 6 := by exact_mod_cast hkj.symm
  have hflo : (Nat.floor T : ℝ) ≤ T := Nat.floor_le hT0
  have hfhi : T < (Nat.floor T : ℝ) + 1 := Nat.lt_floor_add_one T
  obtain ⟨hRlo, hRhi⟩ := hR j
  refine ⟨hj, ?_, ?_, ?_⟩ <;> linarith

theorem log_nat_add_ten_le_two_log_add_three {T : ℝ} (hT : 9 ≤ T)
    {j : ℕ} (hj : (j : ℝ) ≤ T) :
    log ((j : ℝ) + 10) ≤ 2 * log (T + 3) := by
  have hbase : 0 < T + 3 := by linarith
  have hsquare : (j : ℝ) + 10 ≤ (T + 3) * (T + 3) := by nlinarith [sq_nonneg T]
  calc
    _ ≤ log ((T + 3) * (T + 3)) := log_le_log (by positivity) hsquare
    _ = _ := by rw [log_mul hbase.ne' hbase.ne']; ring

theorem log_add_four_le_two_log_add_three {T : ℝ} (hT : 9 ≤ T) :
    log (T + 4) ≤ 2 * log (T + 3) := by
  have hbase : 0 < T + 3 := by linarith
  have hsquare : T + 4 ≤ (T + 3) * (T + 3) := by nlinarith [sq_nonneg T]
  calc
    _ ≤ log ((T + 3) * (T + 3)) := log_le_log (by linarith) hsquare
    _ = _ := by rw [log_mul hbase.ne' hbase.ne']; ring

end Real

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- Actual upward left side, including its normalization and sign convention. -/
def leftLandauLine (A B u : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in A..B, Complex.exp ((u : ℂ) * ((-1 : ℂ) + t * I - 1 / 2)) *
      logDeriv riemannZeta ((-1 : ℂ) + t * I)

/-- Bottom minus top horizontal sides in the positive rectangle orientation. -/
def horizontalLandauCorrection (A B u : ℝ) : ℂ :=
  (1 / (2 * Real.pi * I) : ℂ) *
    ((∫ σ in (-1 : ℝ)..2, Complex.exp ((u : ℂ) * ((σ : ℂ) + A * I - 1 / 2)) *
      logDeriv riemannZeta ((σ : ℂ) + A * I)) -
     (∫ σ in (-1 : ℝ)..2, Complex.exp ((u : ℂ) * ((σ : ℂ) + B * I - 1 / 2)) *
      logDeriv riemannZeta ((σ : ℂ) + B * I)))

/-- The actual normalized prime-power coefficient obtained from Re s=2.
The divisibility branch retains its von Mangoldt value, including zero values. -/
def rationalLandauMain (n m : ℕ) : ℝ :=
  (Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) / (2 * Real.pi)) *
    (if m ∣ n then mangoldtSquareCoeff (n / m) else 0)

theorem rationalLandauMain_nonneg (n m : ℕ) : 0 ≤ rationalLandauMain n m := by
  unfold rationalLandauMain
  apply mul_nonneg (div_nonneg (Real.exp_pos _).le (by positivity))
  split_ifs <;> first | exact mangoldtSquareCoeff_nonneg _ | rfl

theorem rectangleIntegral_centered_eq_four_sides (A B u : ℝ) :
    RectangleIntegral'
      (fun s => Complex.exp ((u : ℂ) * (s - 1 / 2)) * logDeriv riemannZeta s)
      ((-1 : ℂ) + A * I) ((2 : ℂ) + B * I) =
      rightLandauLine A B u - leftLandauLine A B u +
        horizontalLandauCorrection A B u := by
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral,
    rightLandauLine, leftLandauLine, horizontalLandauCorrection,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, add_zero, zero_add, neg_zero, smul_eq_mul]
  norm_num
  norm_num
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ, Complex.I_ne_zero]
  <;> ring_nf
  <;> simp only [Complex.I_sq]
  <;> ring

/-- Exact actual zero window, with the original centered exponential weight. -/
theorem landauSum_sub_eq_four_sides (A B u : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hgoodA : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ A)
    (hgoodB : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ B) :
    landauSum B u - landauSum A u =
      rightLandauLine A B u - leftLandauLine A B u +
        horizontalLandauCorrection A B u := by
  have hrect := RvM.rectangleIntegral'_centered_exp_logDeriv_riemannZeta_eq_zero_sum
    (c := 2) (by norm_num) hA hAB hgoodA hgoodB u
  have hfin : (zetaSeam.finite_window A B).toFinset = (zerosIn_finite A B).toFinset := by
    ext ρ
    simp [zerosIn]
  rw [hfin] at hrect
  calc
    _ = ∑ ρ ∈ (zerosIn_finite A B).toFinset,
      (zeroMult ρ : ℂ) * Complex.exp ((u : ℂ) * (ρ - 1 / 2)) :=
      landauSum_sub_eq_window_sum A B u hA.le hAB
    _ = RectangleIntegral'
      (fun s => Complex.exp ((u : ℂ) * (s - 1 / 2)) * logDeriv riemannZeta s)
      ((-1 : ℂ) + A * I) ((2 : ℂ) + B * I) := by
      convert hrect.symm using 1 <;> norm_num
    _ = _ := rectangleIntegral_centered_eq_four_sides A B u

theorem rightLandauLine_rational_eq_main_nonresonance {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    rightLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) =
      -((B - A : ℝ) : ℂ) * (rationalLandauMain n m : ℂ) -
      ((Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) /
        (2 * Real.pi) : ℝ) : ℂ) *
        ∑' k, rationalMangoldtNonresonantTerm n m A B k := by
  rw [rightLandauLine_rational_eq_split hn hm A B]
  unfold rationalLandauMain
  by_cases hd : m ∣ n <;> simp only [hd, if_true, if_false]
  all_goals push_cast; ring

/-- Full exact signed arbitrary-cutoff identity. The endpoint correction is
(A+T-B) times the actual main coefficient. No zero or contour side is omitted. -/
theorem landauSum_rational_add_main_eq_complete {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (T A B : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hgoodA : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ A)
    (hgoodB : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ B) :
    landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ) =
      landauSum A (Real.log ((n : ℝ) / (m : ℝ))) +
        horizontalLandauCorrection A B (Real.log ((n : ℝ) / (m : ℝ))) -
        leftLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) -
        ((Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) /
          (2 * Real.pi) : ℝ) : ℂ) *
          (∑' k, rationalMangoldtNonresonantTerm n m A B k) -
        (landauSum B (Real.log ((n : ℝ) / (m : ℝ))) -
          landauSum T (Real.log ((n : ℝ) / (m : ℝ)))) +
        (((A + T - B) * rationalLandauMain n m : ℝ) : ℂ) := by
  have h := landauSum_sub_eq_four_sides A B
    (Real.log ((n : ℝ) / (m : ℝ))) hA hAB hgoodA hgoodB
  rw [rightLandauLine_rational_eq_main_nonresonance hn hm A B] at h
  push_cast at h ⊢
  linear_combination h

theorem norm_rightLandauLine_rational_add_main_le {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (A B : ℝ) :
    ‖rightLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) +
        (((B - A) * rationalLandauMain n m : ℝ) : ℂ)‖ ≤
      (Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) / (2 * Real.pi)) *
        ((4 * (n : ℝ)) * ∑' k, mangoldtSquareCoeff k) := by
  convert norm_rightLandauLine_rational_add_resonance_le hn hm A B using 1
  unfold rationalLandauMain
  by_cases hd : m ∣ n <;> simp only [hd, if_true, if_false]
  all_goals push_cast; ring

theorem norm_landauSum_le_count (A u : ℝ) :
    ‖landauSum A u‖ ≤ (Ncount 0 A : ℝ) * Real.exp (|u| / 2) := by
  calc
    _ ≤ realSum A (fun ρ => ‖Complex.exp ((u : ℂ) * (ρ - 1 / 2))‖) := norm_sum_le A _
    _ ≤ realSum A (fun _ => Real.exp (|u| / 2)) :=
      realSum_mono A _ _ (fun ρ hρ => centeredExp_norm_le_strip hρ u)
    _ = _ := by
      simp only [realSum, ← Finset.sum_mul, ← Nat.cast_sum, ← count_eq_sum]

theorem norm_landauSum_rational_add_main_le_components {n m : ℕ}
    (T A B : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hgoodA : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ A)
    (hgoodB : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ B) :
    ‖landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
        ((T * rationalLandauMain n m : ℝ) : ℂ)‖ ≤
      ‖landauSum A (Real.log ((n : ℝ) / (m : ℝ)))‖ +
      ‖rightLandauLine A B (Real.log ((n : ℝ) / (m : ℝ))) +
        (((B - A) * rationalLandauMain n m : ℝ) : ℂ)‖ +
      ‖leftLandauLine A B (Real.log ((n : ℝ) / (m : ℝ)))‖ +
      ‖horizontalLandauCorrection A B (Real.log ((n : ℝ) / (m : ℝ)))‖ +
      ‖landauSum B (Real.log ((n : ℝ) / (m : ℝ))) -
        landauSum T (Real.log ((n : ℝ) / (m : ℝ)))‖ +
      |A + T - B| * rationalLandauMain n m := by
  let u : ℝ := Real.log ((n : ℝ) / (m : ℝ))
  have h := landauSum_sub_eq_four_sides A B u hA hAB hgoodA hgoodB
  have he : landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ) =
      landauSum A u +
        (rightLandauLine A B u + (((B - A) * rationalLandauMain n m : ℝ) : ℂ)) -
        leftLandauLine A B u + horizontalLandauCorrection A B u -
        (landauSum B u - landauSum T u) +
        (((A + T - B) * rationalLandauMain n m : ℝ) : ℂ) := by
    push_cast
    linear_combination h
  change ‖landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)‖ ≤ _
  rw [he]
  have hnorm : ‖(((A + T - B) * rationalLandauMain n m : ℝ) : ℂ)‖ =
      |A + T - B| * rationalLandauMain n m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (rationalLandauMain_nonneg n m)]
  simpa only [hnorm] using Complex.norm_add_sub_add_sub_add_le
    (landauSum A u)
    (rightLandauLine A B u + (((B - A) * rationalLandauMain n m : ℝ) : ℂ))
    (leftLandauLine A B u) (horizontalLandauCorrection A B u)
    (landauSum B u - landauSum T u)
    (((A + T - B) * rationalLandauMain n m : ℝ) : ℂ)

theorem norm_landau_normalizer_le_one : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
  have h2π : 0 < 2 * Real.pi := by positivity
  have he : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by norm_num) h2π.le)]
  apply (div_le_iff₀ h2π).2
  linarith [Real.pi_gt_three]

theorem norm_landau_horizontal_normalizer_le_one :
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (1 / (2 * Real.pi * I) : ℂ) = (1 / (2 * Real.pi) : ℂ) * (-I) := by
    field_simp [hπ, Complex.I_ne_zero]
    <;> simp [Complex.I_sq]
  rw [he, norm_mul, norm_neg, Complex.norm_I, mul_one]
  exact norm_landau_normalizer_le_one

theorem norm_leftLandauLine_le (A B u : ℝ) (hA : 8 ≤ A) (hAB : A ≤ B) (hu : 0 < u) :
    ‖leftLandauLine A B u‖ ≤ Real.exp (-3 * u / 2) *
      (3 * Real.log B / u + 6 * Real.log (B / A) +
        (2 / u) * ∑' k : ℕ, mangoldtSquareCoeff k) := by
  unfold leftLandauLine
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∫ t in A..B,
        Complex.exp ((u : ℂ) * ((-1 : ℂ) + t * I - 1 / 2)) *
          logDeriv riemannZeta ((-1 : ℂ) + t * I)‖ :=
      mul_le_mul_of_nonneg_right norm_landau_normalizer_le_one (norm_nonneg _)
    _ = _ := one_mul _
    _ ≤ _ := norm_integral_centered_left_logDeriv_le A B u hA hAB hu

theorem norm_horizontalLandauCorrection_le (A B u : ℝ) :
    ‖horizontalLandauCorrection A B u‖ ≤
      ‖∫ σ in (-1 : ℝ)..2,
        Complex.exp ((u : ℂ) * ((σ : ℂ) + A * I - 1 / 2)) *
          logDeriv riemannZeta ((σ : ℂ) + A * I)‖ +
      ‖∫ σ in (-1 : ℝ)..2,
        Complex.exp ((u : ℂ) * ((σ : ℂ) + B * I - 1 / 2)) *
          logDeriv riemannZeta ((σ : ℂ) + B * I)‖ := by
  unfold horizontalLandauCorrection
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖_‖ := mul_le_mul_of_nonneg_right
      norm_landau_horizontal_normalizer_le_one (norm_nonneg _)
    _ = _ := one_mul _
    _ ≤ _ := norm_sub_le _ _

theorem rational_frequency_bounds {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    {X : ℝ} (hnX : (n : ℝ) ≤ X) :
    0 < Real.log ((n : ℝ) / (m : ℝ)) ∧
      Real.log ((n : ℝ) / (m : ℝ)) ≤ Real.log X ∧
      1 / Real.log ((n : ℝ) / (m : ℝ)) ≤ 2 * X ∧ 1 ≤ X := by
  have hn : 1 ≤ n := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hu : 0 < Real.log ((n : ℝ) / (m : ℝ)) :=
    Real.log_pos ((lt_div_iff₀ hm0).2 (by simpa using hmnR))
  have hx : (n : ℝ) / (m : ℝ) ≤ X := by
    apply (div_le_iff₀ hm0).2
    nlinarith
  have hlog := Real.log_le_log (div_pos hn0 hm0) hx
  have hs := rationalPhase_frequency_separated hn hm (k := 1) (by norm_num)
    (by simpa using (ne_of_gt hmn : n ≠ m))
  simp only [Nat.cast_one, Real.log_one, sub_zero, abs_of_pos hu] at hs
  have hinv : 1 / Real.log ((n : ℝ) / (m : ℝ)) ≤ 2 * (n : ℝ) := by
    apply (div_le_iff₀ hu).2
    have hs' := (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mp hs
    nlinarith
  refine ⟨hu, hlog, hinv.trans (by linarith), ?_⟩
  linarith

theorem rationalLandauMain_le_total (n m : ℕ) :
    rationalLandauMain n m ≤
      Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) *
        ∑' k : ℕ, mangoldtSquareCoeff k := by
  have hS : 0 ≤ ∑' k : ℕ, mangoldtSquareCoeff k :=
    tsum_nonneg mangoldtSquareCoeff_nonneg
  have hcoeff : (if m ∣ n then mangoldtSquareCoeff (n / m) else 0) ≤
      ∑' k : ℕ, mangoldtSquareCoeff k := by
    split_ifs
    · exact summable_mangoldtSquareCoeff.le_tsum (n / m) (fun k _ => mangoldtSquareCoeff_nonneg k)
    · exact hS
  have hc0 : 0 ≤ if m ∣ n then mangoldtSquareCoeff (n / m) else 0 := by
    split_ifs <;> first | exact mangoldtSquareCoeff_nonneg _ | rfl
  unfold rationalLandauMain
  calc
    _ ≤ Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) *
        (if m ∣ n then mangoldtSquareCoeff (n / m) else 0) := by
      apply mul_le_mul_of_nonneg_right _ hc0
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [Real.pi_gt_three, Real.exp_pos (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff (Real.exp_pos _).le

theorem norm_leftLandauLine_le_log_budget (A B u L : ℝ)
    (hA : 8 ≤ A) (hAB : A ≤ B) (hu : 0 < u) (hL : 1 ≤ L)
    (hlogB : Real.log B ≤ L) :
    ‖leftLandauLine A B u‖ ≤
      (9 + 2 * ∑' k : ℕ, mangoldtSquareCoeff k) * (1 + 1 / u) * L := by
  let S : ℝ := ∑' k : ℕ, mangoldtSquareCoeff k
  have hS : 0 ≤ S := tsum_nonneg mangoldtSquareCoeff_nonneg
  have hB1 : 1 ≤ B := by linarith
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hq : 1 ≤ B / A := (le_div_iff₀ (by linarith : 0 < A)).2 (by simpa using hAB)
  have hlogq0 : 0 ≤ Real.log (B / A) := Real.log_nonneg hq
  have hlogq : Real.log (B / A) ≤ L := by
    apply (Real.log_le_log (by positivity : 0 < B / A) _).trans hlogB
    apply (div_le_iff₀ (by linarith : 0 < A)).2
    nlinarith
  have hinner0 : 0 ≤ 3 * Real.log B / u + 6 * Real.log (B / A) + (2 / u) * S :=
    add_nonneg (add_nonneg (div_nonneg (by positivity) hu.le) (by positivity))
      (by positivity)
  have he : Real.exp (-3 * u / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  have hfirst : 3 * Real.log B / u ≤ 3 * (1 / u) * L := by
    calc
      3 * Real.log B / u = (3 / u) * Real.log B := by ring
      _ ≤ (3 / u) * L := mul_le_mul_of_nonneg_left hlogB (by positivity)
      _ = 3 * (1 / u) * L := by ring
  have hsecond : 6 * Real.log (B / A) ≤ 6 * L := by linarith
  have hthird : (2 / u) * S ≤ 2 * S * (1 / u) * L := by
    calc
      (2 / u) * S = ((2 / u) * S) * 1 := by ring
      _ ≤ ((2 / u) * S) * L := mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 2 * S * (1 / u) * L := by ring
  calc
    _ ≤ Real.exp (-3 * u / 2) *
        (3 * Real.log B / u + 6 * Real.log (B / A) + (2 / u) * S) :=
      norm_leftLandauLine_le A B u hA hAB hu
    _ ≤ 3 * Real.log B / u + 6 * Real.log (B / A) + (2 / u) * S := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he hinner0
    _ ≤ 3 * (1 / u) * L + 6 * L + 2 * S * (1 / u) * L := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ ≤ (9 + 2 * S) * (1 + 1 / u) * L := by
      have hL0 : 0 ≤ L := by linarith
      have huinv : 0 ≤ 1 / u := by positivity
      nlinarith [mul_nonneg hS hL0, mul_nonneg huinv hL0]

set_option maxHeartbeats 800000 in
/-- An unconditional uniform Landau provider for the actual zeta zeros.
All parameters are uniform. It uses only fixed-c=2 contour sides and actual
finite-height transfer. The prime-power main retains its exact negative sign. -/
theorem exists_uniform_rational_landau_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (n m : ℕ), 9 ≤ T → 1 ≤ m → m < n →
      ‖landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
          ((T * rationalLandauMain n m : ℝ) : ℂ)‖ ≤
        C * (Real.exp (3 * Real.log ((n : ℝ) / (m : ℝ)) / 2) *
          ((n : ℝ) + (Real.log (T + 3)) ^ 2) +
          (1 + 1 / Real.log ((n : ℝ) / (m : ℝ))) * Real.log (T + 3)) := by
  obtain ⟨Cg, hCg, R, hR⟩ := WeilEF.good_heights_centered_exponential_horizontals
  obtain ⟨D, hD, htransfer⟩ := exists_landauSum_short_height_bound
  let A : ℝ := R 1
  let S : ℝ := ∑' k : ℕ, mangoldtSquareCoeff k
  let Na : ℝ := (Ncount 0 A : ℝ)
  let C : ℝ := Na + 15 * S + 15 * Cg + 4 * D + 10
  have hS : 0 ≤ S := tsum_nonneg mangoldtSquareCoeff_nonneg
  have hNa : 0 ≤ Na := Nat.cast_nonneg _
  have hD0 : 0 ≤ D := by linarith
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro T n m hT hm hmn
  have hn : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let u : ℝ := Real.log ((n : ℝ) / (m : ℝ))
  let L : ℝ := Real.log (T + 3)
  let e : ℝ := Real.exp (3 * u / 2)
  let F : ℝ := e * ((n : ℝ) + L ^ 2)
  let G : ℝ := (1 + 1 / u) * L
  have hu : 0 < u := (rational_frequency_bounds hm hmn (le_refl (n : ℝ))).1
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 ≤ L := by linarith
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  have heF : e ≤ F := by dsimp [F]; nlinarith [sq_nonneg L]
  have henF : e * (n : ℝ) ≤ F := by dsimp [F]; nlinarith [sq_nonneg L]
  have heL2F : e * L ^ 2 ≤ F := by dsimp [F]; nlinarith
  have hhalf : Real.exp (|u| / 2) ≤ e := by
    rw [abs_of_pos hu]
    exact Real.exp_le_exp.mpr (by linarith)
  let j : ℕ := Nat.floor T - 6
  let B : ℝ := R j
  have hRgeom : ∀ k : ℕ, (k : ℝ) + 7 ≤ R k ∧ R k ≤ (k : ℝ) + 8 :=
    fun k => ⟨(hR k).1, (hR k).2.1⟩
  obtain ⟨hj1, hjT, hTB, hBT⟩ := Real.goodHeight_floor_choice R hRgeom hT
  change (j : ℝ) ≤ T at hjT
  change T ≤ B at hTB
  change B ≤ T + 2 at hBT
  obtain ⟨hAlo, hAhi, hAgood, hAh⟩ := hR 1
  norm_num at hAlo hAhi
  change 8 ≤ A at hAlo
  change A ≤ 9 at hAhi
  have hAB : A ≤ B := by linarith
  have hgoodA : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ A := by
    intro ρ hρ him
    exact (hAgood ρ (Or.inl him) (by linarith [hρ.2.1]) (by linarith [hρ.2.2])) hρ.1
  obtain ⟨_, _, hBgood, hBh⟩ := hR j
  have hgoodB : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ B := by
    intro ρ hρ him
    exact (hBgood ρ (Or.inl him) (by linarith [hρ.2.1]) (by linarith [hρ.2.2])) hρ.1
  have hlow : ‖landauSum A u‖ ≤ Na * F := by
    calc
      _ ≤ Na * Real.exp (|u| / 2) := norm_landauSum_le_count A u
      _ ≤ Na * e := mul_le_mul_of_nonneg_left hhalf hNa
      _ ≤ _ := mul_le_mul_of_nonneg_left heF hNa
  have hc : e / (2 * Real.pi) ≤ e := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hright : ‖rightLandauLine A B u +
      (((B - A) * rationalLandauMain n m : ℝ) : ℂ)‖ ≤ 4 * S * F := by
    calc
      _ ≤ (e / (2 * Real.pi)) * ((4 * (n : ℝ)) * S) :=
        norm_rightLandauLine_rational_add_main_le hn hm A B
      _ ≤ e * ((4 * (n : ℝ)) * S) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (4 * S) * (e * (n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left henF (by positivity)
  have hlogB : Real.log B ≤ L :=
    Real.log_le_log (by linarith : 0 < B) (by linarith)
  have hleft : ‖leftLandauLine A B u‖ ≤ (9 + 2 * S) * G := by
    simpa only [G, mul_assoc] using
      norm_leftLandauLine_le_log_budget A B u L hAlo hAB hu hL hlogB
  have hlog11 : Real.log 11 ≤ L :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog11sq : (Real.log 11) ^ 2 ≤ L ^ 2 := by
    nlinarith only [hlog11, hL0, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 11)]
  have hlogj : Real.log ((j : ℝ) + 10) ≤ 2 * L :=
    Real.log_nat_add_ten_le_two_log_add_three hT hjT
  have hlogjsq : (Real.log ((j : ℝ) + 10)) ^ 2 ≤ 4 * L ^ 2 := by
    nlinarith only [hlogj, hL0, Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j] : 1 ≤ (j : ℝ) + 10)]
  have hbottom := hAh u A (Or.inl rfl)
  have htop := hBh u B (Or.inl rfl)
  rw [abs_of_pos hu] at hbottom htop
  simp only [Nat.cast_one, show (1 : ℝ) + 10 = 11 by norm_num] at hbottom
  change ‖_‖ ≤ 3 * e * Cg * (Real.log 11) ^ 2 at hbottom
  change ‖_‖ ≤ 3 * e * Cg * (Real.log ((j : ℝ) + 10)) ^ 2 at htop
  have hbottom' := hbottom.trans
    (mul_le_mul_of_nonneg_left hlog11sq (by positivity : 0 ≤ 3 * e * Cg))
  have htop' := htop.trans
    (mul_le_mul_of_nonneg_left hlogjsq (by positivity : 0 ≤ 3 * e * Cg))
  have hhorizontal : ‖horizontalLandauCorrection A B u‖ ≤ 15 * Cg * F := by
    calc
      _ ≤ _ := (norm_horizontalLandauCorrection_le A B u).trans (add_le_add hbottom' htop')
      _ = (15 * Cg) * (e * L ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left heL2F (by positivity)
  have hshortlog : Real.log (T + 4) ≤ 2 * L := Real.log_add_four_le_two_log_add_three hT
  have hheight : ‖landauSum B u - landauSum T u‖ ≤ 4 * D * F := by
    calc
      _ ≤ (2 * D * Real.log (T + 4)) * Real.exp (|u| / 2) :=
        htransfer T B u (by linarith) hTB hBT
      _ ≤ (2 * D * (2 * L)) * e := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hshortlog (by positivity)
        · exact hhalf
        · exact (Real.exp_pos _).le
        · positivity
      _ ≤ (4 * D) * (e * L ^ 2) := by
        have hLL : L ≤ L ^ 2 := by nlinarith only [hL]
        calc
          _ = (4 * D * e) * L := by ring
          _ ≤ (4 * D * e) * L ^ 2 := mul_le_mul_of_nonneg_left hLL (by positivity)
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left heL2F (by positivity)
  have hendabs : |A + T - B| ≤ 9 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ A + T - B)]
    linarith
  have hend : |A + T - B| * rationalLandauMain n m ≤ 9 * S * F := by
    calc
      _ ≤ 9 * rationalLandauMain n m := mul_le_mul_of_nonneg_right hendabs
        (rationalLandauMain_nonneg n m)
      _ ≤ 9 * (e * S) := mul_le_mul_of_nonneg_left (rationalLandauMain_le_total n m) (by norm_num)
      _ = (9 * S) * e := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left heF (by positivity)
  have hcoefF : Na + 13 * S + 15 * Cg + 4 * D ≤ C := by dsimp [C]; linarith only [hS]
  have hcoefG : 9 + 2 * S ≤ C := by dsimp [C]; linarith only [hNa, hS, hCg, hD]
  change ‖landauSum T u + ((T * rationalLandauMain n m : ℝ) : ℂ)‖ ≤ C * (F + G)
  calc
    _ ≤ _ := norm_landauSum_rational_add_main_le_components T A B (by linarith)
      hAB hgoodA hgoodB
    _ ≤ Na * F + 4 * S * F + (9 + 2 * S) * G + 15 * Cg * F + 4 * D * F + 9 * S * F := by
      gcongr
    _ = (Na + 13 * S + 15 * Cg + 4 * D) * F + (9 + 2 * S) * G := by ring
    _ ≤ C * F + C * G := add_le_add
      (mul_le_mul_of_nonneg_right hcoefF hF0) (mul_le_mul_of_nonneg_right hcoefG hG0)
    _ = _ := by ring

end RiemannResearch.Analysis.ActualZeroOrdinate


noncomputable section
open scoped ArithmeticFunction

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- The Re s=2 resonance coefficient is exactly the classical centered
Landau coefficient. The arithmetic branch counts every prime power. -/
theorem rationalLandauMain_eq_vonMangoldt_div_sqrt {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) :
    rationalLandauMain n m =
      if m ∣ n then
        (Λ (n / m) : ℝ) /
          ((2 * Real.pi) * Real.sqrt ((n : ℝ) / (m : ℝ)))
      else 0 := by
  have hn : 1 ≤ n := hm.trans hmn.le
  have hmpos : (0 : ℝ) < m := by positivity
  have hnpos : (0 : ℝ) < n := by positivity
  let x : ℝ := (n : ℝ) / (m : ℝ)
  have hx : 0 < x := div_pos hnpos hmpos
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hexp : Real.exp (3 * Real.log x / 2) = x * Real.sqrt x := by
    calc
      _ = Real.exp (Real.log x + Real.log (Real.sqrt x)) := by
        rw [Real.log_sqrt hx.le]
        congr 1
        ring
      _ = _ := by
        rw [Real.exp_add, Real.exp_log hx, Real.exp_log hs]
  unfold rationalLandauMain
  by_cases hd : m ∣ n
  · simp only [hd, if_true]
    have hq : ((n / m : ℕ) : ℝ) = x := by
      apply (eq_div_iff hmpos.ne').mpr
      exact_mod_cast Nat.div_mul_cancel hd
    change (Real.exp (3 * Real.log x / 2) / (2 * Real.pi)) *
        mangoldtSquareCoeff (n / m) =
      (Λ (n / m) : ℝ) / ((2 * Real.pi) * Real.sqrt x)
    rw [mangoldtSquareCoeff, hq, hexp]
    field_simp [Real.pi_ne_zero, hx.ne', hs.ne']
    <;> ring_nf
    <;> rw [Real.sq_sqrt hx.le]
    <;> ring
  · simp only [hd, if_false, mul_zero]

end RiemannResearch.Analysis.ActualZeroOrdinate




noncomputable section
namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem exists_uniform_rational_landau_rpow_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T X : ℝ) (n m : ℕ),
      9 ≤ T → 1 ≤ m → m < n → (n : ℝ) ≤ X →
      ‖landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
          ((T * rationalLandauMain n m : ℝ) : ℂ)‖ ≤
        C * (X ^ (5 / 2 : ℝ) +
          X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 + X * Real.log (T + 3)) := by
  obtain ⟨C, hC, hlandau⟩ := exists_uniform_rational_landau_bound
  refine ⟨3 * C, by positivity, ?_⟩
  intro T X n m hT hm hmn hnX
  let u : ℝ := Real.log ((n : ℝ) / (m : ℝ))
  let L : ℝ := Real.log (T + 3)
  obtain ⟨hu, huX, hinv, hX1⟩ := rational_frequency_bounds hm hmn hnX
  change 0 < u at hu
  change u ≤ Real.log X at huX
  change 1 / u ≤ 2 * X at hinv
  have hX0 : 0 < X := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith : 1 ≤ T + 3)
  have hE15 : Real.exp (3 * u / 2) ≤ X ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hX0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpow : X ^ (3 / 2 : ℝ) * X = X ^ (5 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hX0]
    calc
      Real.exp (Real.log X * (3 / 2)) * X =
          Real.exp (Real.log X * (3 / 2)) * Real.exp (Real.log X) := by
        rw [Real.exp_log hX0]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hEn : Real.exp (3 * u / 2) * (n : ℝ) ≤ X ^ (5 / 2 : ℝ) := by
    calc
      _ ≤ X ^ (3 / 2 : ℝ) * X := mul_le_mul hE15 hnX
        (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hX0 _).le
      _ = _ := hpow
  have hF : Real.exp (3 * u / 2) * ((n : ℝ) + L ^ 2) ≤
      X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * L ^ 2 := by
    rw [mul_add]
    exact add_le_add hEn (mul_le_mul_of_nonneg_right hE15 (sq_nonneg L))
  have hG : (1 + 1 / u) * L ≤ 3 * X * L :=
    mul_le_mul_of_nonneg_right (by linarith) hL0
  have hsum : Real.exp (3 * u / 2) * ((n : ℝ) + L ^ 2) + (1 + 1 / u) * L ≤
      3 * (X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * L ^ 2 + X * L) := by
    have hp25 : 0 ≤ X ^ (5 / 2 : ℝ) := (Real.rpow_pos_of_pos hX0 _).le
    have hp15L : 0 ≤ X ^ (3 / 2 : ℝ) * L ^ 2 :=
      mul_nonneg (Real.rpow_pos_of_pos hX0 _).le (sq_nonneg L)
    linarith only [hF, hG, hp25, hp15L]
  calc
    _ ≤ C * (Real.exp (3 * u / 2) * ((n : ℝ) + L ^ 2) + (1 + 1 / u) * L) :=
      hlandau T n m hT hm hmn
    _ ≤ C * (3 * (X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * L ^ 2 + X * L)) :=
      mul_le_mul_of_nonneg_left hsum hC.le
    _ = _ := by ring

end RiemannResearch.Analysis.ActualZeroOrdinate
