/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConsecutivePhaseTaylor
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Quantitative consecutive-phase laws from explicit moment inputs

This module retains finite endpoint, drift, and square terms before forming
asymptotic consequences. The row samples and counts are explicit arguments.
Squared/cubic gap bounds and one-point arithmetic estimates are explicit
hypotheses; the classical Fujii and FMZ estimates are not asserted here.

Source: user-provided argument. The motivating classical estimates are
Ford--Meng--Zaharescu, arXiv:1511.06814, Lemma 2, and Fujii's gap moments as
recorded in Ivić, arXiv:1610.01317, equation (1.2).
-/

noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ConsecutivePhaseAsymptotics
open OrdinateLagPhase

def gapEnergy (γ : ℕ → ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, (γ (j+1) - γ j)^2

def gapCubicMoment (γ : ℕ → ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, |γ (j+1) - γ j|^3

def pairMean (γ : ℕ → ℝ) (J : ℕ) (a b : ℝ) : ℂ :=
  (∑ j ∈ Finset.range J, phase a (γ j) * phase b (γ (j+1))) / (J : ℂ)

def ordinateMean (γ : ℕ → ℝ) (J : ℕ) (q : ℝ) : ℂ :=
  (∑ j ∈ Finset.range J, phase q (γ j)) / (J : ℂ)

def gapMean (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) : ℂ :=
  (∑ j ∈ Finset.range J, phase b (γ (j+1) - γ j)) / (J : ℂ)

theorem pairMean_neg_eq_gapMean (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) :
    pairMean γ J (-b) b = gapMean γ J b := by
  unfold pairMean gapMean
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [consecutive_phase_factor]
  simp [phase]

theorem gapEnergy_nonneg (γ : ℕ → ℝ) (J : ℕ) : 0 ≤ gapEnergy γ J :=
  Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem gapCubicMoment_nonneg (γ : ℕ → ℝ) (J : ℕ) :
    0 ≤ gapCubicMoment γ J :=
  Finset.sum_nonneg (fun j _ => pow_nonneg (abs_nonneg _) _)

/-- The endpoint contribution remains visible in the quantitative pair
comparison. This bound is valid even when the count is zero. -/
theorem norm_pairMean_sub_ordinateMean_le
    (γ : ℕ → ℝ) (J : ℕ) (a b : ℝ) (hq : a+b ≠ 0) :
    ‖pairMean γ J a b - ordinateMean γ J (a+b)‖ ≤
      2 * |b/(a+b)| * (1 / (J : ℝ)) +
        (2 * (b^2 + |b/(a+b)| * (a+b)^2)) *
          (gapEnergy γ J / (J : ℝ)) := by
  have hc : b = (b/(a+b)) * (a+b) := by field_simp [hq]
  have he := consecutive_phase_transport_eq γ J a b (b/(a+b)) hc
  have hb : ‖phase (a+b) (γ J) - phase (a+b) (γ 0)‖ ≤ 2 := by
    calc
      _ ≤ ‖phase (a+b) (γ J)‖ + ‖phase (a+b) (γ 0)‖ := norm_sub_le _ _
      _ = _ := by simp only [norm_phase]; norm_num
  have hraw :
      ‖(∑ j ∈ Finset.range J, phase a (γ j) * phase b (γ (j+1))) -
        (∑ j ∈ Finset.range J, phase (a+b) (γ j))‖ ≤
      2 * |b/(a+b)| +
        (2 * (b^2 + |b/(a+b)| * (a+b)^2)) * gapEnergy γ J := by
    rw [he]
    have halg (x y z : ℂ) : x+y+z-x = y+z := by ring
    rw [halg]
    calc
      _ ≤ ‖((b/(a+b) : ℝ) : ℂ) *
          (phase (a+b) (γ J) - phase (a+b) (γ 0))‖ +
          ‖consecutiveTransportDefect γ J (a+b) b (b/(a+b))‖ := norm_add_le _ _
      _ ≤ |b/(a+b)| * 2 +
          (2 * (b^2 + |b/(a+b)| * (a+b)^2)) * gapEnergy γ J := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        · exact norm_consecutiveTransportDefect_le γ J (a+b) b (b/(a+b))
      _ = _ := by ring
  unfold pairMean ordinateMean
  rw [← sub_div, norm_div, Complex.norm_natCast]
  calc
    _ ≤ (2 * |b/(a+b)| +
        (2 * (b^2 + |b/(a+b)| * (a+b)^2)) * gapEnergy γ J) / (J : ℝ) :=
      div_le_div_of_nonneg_right hraw (Nat.cast_nonneg J)
    _ = _ := by ring

/-- Quantitative nonresonant transfer for arbitrary rows. The two required
inputs are the normalized square-gap energy and the reciprocal count. -/
theorem pairMean_sub_ordinateMean_isBigO
    (γ : ℝ → ℕ → ℝ) (count : ℝ → ℕ) (r : ℝ → ℝ)
    (a b : ℝ) (hq : a+b ≠ 0)
    (henergy : (fun T => gapEnergy (γ T) (count T) / (count T : ℝ)) =O[atTop] r)
    (hcount : (fun T => 1 / (count T : ℝ)) =O[atTop] r) :
    (fun T => pairMean (γ T) (count T) a b -
      ordinateMean (γ T) (count T) (a+b)) =O[atTop] r := by
  obtain ⟨CE, hE⟩ := henergy.bound
  obtain ⟨CN, hN⟩ := hcount.bound
  let A : ℝ := 2 * |b/(a+b)|
  let B : ℝ := 2 * (b^2 + |b/(a+b)| * (a+b)^2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply IsBigO.of_bound (A*CN+B*CE)
  filter_upwards [hE, hN] with T hET hNT
  rw [Real.norm_of_nonneg (div_nonneg (gapEnergy_nonneg _ _) (Nat.cast_nonneg _))] at hET
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1/(count T : ℝ))] at hNT
  calc
    _ ≤ A * (1/(count T : ℝ)) + B *
        (gapEnergy (γ T) (count T)/(count T : ℝ)) :=
      norm_pairMean_sub_ordinateMean_le (γ T) (count T) a b hq
    _ ≤ A * (CN * ‖r T‖) + B * (CE * ‖r T‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hNT hA)
        (mul_le_mul_of_nonneg_left hET hB)
    _ = _ := by ring

/-- A supplied one-point main term survives consecutive sampling at the same
error scale. In the zeta application it must be supplied by actual FMZ. -/
theorem pairMean_sub_main_isBigO
    (γ : ℝ → ℕ → ℝ) (count : ℝ → ℕ) (r : ℝ → ℝ)
    (main : ℝ → ℂ) (a b : ℝ) (hq : a+b ≠ 0)
    (henergy : (fun T => gapEnergy (γ T) (count T) / (count T : ℝ)) =O[atTop] r)
    (hcount : (fun T => 1 / (count T : ℝ)) =O[atTop] r)
    (honepoint : (fun T => ordinateMean (γ T) (count T) (a+b) - main T) =O[atTop] r) :
    (fun T => pairMean (γ T) (count T) a b - main T) =O[atTop] r := by
  simpa only [sub_add_sub_cancel] using
    (pairMean_sub_ordinateMean_isBigO γ count r a b hq henergy hcount).add honepoint

/-- Exact resonant expansion with its full signed linear remainder. -/
theorem gap_phase_linear_eq (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) :
    (∑ j ∈ Finset.range J, phase b (γ (j+1)-γ j)) =
      (J : ℂ) + Complex.I * (b : ℂ) * ((γ J-γ 0 : ℝ) : ℂ) +
        ∑ j ∈ Finset.range J, phaseLinearDefect (b*(γ (j+1)-γ j)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    unfold phaseLinearDefect
    have hp : phase 1 (b*(γ (J+1)-γ J)) = phase b (γ (J+1)-γ J) := by
      simp [phase]
    rw [hp]
    push_cast
    ring

theorem norm_gap_linear_remainder_le (γ : ℕ → ℝ) (J : ℕ) (b : ℝ) :
    ‖∑ j ∈ Finset.range J, phaseLinearDefect (b*(γ (j+1)-γ j))‖ ≤
      2*b^2*gapEnergy γ J := by
  calc
    _ ≤ ∑ j ∈ Finset.range J, ‖phaseLinearDefect (b*(γ (j+1)-γ j))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, 2*b^2*(γ (j+1)-γ j)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [mul_pow, mul_assoc] using norm_phaseLinearDefect_le (b*(γ (j+1)-γ j))
    _ = _ := by simp only [gapEnergy, Finset.mul_sum]

theorem norm_gapMean_sub_drift_le (γ : ℕ → ℝ) (J : ℕ)
    (hJ : J ≠ 0) (b : ℝ) :
    ‖gapMean γ J b - 1 -
      Complex.I * (b : ℂ) * ((γ J-γ 0 : ℝ) : ℂ)/(J : ℂ)‖ ≤
      2*b^2*(gapEnergy γ J/(J : ℝ)) := by
  have hJc : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have heq : gapMean γ J b - 1 -
      Complex.I * (b : ℂ) * ((γ J-γ 0 : ℝ) : ℂ)/(J : ℂ) =
      (∑ j ∈ Finset.range J, phaseLinearDefect (b*(γ (j+1)-γ j)))/(J : ℂ) := by
    unfold gapMean
    rw [gap_phase_linear_eq]
    field_simp [hJc]
    ring
  rw [heq, norm_div, Complex.norm_natCast]
  calc
    _ ≤ (2*b^2*gapEnergy γ J)/(J : ℝ) :=
      div_le_div_of_nonneg_right (norm_gap_linear_remainder_le γ J b) (Nat.cast_nonneg J)
    _ = _ := by ring

/-- The drift is retained. Only the normalized squared-gap moment is needed. -/
theorem gapMean_sub_drift_isBigO
    (γ : ℝ → ℕ → ℝ) (count : ℝ → ℕ) (r : ℝ → ℝ) (b : ℝ)
    (hcount : ∀ᶠ T in atTop, count T ≠ 0)
    (henergy : (fun T => gapEnergy (γ T) (count T)/(count T : ℝ)) =O[atTop] r) :
    (fun T => gapMean (γ T) (count T) b - 1 -
      Complex.I * (b : ℂ) * ((γ T (count T)-γ T 0 : ℝ) : ℂ)/(count T : ℂ)) =O[atTop] r := by
  obtain ⟨C, hC⟩ := henergy.bound
  apply IsBigO.of_bound (2*b^2*C)
  filter_upwards [hcount, hC] with T hT hCT
  rw [Real.norm_of_nonneg (div_nonneg (gapEnergy_nonneg _ _) (Nat.cast_nonneg _))] at hCT
  calc
    _ ≤ 2*b^2*(gapEnergy (γ T) (count T)/(count T : ℝ)) :=
      norm_gapMean_sub_drift_le (γ T) (count T) hT b
    _ ≤ 2*b^2*(C*‖r T‖) := mul_le_mul_of_nonneg_left hCT (by positivity)
    _ = _ := by ring

/-- The square term has its exact negative sign; the cubic remainder is the
only discarded term in this estimate. -/
theorem norm_gapMean_sub_drift_add_square_le
    (γ : ℕ → ℝ) (J : ℕ) (hJ : J ≠ 0) (b : ℝ) :
    ‖gapMean γ J b - 1 -
      Complex.I * (b : ℂ) * ((γ J-γ 0 : ℝ) : ℂ)/(J : ℂ) +
      ((b^2/2 : ℝ) : ℂ) * (gapEnergy γ J : ℂ)/(J : ℂ)‖ ≤
      3*|b|^3*(gapCubicMoment γ J/(J : ℝ)) := by
  have hJc : (J : ℂ) ≠ 0 := by exact_mod_cast hJ
  have heq : gapMean γ J b - 1 -
      Complex.I * (b : ℂ) * ((γ J-γ 0 : ℝ) : ℂ)/(J : ℂ) +
      ((b^2/2 : ℝ) : ℂ) * (gapEnergy γ J : ℂ)/(J : ℂ) =
      (∑ j ∈ Finset.range J, phaseQuadraticDefect (b*(γ (j+1)-γ j)))/(J : ℂ) := by
    unfold gapMean
    rw [consecutive_gap_phase_quadratic_eq]
    simp only [gapEnergy, Complex.ofReal_sum]
    field_simp [hJc]
    ring
  rw [heq, norm_div, Complex.norm_natCast]
  calc
    _ ≤ (3*|b|^3*gapCubicMoment γ J)/(J : ℝ) :=
      div_le_div_of_nonneg_right
        (norm_consecutive_gap_quadratic_remainder_le γ J b) (Nat.cast_nonneg J)
    _ = _ := by ring

theorem gapMean_sub_drift_add_square_isBigO
    (γ : ℝ → ℕ → ℝ) (count : ℝ → ℕ) (r : ℝ → ℝ) (b : ℝ)
    (hcount : ∀ᶠ T in atTop, count T ≠ 0)
    (hcubic : (fun T => gapCubicMoment (γ T) (count T)/(count T : ℝ)) =O[atTop] r) :
    (fun T => gapMean (γ T) (count T) b - 1 -
      Complex.I * (b : ℂ) * ((γ T (count T)-γ T 0 : ℝ) : ℂ)/(count T : ℂ) +
      ((b^2/2 : ℝ) : ℂ) * (gapEnergy (γ T) (count T) : ℂ)/(count T : ℂ)) =O[atTop] r := by
  obtain ⟨C, hC⟩ := hcubic.bound
  apply IsBigO.of_bound (3*|b|^3*C)
  filter_upwards [hcount, hC] with T hT hCT
  rw [Real.norm_of_nonneg
    (div_nonneg (gapCubicMoment_nonneg _ _) (Nat.cast_nonneg _))] at hCT
  calc
    _ ≤ 3*|b|^3*(gapCubicMoment (γ T) (count T)/(count T : ℝ)) :=
      norm_gapMean_sub_drift_add_square_le (γ T) (count T) hT b
    _ ≤ 3*|b|^3*(C*‖r T‖) := mul_le_mul_of_nonneg_left hCT (by positivity)
    _ = _ := by ring

/-- The resonant pair formulation, equivalent to the gap characteristic
function, with the deterministic transport drift explicitly retained. -/
theorem resonant_pairMean_sub_drift_isBigO
    (γ : ℝ → ℕ → ℝ) (count : ℝ → ℕ) (r : ℝ → ℝ) (b : ℝ)
    (hcount : ∀ᶠ T in atTop, count T ≠ 0)
    (henergy : (fun T => gapEnergy (γ T) (count T)/(count T : ℝ)) =O[atTop] r) :
    (fun T => pairMean (γ T) (count T) (-b) b - 1 -
      Complex.I * (b : ℂ) * ((γ T (count T)-γ T 0 : ℝ) : ℂ)/(count T : ℂ)) =O[atTop] r := by
  simpa only [pairMean_neg_eq_gapMean] using
    gapMean_sub_drift_isBigO γ count r b hcount henergy

end RiemannResearch.Analysis.ConsecutivePhaseAsymptotics
