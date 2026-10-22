/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroHorizontalEnergy
import RiemannResearch.Analysis.GaussianLaplaceBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Absolute Laplace masses for all actual nontrivial zeros, including multiplicity.
The critical strip and existing reciprocal-square sum supply the majorant
without a separate zero-counting hypothesis or a lower-ordinate bound.
Source: independently developed domination for the Gaussian-to-resolvent
identity in RH/OrdinateHorizontalDefects20261010.md, Appendix Section 2.
The complete all-zero heat traces and signed infinite transform are assembled
here; see RH/InfiniteGaussianAnalyticBridge20261011.md for the exact scope.
-/

noncomputable section
open Complex Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroGaussianLaplace

abbrev ActualZero := ActualZeroHorizontalEnergy.ActualZero

def displacement (ρ : ActualZero) : ℝ := (ρ : ℂ).re - 1 / 2

def decay (x : ℝ) (ρ : ActualZero) : ℝ :=
  x ^ 2 + (ρ : ℂ).im ^ 2 - displacement ρ ^ 2

def laplaceMass (x : ℝ) (ρ : ActualZero) : ℝ :=
  (zeroMult (ρ : ℂ) : ℝ) / decay x ρ

theorem displacement_sq_le (ρ : ActualZero) : displacement ρ ^ 2 ≤ 1 / 4 := by
  have hs : IsNontrivialZero (ρ : ℂ) := ρ.property
  dsimp [displacement]
  nlinarith [hs.2.1, hs.2.2, sq_nonneg ((ρ : ℂ).re - 1 / 2)]

theorem decay_pos {x : ℝ} (hx : 1 / 2 < x) (ρ : ActualZero) :
    0 < decay x ρ := by
  have hd := displacement_sq_le ρ
  dsimp [decay]
  nlinarith [sq_nonneg (ρ : ℂ).im]

theorem laplaceMass_nonneg (x : ℝ) (ρ : ActualZero) (hx : 1 / 2 < x) :
    0 ≤ laplaceMass x ρ := by
  unfold laplaceMass
  exact div_nonneg (by positivity) (le_of_lt (decay_pos hx ρ))

/-- A concrete positive majorant retaining the whole horizontal square. -/
theorem laplaceMass_le_inv_sq {x : ℝ} (hx : 1 / 2 < x) (ρ : ActualZero) :
    laplaceMass x ρ ≤ (1 + (5 / 4 : ℝ) / (x ^ 2 - 1 / 4)) *
      ((zeroMult (ρ : ℂ) : ℝ) / (1 + normSq (gammaOf (ρ : ℂ)))) := by
  let κ : ℝ := x ^ 2 - 1 / 4
  let C : ℝ := 1 + (5 / 4 : ℝ) / κ
  let y : ℝ := (ρ : ℂ).im ^ 2
  let q : ℝ := displacement ρ ^ 2
  let B : ℝ := 1 + normSq (gammaOf (ρ : ℂ))
  let D : ℝ := decay x ρ
  let M : ℝ := (zeroMult (ρ : ℂ) : ℝ)
  have hκ : 0 < κ := by dsimp [κ]; nlinarith
  have hq : q ≤ 1 / 4 := displacement_sq_le ρ
  have hy : 0 ≤ y := sq_nonneg _
  have hD : 0 < D := decay_pos hx ρ
  have hB_eq : B = 1 + y + q := by
    dsimp [B, y, q, displacement]
    rw [normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    ring
  have hB : 0 < B := by
    rw [hB_eq]
    dsimp [y, q]
    positivity
  have hD_eq : D = κ + y + (1 / 4 - q) := by
    dsimp [D, decay, κ, y, q]
    ring
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (by positivity)
  have hCκ : C * κ = κ + 5 / 4 := by
    dsimp [C]
    rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hκ)]
  have hCy : y ≤ C * y := by
    simpa using mul_le_mul_of_nonneg_right hC1 hy
  have hDC : C * (κ + y) ≤ C * D :=
    mul_le_mul_of_nonneg_left (by rw [hD_eq]; linarith) (le_of_lt hC)
  have hmain : B ≤ C * D := by
    rw [hB_eq]
    nlinarith only [hCκ, hCy, hDC, hq, hκ]
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmul : M * B ≤ (C * M) * D := by
    have h := mul_le_mul_of_nonneg_left hmain hM
    nlinarith only [h]
  change M / D ≤ C * (M / B)
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ hD hB).2 hmul

theorem laplaceMass_summable {x : ℝ} (hx : 1 / 2 < x) :
    Summable (laplaceMass x) := by
  have hknown := Zeta23.WeilEF.zero_sum_inv_sq zetaSeam
  have hdom := hknown.mul_left (1 + (5 / 4 : ℝ) / (x ^ 2 - 1 / 4))
  exact Summable.of_nonneg_of_le
    (fun ρ => laplaceMass_nonneg x ρ hx)
    (fun ρ => laplaceMass_le_inv_sq hx ρ) hdom


/-- Countability follows from the known summable positive reciprocal mass. -/
instance actualZero_countable : Countable ActualZero := by
  let f : ActualZero → ℝ := fun ρ =>
    (zeroMult (ρ : ℂ) : ℝ) / (1 + normSq (gammaOf (ρ : ℂ)))
  have hf : Summable f := Zeta23.WeilEF.zero_sum_inv_sq zetaSeam
  have hs : Function.support f = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ρ
    change f ρ ≠ 0
    have hm : 0 < (zeroMult (ρ : ℂ) : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one
        (zetaSeam.one_le_mult (ρ : ℂ) ρ.property))
    have hb : 0 < 1 + normSq (gammaOf (ρ : ℂ)) := by
      rw [normSq_apply]
      nlinarith [sq_nonneg (gammaOf (ρ : ℂ)).re,
        sq_nonneg (gammaOf (ρ : ℂ)).im]
    exact ne_of_gt (div_pos hm hb)
  exact Set.countable_univ_iff.mp (hs ▸ hf.countable_support)

open MeasureTheory Set
open ActualZeroHorizontalEnergy GaussianLaplaceBridge

def ordinateRate (x : ℝ) (ρ : ActualZero) : ℂ :=
  ((x ^ 2 + (ρ : ℂ).im ^ 2 : ℝ) : ℂ)

def fullRate (x : ℝ) (ρ : ActualZero) : ℂ :=
  ((x ^ 2 : ℝ) : ℂ) - ((ρ : ℂ) - 1 / 2) ^ 2

theorem ordinateRate_re (x : ℝ) (ρ : ActualZero) :
    (ordinateRate x ρ).re = x ^ 2 + (ρ : ℂ).im ^ 2 := by
  change (((x ^ 2 + (ρ : ℂ).im ^ 2 : ℝ) : ℂ)).re = _
  exact Complex.ofReal_re _

theorem fullRate_re (x : ℝ) (ρ : ActualZero) :
    (fullRate x ρ).re = decay x ρ := by
  simp [fullRate, decay, displacement, pow_two, Complex.mul_re]
  ring

theorem fullRate_re_pos {x : ℝ} (hx : 1 / 2 < x) (ρ : ActualZero) :
    0 < (fullRate x ρ).re := by
  rw [fullRate_re]
  exact decay_pos hx ρ

theorem ordinateRate_re_pos {x : ℝ} (hx : 1 / 2 < x) (ρ : ActualZero) :
    0 < (ordinateRate x ρ).re := by
  rw [ordinateRate_re]
  nlinarith [sq_nonneg (ρ : ℂ).im, sq_nonneg (x - 1 / 2)]

theorem fullRate_mass_summable {x : ℝ} (hx : 1 / 2 < x) :
    Summable (fun ρ : ActualZero => (zeroMult (ρ : ℂ) : ℝ) / (fullRate x ρ).re) := by
  simpa only [fullRate_re] using (show Summable (fun ρ : ActualZero =>
    (zeroMult (ρ : ℂ) : ℝ) / decay x ρ) from laplaceMass_summable hx)

theorem ordinateRate_mass_summable {x : ℝ} (hx : 1 / 2 < x) :
    Summable (fun ρ : ActualZero =>
      (zeroMult (ρ : ℂ) : ℝ) / (ordinateRate x ρ).re) := by
  apply Summable.of_nonneg_of_le
    (fun ρ => div_nonneg (Nat.cast_nonneg _) (le_of_lt (ordinateRate_re_pos hx ρ)))
    _ (laplaceMass_summable hx)
  intro ρ
  rw [ordinateRate_re]
  unfold laplaceMass
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (decay_pos hx ρ)
  unfold decay
  nlinarith [sq_nonneg (displacement ρ)]

/-- Multiplicity-weighted trace of the ordinates of all nontrivial zeros. -/
def ordinateHeatTrace (a : ℝ) : ℂ :=
  ∑' ρ : ActualZero, (zeroMult (ρ : ℂ) : ℂ) *
    Complex.exp (-(((ρ : ℂ).im ^ 2 : ℝ) : ℂ) * (a : ℂ))

/-- Signed complex trace retaining the full horizontal coordinate of every zero. -/
def fullHeatTrace (a : ℝ) : ℂ :=
  ∑' ρ : ActualZero, (zeroMult (ρ : ℂ) : ℂ) *
    Complex.exp ((a : ℂ) * ((ρ : ℂ) - 1 / 2) ^ 2)

def damping (x a : ℝ) : ℂ := Complex.exp (-((x ^ 2 : ℝ) : ℂ) * (a : ℂ))

theorem damped_ordinateTerm (x a : ℝ) (ρ : ActualZero) :
    damping x a * ((zeroMult (ρ : ℂ) : ℂ) *
      Complex.exp (-(((ρ : ℂ).im ^ 2 : ℝ) : ℂ) * (a : ℂ))) =
      exponentialKernel (zeroMult (ρ : ℂ)) (ordinateRate x ρ) a := by
  unfold damping exponentialKernel ordinateRate
  calc
    _ = (zeroMult (ρ : ℂ) : ℂ) *
        (Complex.exp (-((x ^ 2 : ℝ) : ℂ) * (a : ℂ)) *
          Complex.exp (-(((ρ : ℂ).im ^ 2 : ℝ) : ℂ) * (a : ℂ))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem damped_fullTerm (x a : ℝ) (ρ : ActualZero) :
    damping x a * ((zeroMult (ρ : ℂ) : ℂ) *
      Complex.exp ((a : ℂ) * ((ρ : ℂ) - 1 / 2) ^ 2)) =
      exponentialKernel (zeroMult (ρ : ℂ)) (fullRate x ρ) a := by
  unfold damping exponentialKernel fullRate
  calc
    _ = (zeroMult (ρ : ℂ) : ℂ) *
        (Complex.exp (-((x ^ 2 : ℝ) : ℂ) * (a : ℂ)) *
          Complex.exp ((a : ℂ) * ((ρ : ℂ) - 1 / 2) ^ 2)) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

theorem damping_ne_zero (x a : ℝ) : damping x a ≠ 0 := Complex.exp_ne_zero _

theorem ordinateHeatTrace_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun ρ : ActualZero => (zeroMult (ρ : ℂ) : ℂ) *
      Complex.exp (-(((ρ : ℂ).im ^ 2 : ℝ) : ℂ) * (a : ℂ))) := by
  have hs := exponentialKernel_summable (fun ρ : ActualZero => zeroMult (ρ : ℂ))
    (ordinateRate 1) (ordinateRate_re_pos (by norm_num))
    (ordinateRate_mass_summable (by norm_num)) ha
  have ht := hs.mul_left (damping 1 a)⁻¹
  apply ht.congr
  intro ρ
  rw [← damped_ordinateTerm]
  simp only [← mul_assoc, inv_mul_cancel₀ (damping_ne_zero 1 a), one_mul]

theorem fullHeatTrace_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun ρ : ActualZero => (zeroMult (ρ : ℂ) : ℂ) *
      Complex.exp ((a : ℂ) * ((ρ : ℂ) - 1 / 2) ^ 2)) := by
  have hs := exponentialKernel_summable (fun ρ : ActualZero => zeroMult (ρ : ℂ))
    (fullRate 1) (fullRate_re_pos (by norm_num))
    (fullRate_mass_summable (by norm_num)) ha
  have ht := hs.mul_left (damping 1 a)⁻¹
  apply ht.congr
  intro ρ
  rw [← damped_fullTerm]
  simp only [← mul_assoc, inv_mul_cancel₀ (damping_ne_zero 1 a), one_mul]

theorem damped_ordinateHeatTrace (x a : ℝ) :
    damping x a * ordinateHeatTrace a =
      ∑' ρ : ActualZero, exponentialKernel (zeroMult (ρ : ℂ)) (ordinateRate x ρ) a := by
  unfold ordinateHeatTrace
  rw [← tsum_mul_left]
  exact tsum_congr (damped_ordinateTerm x a)

theorem damped_fullHeatTrace (x a : ℝ) :
    damping x a * fullHeatTrace a =
      ∑' ρ : ActualZero, exponentialKernel (zeroMult (ρ : ℂ)) (fullRate x ρ) a := by
  unfold fullHeatTrace
  rw [← tsum_mul_left]
  exact tsum_congr (damped_fullTerm x a)


/-- Absolute integrability of the entire damped ordinate trace. -/
theorem damped_ordinateHeatTrace_integrable {x : ℝ} (hx : 1 / 2 < x) :
    IntegrableOn (fun a : ℝ => damping x a * ordinateHeatTrace a) (Ioi 0) := by
  have hi := infinite_exponential_integrable
    (fun ρ : ActualZero => zeroMult (ρ : ℂ)) (ordinateRate x)
    (ordinateRate_re_pos hx) (ordinateRate_mass_summable hx)
  exact hi.congr (Filter.Eventually.of_forall (fun a => (damped_ordinateHeatTrace x a).symm))

/-- Absolute integrability of the entire damped full horizontal trace. -/
theorem damped_fullHeatTrace_integrable {x : ℝ} (hx : 1 / 2 < x) :
    IntegrableOn (fun a : ℝ => damping x a * fullHeatTrace a) (Ioi 0) := by
  have hi := infinite_exponential_integrable
    (fun ρ : ActualZero => zeroMult (ρ : ℂ)) (fullRate x)
    (fullRate_re_pos hx) (fullRate_mass_summable hx)
  exact hi.congr (Filter.Eventually.of_forall (fun a => (damped_fullHeatTrace x a).symm))

theorem damped_heatDefect_integrable {x : ℝ} (hx : 1 / 2 < x) :
    IntegrableOn (fun a : ℝ => damping x a * (ordinateHeatTrace a - fullHeatTrace a))
      (Ioi 0) := by
  have hi := (damped_ordinateHeatTrace_integrable hx).sub
    (damped_fullHeatTrace_integrable hx)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun a => by
    change damping x a * ordinateHeatTrace a - damping x a * fullHeatTrace a =
      damping x a * (ordinateHeatTrace a - fullHeatTrace a)
    ring)

theorem signed_resolvent_summable {x : ℝ} (hx : 1 / 2 < x) :
    Summable (fun ρ : ActualZero => (zeroMult (ρ : ℂ) : ℂ) / ordinateRate x ρ -
      (zeroMult (ρ : ℂ) : ℂ) / fullRate x ρ) :=
  (reciprocalRate_summable (fun ρ : ActualZero => zeroMult (ρ : ℂ))
    (ordinateRate x) (ordinateRate_re_pos hx) (ordinateRate_mass_summable hx)).sub
      (reciprocalRate_summable (fun ρ : ActualZero => zeroMult (ρ : ℂ))
        (fullRate x) (fullRate_re_pos hx) (fullRate_mass_summable hx))

/-- Exact signed infinite Laplace transform for all actual zeros. -/
theorem infinite_signed_gaussian_laplace {x : ℝ} (hx : 1 / 2 < x) :
    (∫ a : ℝ in Ioi 0, damping x a * (ordinateHeatTrace a - fullHeatTrace a)) =
      ∑' ρ : ActualZero, ((zeroMult (ρ : ℂ) : ℂ) / ordinateRate x ρ -
        (zeroMult (ρ : ℂ) : ℂ) / fullRate x ρ) := by
  have hH := ordinateRate_mass_summable hx
  have hF := fullRate_mass_summable hx
  have hpoint : ∀ a : ℝ, 0 < a →
      damping x a * (ordinateHeatTrace a - fullHeatTrace a) =
        ∑' ρ : ActualZero, signedExponentialKernel (zeroMult (ρ : ℂ))
          (ordinateRate x ρ) (fullRate x ρ) a := by
    intro a ha
    rw [mul_sub, damped_ordinateHeatTrace, damped_fullHeatTrace]
    exact (exponentialKernel_summable (fun ρ : ActualZero => zeroMult (ρ : ℂ))
      (ordinateRate x) (ordinateRate_re_pos hx) hH ha).tsum_sub
        (exponentialKernel_summable (fun ρ : ActualZero => zeroMult (ρ : ℂ))
          (fullRate x) (fullRate_re_pos hx) hF ha) |>.symm
  calc
    _ = ∫ a : ℝ in Ioi 0, ∑' ρ : ActualZero,
        signedExponentialKernel (zeroMult (ρ : ℂ)) (ordinateRate x ρ) (fullRate x ρ) a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact fun a ha => hpoint a ha
    _ = _ := infinite_signed_exponential_integral
      (fun ρ : ActualZero => zeroMult (ρ : ℂ)) (ordinateRate x) (fullRate x)
      (ordinateRate_re_pos hx) (fullRate_re_pos hx) hH hF

end RiemannResearch.Analysis.ActualZeroGaussianLaplace
