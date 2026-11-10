/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.WeightedSqrtTransfer
import RiemannResearch.Analysis.MontgomeryHorizontalBessel
import RiemannResearch.Analysis.MontgomeryHorizontalBound
import Mathlib.MeasureTheory.Function.L2Space
import RiemannResearch.Analysis.MontgomeryGaussianSmoothing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Averaged horizontal transfer for actual Fourier pairings

Source: the complex-zero pair framework of
Baluyot--Goldston--Suriajaya--Turnage-Butterbaugh, Acta Arithmetica 214
(2024), https://doi.org/10.4064/aa230612-20-3, supplies the conventions
used by the previously checked horizontal-transfer module. No
asymptotic result from that reference is imported as an assumption.

We retain the exact signed cross term and defect square. The resulting
test-pairing estimate uses the averaged one-point budget, with no
pointwise-uniform density hypothesis in the Fourier variable. The last
theorem additionally removes the already controlled Gaussian Fourier
damping. Its averaged budget and complex pairing limit are explicit conditional
research inputs. One criterion uses a bounded complex reference pairing;
the logarithmically stronger budget criterion removes that premise using
the unconditional raw local-mass estimate.

This module concerns the hard-height-cutoff pair statistics already
defined in MontgomeryHorizontalTransfer. It does not transfer a
full-height smoothed single-zero matrix to these pair statistics.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalPairing
open MontgomeryHorizontalTransfer MontgomeryHorizontalBessel MontgomeryFormFactor
open MontgomeryGaussianSmoothing WeightedSqrtTransfer

open scoped ComplexConjugate

theorem complex_norm_sq_add (z w : ℂ) :
    ‖z+w‖^2 = ‖z‖^2 + 2*(z*conj w).re + ‖w‖^2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

def signedHorizontalCross (T u : ℝ) : ℝ :=
  ∫ s, Real.exp (-2*|s|) *
    (ActualZeroOrdinate.ordinateSum T (u+s) *
      conj (ActualZeroOrdinate.coshCorrection T (u+s))).re

theorem horizontal_cross_integrable (T u : ℝ) :
    Integrable (fun s => Real.exp (-2*|s|) *
      (ActualZeroOrdinate.ordinateSum T (u+s) *
        conj (ActualZeroOrdinate.coshCorrection T (u+s))).re) := by
  have hraw := (memLp_two_iff_integrable_sq_norm
    (weightedOrdinate_memLp T u).aestronglyMeasurable).mp (weightedOrdinate_memLp T u)
  have hsharp := (memLp_two_iff_integrable_sq_norm
    (weightedLandau_memLp T u).aestronglyMeasurable).mp (weightedLandau_memLp T u)
  simp only [weightedOrdinate, weightedLandau, weighted_mul_sq] at hraw hsharp
  have hdef := MontgomeryHorizontalBound.integrable_actualDefect T u
  have he (s : ℝ) : Real.exp (-2*|s|) *
      (ActualZeroOrdinate.ordinateSum T (u+s) *
        conj (ActualZeroOrdinate.coshCorrection T (u+s))).re =
      (Real.exp (-2*|s|)*‖ActualZeroOrdinate.landauSum T (u+s)‖^2 -
        Real.exp (-2*|s|)*‖ActualZeroOrdinate.ordinateSum T (u+s)‖^2 -
        Real.exp (-2*|s|)*‖ActualZeroOrdinate.coshCorrection T (u+s)‖^2) / 2 := by
    have hz : ActualZeroOrdinate.landauSum T (u+s) =
        ActualZeroOrdinate.ordinateSum T (u+s) + ActualZeroOrdinate.coshCorrection T (u+s) := by
      rw [ActualZeroOrdinate.exact_signed_correction]
      ring
    rw [hz, complex_norm_sq_add]
    ring
  apply (((hsharp.sub hraw).sub hdef).div_const 2).congr
  filter_upwards with s
  exact (he s).symm

/-- The signed cross term and the nonnegative defect square are both retained. -/
theorem sharp_sub_raw_exact (T u : ℝ) :
    sharpIntegral T u - rawIntegral T u =
      2*signedHorizontalCross T u + defectIntegral T u := by
  have hraw := (memLp_two_iff_integrable_sq_norm
    (weightedOrdinate_memLp T u).aestronglyMeasurable).mp (weightedOrdinate_memLp T u)
  have hsharp := (memLp_two_iff_integrable_sq_norm
    (weightedLandau_memLp T u).aestronglyMeasurable).mp (weightedLandau_memLp T u)
  simp only [weightedOrdinate, weightedLandau, weighted_mul_sq] at hraw hsharp
  unfold sharpIntegral rawIntegral signedHorizontalCross defectIntegral
  rw [← integral_sub hsharp hraw, ← integral_const_mul,
    ← integral_add ((horizontal_cross_integrable T u).const_mul 2)
      (MontgomeryHorizontalBound.integrable_actualDefect T u)]
  apply integral_congr_ae
  filter_upwards with s
  have hz : ActualZeroOrdinate.landauSum T (u+s) =
      ActualZeroOrdinate.ordinateSum T (u+s) + ActualZeroOrdinate.coshCorrection T (u+s) := by
    rw [ActualZeroOrdinate.exact_signed_correction]
    ring
  rw [hz, complex_norm_sq_add]
  ring

def averagedBudget (T : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ α, |f α| * (horizontalBudget T (α * Real.log T) / T)

theorem continuous_budget (T : ℝ) :
    Continuous (fun α => horizontalBudget T (α * Real.log T) / T) := by
  unfold horizontalBudget
  fun_prop

theorem continuous_sharpFormFactor (T : ℝ) : Continuous (sharpFormFactor T) := by
  have he : sharpFormFactor T = fun α =>
      (actualComplexPairSum T (α*Real.log T)).re / (T*Real.log T/(2*Real.pi)) := by
    funext α
    exact sharpFormFactor_eq_actualComplexPairSum T α
  rw [he]
  unfold actualComplexPairSum ActualZeroOrdinate.sum complexPairTerm
  fun_prop

theorem sharpFormFactor_nonneg {T : ℝ} (hT : 1 < T) (α : ℝ) :
    0 ≤ sharpFormFactor T α := by
  unfold sharpFormFactor sharpIntegral
  apply div_nonneg (integral_nonneg (fun _ => by positivity))
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos hT
  positivity

theorem averagedBudget_nonneg {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ) :
    0 ≤ averagedBudget T f := by
  apply integral_nonneg
  intro α
  exact mul_nonneg (abs_nonneg _) (div_nonneg (horizontalBudget_nonneg _ _) hT)

/-- One-point averaged horizontal control for signed Fourier tests.
No uniformity in the Fourier variable is required. -/
theorem exists_pairing_error_le_young :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 9 ≤ T → ∀ f : ℝ → ℝ,
      Continuous f → HasCompactSupport f → ∀ ε : ℝ, 0 < ε →
      |(∫ α, f α * formFactor T α) - (∫ α, f α * sharpFormFactor T α)| ≤
        ε * (∫ α, |f α| * sharpFormFactor T α) +
          (1+1/ε) * C * averagedBudget T f := by
  obtain ⟨C,hC,hb⟩ := exists_horizontalDefect_le_budget
  refine ⟨C,hC,?_⟩
  intro T hT f hf hfc ε hε
  have ht : 0 < T := by linarith
  let d : ℝ → ℝ := fun α => C * (horizontalBudget T (α * Real.log T) / T)
  have hd : Continuous d := (continuous_budget T).const_mul C
  have hd0 : ∀ α, 0 ≤ d α := fun α =>
    mul_nonneg hC.le (div_nonneg (horizontalBudget_nonneg _ _) ht.le)
  have hpoint (α : ℝ) :
      |Real.sqrt (formFactor T α) - Real.sqrt (sharpFormFactor T α)| ≤
        Real.sqrt (d α) := by
    rw [abs_sub_comm]
    apply (sqrt_horizontal_error T α).trans
    apply Real.sqrt_le_sqrt
    simpa only [d, mul_div_assoc] using hb T α hT
  have h := pairing_error_le_young f (formFactor T) (sharpFormFactor T) d
    hf hfc (continuous_formFactor T) (continuous_sharpFormFactor T) hd
    (fun α => formFactor_nonneg (by linarith) α)
    (fun α => sharpFormFactor_nonneg (by linarith) α) hd0 hpoint hε
  have he : (∫ α, |f α| * d α) = C * averagedBudget T f := by
    unfold averagedBudget
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with α
    dsimp [d]
    ring
  rw [he] at h
  simpa only [mul_assoc] using h

/-- A dominated family permits shrinking Fourier damping without a uniform
pointwise zero-density hypothesis. -/
theorem pairing_sub_tendsto_zero_of_averagedBudget
    (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hf : ∀ T, Continuous (f T)) (hfc : ∀ T, HasCompactSupport (f T))
    (hfg : ∀ T α, |f T α| ≤ |g α|)
    (M : ℝ) (hM : 0 ≤ M)
    (hsharp : ∀ᶠ T in atTop, (∫ α, |g α| * sharpFormFactor T α) ≤ M)
    (hbudget : Tendsto (fun T => averagedBudget T g) atTop (nhds 0)) :
    Tendsto (fun T => (∫ α, f T α * formFactor T α) -
      (∫ α, f T α * sharpFormFactor T α)) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_pairing_error_le_young
  apply tendsto_zero_of_young_bounds _ (fun T => ∫ α, |g α| * sharpFormFactor T α)
    (fun T => C * averagedBudget T g) M hM hsharp
    (by simpa using hbudget.const_mul C)
  intro ε hε
  filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
  have ht : 0 < T := by linarith
  have hsf : (∫ α, |f T α| * sharpFormFactor T α) ≤
      ∫ α, |g α| * sharpFormFactor T α := by
    apply integral_mono
      (((hf T).abs.mul (continuous_sharpFormFactor T)).integrable_of_hasCompactSupport
        (hfc T).abs.mul_right)
      ((hg.abs.mul (continuous_sharpFormFactor T)).integrable_of_hasCompactSupport
        hgc.abs.mul_right)
    intro α
    exact mul_le_mul_of_nonneg_right (hfg T α)
      (sharpFormFactor_nonneg (by linarith) α)
  have hbf : averagedBudget T (f T) ≤ averagedBudget T g := by
    apply integral_mono
      (((hf T).abs.mul (continuous_budget T)).integrable_of_hasCompactSupport
        (hfc T).abs.mul_right)
      ((hg.abs.mul (continuous_budget T)).integrable_of_hasCompactSupport
        hgc.abs.mul_right)
    intro α
    exact mul_le_mul_of_nonneg_right (hfg T α)
      (div_nonneg (horizontalBudget_nonneg _ _) ht.le)
  have hh := hbound T hT (f T) (hf T) (hfc T) ε hε
  have heps : 0 ≤ (1+1/ε)*C := by positivity
  calc
    _ ≤ ε * (∫ α, |f T α| * sharpFormFactor T α) +
          (1+1/ε)*C*averagedBudget T (f T) := hh
    _ ≤ ε * (∫ α, |g α| * sharpFormFactor T α) +
          (1+1/ε)*C*averagedBudget T g :=
      add_le_add (mul_le_mul_of_nonneg_left hsf hε.le)
        (mul_le_mul_of_nonneg_left hbf heps)
    _ = _ := by ring

/-- Actual raw ordinate pairings inherit a Gaussian-damped complex-zero
pairing limit from an averaged one-point horizontal budget. The budget and
complex pairing asymptotic remain explicit research hypotheses. -/
theorem raw_pairing_limit_of_damped_complex
    (f : ℝ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (M : ℝ) (hM : 0 ≤ M)
    (hsharp : ∀ᶠ T in atTop, (∫ α, |f α| * sharpFormFactor T α) ≤ M)
    (hbudget : Tendsto (fun T => averagedBudget T f) atTop (nhds 0))
    {l : ℝ}
    (hdamped : Tendsto (fun T => ∫ α,
      f α * Real.exp (-((α / Real.log T) ^ 2)) * sharpFormFactor T α)
      atTop (nhds l)) :
    Tendsto (fun T => ∫ α, f α * formFactor T α) atTop (nhds l) := by
  let d : ℝ → ℝ → ℝ := fun T α => f α * Real.exp (-((α / Real.log T)^2))
  have hdc : ∀ T, Continuous (d T) := by intro T; dsimp [d]; fun_prop
  have hdcomp : ∀ T, HasCompactSupport (d T) := by
    intro T
    exact hfc.mul_right
  have hdom : ∀ T α, |d T α| ≤ |f α| := by
    intro T α
    dsimp [d]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ |f α| * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))) (abs_nonneg _)
      _ = _ := mul_one _
  have hh := pairing_sub_tendsto_zero_of_averagedBudget d f hf hfc hdc hdcomp
    hdom M hM hsharp hbudget
  have hm : Integrable (fun α => α^2 * |f α|) :=
    ((continuous_id.pow 2).mul hf.abs).integrable_of_hasCompactSupport hfc.abs.mul_left
  have hg := actual_reciprocal_log_pairing_sub_tendsto_zero
    (hf.integrable_of_hasCompactSupport hfc) hm
  have hsum := (hg.add hh).add hdamped
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards with T
  dsimp [d]
  ring


/-- The symmetric estimate takes the unconditional raw statistic as reference. -/
theorem exists_pairing_error_le_young_raw_reference :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 9 ≤ T → ∀ f : ℝ → ℝ,
      Continuous f → HasCompactSupport f → ∀ ε : ℝ, 0 < ε →
      |(∫ α, f α * formFactor T α) - (∫ α, f α * sharpFormFactor T α)| ≤
        ε * (∫ α, |f α| * formFactor T α) +
          (1 + 1 / ε) * C * averagedBudget T f := by
  obtain ⟨C,hC,hb⟩ := exists_horizontalDefect_le_budget
  refine ⟨C,hC,?_⟩
  intro T hT f hf hfc ε hε
  have ht : 0 < T := by linarith
  let d : ℝ → ℝ := fun α => C * (horizontalBudget T (α * Real.log T) / T)
  have hd : Continuous d := (continuous_budget T).const_mul C
  have hd0 : ∀ α, 0 ≤ d α := fun α =>
    mul_nonneg hC.le (div_nonneg (horizontalBudget_nonneg _ _) ht.le)
  have hpoint (α : ℝ) :
      |Real.sqrt (sharpFormFactor T α) - Real.sqrt (formFactor T α)| ≤
        Real.sqrt (d α) := by
    apply (sqrt_horizontal_error T α).trans
    apply Real.sqrt_le_sqrt
    simpa only [d, mul_div_assoc] using hb T α hT
  have h := pairing_error_le_young f (sharpFormFactor T) (formFactor T) d
    hf hfc (continuous_sharpFormFactor T) (continuous_formFactor T) hd
    (fun α => sharpFormFactor_nonneg (by linarith) α)
    (fun α => formFactor_nonneg (by linarith) α) hd0 hpoint hε
  have he : (∫ α, |f α| * d α) = C * averagedBudget T f := by
    unfold averagedBudget
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with α
    dsimp [d]
    ring
  rw [he] at h
  simpa only [abs_sub_comm, mul_assoc] using h

private theorem normalize_young_bound {x R B L C M ε : ℝ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε)
    (hR : R ≤ C * L * M)
    (hx : x ≤ (ε / (1 + L)) * R + (1 + 1 / (ε / (1 + L))) * B) :
    x ≤ ε * (C * M) + (1 + 1 / ε) * ((1 + L) * B) := by
  have hden : 0 < 1 + L := by linarith
  have hfrac : L / (1 + L) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hfirst : (ε / (1 + L)) * (C * L * M) ≤ ε * (C * M) := by
    calc
      _ = (ε * (C * M)) * (L / (1 + L)) := by ring
      _ ≤ (ε * (C * M)) * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := mul_one _
  have hid : 1 / (ε / (1 + L)) = (1 + L) / ε := by field_simp
  have hsecond : (1 + 1 / (ε / (1 + L))) * B ≤ (1 + 1 / ε) * ((1 + L) * B) := by
    rw [hid]
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg hL hB]
  exact hx.trans (add_le_add
    ((mul_le_mul_of_nonneg_left hR (by positivity)).trans hfirst) hsecond)

/-- A logarithmically weighted averaged budget eliminates the separate
bounded-complex-pairing input, using the unconditional raw Cauchy bound. -/
theorem pairing_sub_tendsto_zero_of_log_averagedBudget
    (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hf : ∀ T, Continuous (f T)) (hfc : ∀ T, HasCompactSupport (f T))
    (hfg : ∀ T α, |f T α| ≤ |g α|)
    (hbudget : Tendsto (fun T => (1 + Real.log T) * averagedBudget T g)
      atTop (nhds 0)) :
    Tendsto (fun T => (∫ α, f T α * formFactor T α) -
      (∫ α, f T α * sharpFormFactor T α)) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_pairing_error_le_young_raw_reference
  obtain ⟨A,hA,hraw⟩ := MontgomeryLocalMass.exists_formFactor_le_log
  let M : ℝ := ∫ α, |g α|
  have hM : 0 ≤ M := integral_nonneg (fun _ => abs_nonneg _)
  apply tendsto_zero_of_young_bounds _ (fun _ => A * M)
    (fun T => C * ((1 + Real.log T) * averagedBudget T g)) (A * M) (by positivity)
    (Eventually.of_forall (fun _ => le_rfl))
    (by simpa using hbudget.const_mul C)
  intro ε hε
  filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
  have ht : 0 < T := by linarith
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hR : (∫ α, |f T α| * formFactor T α) ≤ A * Real.log T * M := by
    have hgI : Integrable (fun α => |g α|) :=
      hg.abs.integrable_of_hasCompactSupport hgc.abs
    calc
      _ ≤ ∫ α, (A * Real.log T)*|g α| := by
        apply integral_mono
          (((hf T).abs.mul (continuous_formFactor T)).integrable_of_hasCompactSupport
            (hfc T).abs.mul_right)
          (hgI.const_mul _)
        intro α
        calc
          _ ≤ |g α| * (A * Real.log T) := mul_le_mul (hfg T α)
            (hraw T α hT) (formFactor_nonneg (by linarith) α) (abs_nonneg _)
          _ = _ := mul_comm _ _
      _ = _ := by rw [integral_const_mul]
  have hbf : averagedBudget T (f T) ≤ averagedBudget T g := by
    apply integral_mono
      (((hf T).abs.mul (continuous_budget T)).integrable_of_hasCompactSupport
        (hfc T).abs.mul_right)
      ((hg.abs.mul (continuous_budget T)).integrable_of_hasCompactSupport
        hgc.abs.mul_right)
    intro α
    exact mul_le_mul_of_nonneg_right (hfg T α)
      (div_nonneg (horizontalBudget_nonneg _ _) ht.le)
  have he : 0 < ε / (1 + Real.log T) := by positivity
  have hx := hbound T hT (f T) (hf T) (hfc T) (ε / (1 + Real.log T)) he
  have hx' : |(∫ α, f T α * formFactor T α) -
      (∫ α, f T α * sharpFormFactor T α)| ≤
      (ε / (1 + Real.log T)) * (∫ α, |f T α| * formFactor T α) +
        (1 + 1 / (ε / (1 + Real.log T))) * (C * averagedBudget T g) := by
    calc
      _ ≤ _ := hx
      _ ≤ _ := by
        have hn : 0 ≤ (1 + 1 / (ε / (1 + Real.log T))) * C := by positivity
        have hh := mul_le_mul_of_nonneg_left hbf hn
        nlinarith
  have hh := normalize_young_bound hl hA.le hM
    (mul_nonneg hC.le (averagedBudget_nonneg ht.le g)) hε hR hx'
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

/-- With the stronger averaged one-point decay, the Gaussian-damped complex
pairing asymptotic is the sole remaining two-point input. -/
theorem raw_pairing_limit_of_damped_complex_log_budget
    (f : ℝ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hbudget : Tendsto (fun T => (1 + Real.log T) * averagedBudget T f)
      atTop (nhds 0))
    {l : ℝ}
    (hdamped : Tendsto (fun T => ∫ α,
      f α * Real.exp (-((α / Real.log T) ^ 2)) * sharpFormFactor T α)
      atTop (nhds l)) :
    Tendsto (fun T => ∫ α, f α * formFactor T α) atTop (nhds l) := by
  let d : ℝ → ℝ → ℝ := fun T α => f α * Real.exp (-((α / Real.log T) ^ 2))
  have hdc : ∀ T, Continuous (d T) := by intro T; dsimp [d]; fun_prop
  have hdcomp : ∀ T, HasCompactSupport (d T) := by
    intro T
    exact hfc.mul_right
  have hdom : ∀ T α, |d T α| ≤ |f α| := by
    intro T α
    dsimp [d]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ |f α| * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))) (abs_nonneg _)
      _ = _ := mul_one _
  have hh := pairing_sub_tendsto_zero_of_log_averagedBudget d f hf hfc hdc hdcomp
    hdom hbudget
  have hm : Integrable (fun α => α^2 * |f α|) :=
    ((continuous_id.pow 2).mul hf.abs).integrable_of_hasCompactSupport hfc.abs.mul_left
  have hg := actual_reciprocal_log_pairing_sub_tendsto_zero
    (hf.integrable_of_hasCompactSupport hfc) hm
  have hsum := (hg.add hh).add hdamped
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards with T
  dsimp [d]
  ring

end RiemannResearch.Analysis.MontgomeryHorizontalPairing
