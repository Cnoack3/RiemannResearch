import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Actual Lebesgue L² translation inverse for the conductor operator.
Source: user-provided RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md,
section 4 (statement and geometric-series proof strategy).

The proof uses Mathlib's measure-preserving Lp composition and Banach-algebra
geometric series. No inverse or convergence assumption is supplied.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace RiemannResearch.Analysis.ConductorL2Inverse

abbrev L2 := MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)
abbrev Op := L2 →L[ℝ] L2

/-- Translation convention: `translate a f x = f (x-a)` almost everywhere. -/
def translate (a : ℝ) : Op :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => x - a)
    (measurePreserving_sub_right volume a)).toContinuousLinearMap

theorem translate_coe_ae (a : ℝ) (f : L2) :
    translate a f =ᵐ[volume] fun x => f (x - a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume a)

@[simp] theorem translate_zero : translate 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change translate 0 f = f
  apply Lp.ext
  simpa only [sub_zero] using translate_coe_ae 0 f

@[simp] theorem translate_mul (a b : ℝ) :
    translate a * translate b = translate (a + b) := by
  apply ContinuousLinearMap.ext
  intro f
  change Lp.compMeasurePreserving (fun x : ℝ => x - a) _
    (Lp.compMeasurePreserving (fun x : ℝ => x - b) _ f) =
      Lp.compMeasurePreserving (fun x : ℝ => x - (a + b)) _ f
  have hh : (fun x : ℝ => x - b) ∘ (fun x : ℝ => x - a) =
      (fun x : ℝ => x - (a + b)) := by funext x; simp only [Function.comp_apply]; ring
  have h := Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_sub_right volume b) (measurePreserving_sub_right volume a)
  simpa only [hh] using h.symm

@[simp] theorem norm_translate_apply (a : ℝ) (f : L2) :
    ‖translate a f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (measurePreserving_sub_right volume a)

theorem norm_translate_le (a : ℝ) : ‖translate a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp

/-- The scaled actual translation entering the Neumann series. -/
def contraction (q a : ℝ) : Op := q • translate (-a)

/-- The original two-term conductor expression, with `q = n^(-1/2)`. -/
def conductor (q a : ℝ) : Op := q ^ 2 • (1 : Op) - q • translate a

/-- Inverse given by a genuine operator-norm convergent geometric series. -/
def inverse (q a : ℝ) : Op :=
  -(q⁻¹) • ((∑' j : ℕ, contraction q a ^ j) * translate (-a))

private theorem contraction_norm_le {q : ℝ} (hq : 0 ≤ q) (a : ℝ) :
    ‖contraction q a‖ ≤ q := by
  rw [contraction, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
  simpa using mul_le_mul_of_nonneg_left (norm_translate_le (-a)) hq

theorem contraction_powers_summable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (a : ℝ) : Summable (fun j : ℕ => contraction q a ^ j) :=
  summable_geometric_of_norm_lt_one ((contraction_norm_le hq0 a).trans_lt hq1)

private theorem conductor_mul_left_shift (q a : ℝ) :
    conductor q a * translate (-a) = -q • (1 - contraction q a) := by
  simp only [conductor, sub_mul, smul_mul_assoc, one_mul, translate_mul,
    add_neg_cancel, translate_zero, contraction, smul_sub, smul_smul]
  module

private theorem left_shift_mul_conductor (q a : ℝ) :
    translate (-a) * conductor q a = -q • (1 - contraction q a) := by
  simp only [conductor, mul_sub, mul_smul_comm, mul_one, translate_mul,
    neg_add_cancel, translate_zero, contraction, smul_sub, smul_smul]
  module

theorem inverse_mul_conductor {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a : ℝ) :
    inverse q a * conductor q a = 1 := by
  have hn : ‖contraction q a‖ < 1 := (contraction_norm_le hq0.le a).trans_lt hq1
  rw [inverse, smul_mul_assoc, mul_assoc, left_shift_mul_conductor,
    mul_smul_comm, geom_series_mul_neg _ hn, smul_smul]
  simp [ne_of_gt hq0]

private theorem conductor_mul_right_inverse {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (a : ℝ) : conductor q a *
      (-(q⁻¹) • (translate (-a) * ∑' j : ℕ, contraction q a ^ j)) = 1 := by
  have hn : ‖contraction q a‖ < 1 := (contraction_norm_le hq0.le a).trans_lt hq1
  rw [mul_smul_comm, ← mul_assoc, conductor_mul_left_shift,
    smul_mul_assoc, mul_neg_geom_series _ hn, smul_smul]
  simp [ne_of_gt hq0]

theorem conductor_mul_inverse {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a : ℝ) :
    conductor q a * inverse q a = 1 := by
  let R : Op := -(q⁻¹) • (translate (-a) * ∑' j : ℕ, contraction q a ^ j)
  have hR : conductor q a * R = 1 := conductor_mul_right_inverse hq0 hq1 a
  have heq : inverse q a = R := by
    calc
      inverse q a = inverse q a * 1 := (mul_one _).symm
      _ = inverse q a * (conductor q a * R) := by rw [hR]
      _ = (inverse q a * conductor q a) * R := (mul_assoc _ _ _).symm
      _ = R := by rw [inverse_mul_conductor hq0 hq1, one_mul]
  rw [heq, hR]

theorem inverse_hasSum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) :
    HasSum (fun j : ℕ => -(q⁻¹) •
      (contraction q a ^ j * translate (-a))) (inverse q a) := by
  exact ((contraction_powers_summable hq0 hq1 a).hasSum.mul_right
    (translate (-a))).const_smul (-(q⁻¹))

theorem inverse_norm_bound {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a : ℝ) :
    ‖inverse q a‖ ≤ q⁻¹ * (1 - q)⁻¹ := by
  have hn : ‖contraction q a‖ < 1 := (contraction_norm_le hq0.le a).trans_lt hq1
  have hsum : ‖∑' j : ℕ, contraction q a ^ j‖ ≤ (1 - q)⁻¹ := by
    have h0 : ‖(1 : Op)‖ ≤ 1 := by simpa only [← translate_zero] using norm_translate_le 0
    have hi : (1 - ‖contraction q a‖)⁻¹ ≤ (1 - q)⁻¹ := by
      apply inv_anti₀ (sub_pos.mpr hq1)
      linarith [contraction_norm_le hq0.le a]
    have h := tsum_geometric_le_of_norm_lt_one (contraction q a) hn
    linarith
  have hninv : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  calc
    ‖inverse q a‖ = q⁻¹ * ‖(∑' j : ℕ, contraction q a ^ j) * translate (-a)‖ := by
      simp only [inverse, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hninv]
    _ ≤ q⁻¹ * (‖∑' j : ℕ, contraction q a ^ j‖ * ‖translate (-a)‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) hninv
    _ ≤ q⁻¹ * ((1 - q)⁻¹ * 1) := by
      apply mul_le_mul_of_nonneg_left _ hninv
      exact mul_le_mul hsum (norm_translate_le (-a)) (norm_nonneg _)
        (inv_nonneg.mpr (sub_nonneg.mpr hq1.le))
    _ = q⁻¹ * (1 - q)⁻¹ := by rw [mul_one]

end RiemannResearch.Analysis.ConductorL2Inverse

namespace RiemannResearch.Analysis.ConductorL2Inverse

/-- Every Neumann-series term is the specified left translation. -/
theorem contraction_pow (q a : ℝ) (j : ℕ) :
    contraction q a ^ j = q ^ j • translate (-(j : ℝ) * a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih]
    simp only [contraction, smul_mul_assoc, mul_smul_comm,
      smul_smul, translate_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    apply congrArg₂ (fun (r : ℝ) (T : Op) => r • T)
    · ring
    · congr 1
      ring

theorem inverse_hasSum_translations {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) :
    HasSum (fun j : ℕ => (-(q⁻¹) * q ^ j) •
      translate (-((j : ℝ) + 1) * a)) (inverse q a) := by
  convert inverse_hasSum hq0 hq1 a using 1
  funext j
  rw [contraction_pow, smul_mul_assoc, translate_mul, smul_smul]
  congr 2 <;> ring

/-- Critical-line conductor on actual complex-valued Lebesgue L². -/
def natConductor (n : ℕ) : Op :=
  (n : ℝ)⁻¹ • (1 : Op) - (Real.sqrt n)⁻¹ • translate (Real.log n)

/-- The actual bounded inverse, constructed rather than postulated. -/
def natInverse (n : ℕ) : Op := inverse (Real.sqrt n)⁻¹ (Real.log n)

private theorem sqrt_inv_pos_lt_one {n : ℕ} (hn : 1 < n) :
    0 < (Real.sqrt n)⁻¹ ∧ (Real.sqrt n)⁻¹ < 1 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hs : 1 < Real.sqrt n := by
    have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    have hnon := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  have hp : 0 < Real.sqrt n := zero_lt_one.trans hs
  have hi : 0 < (Real.sqrt n)⁻¹ := inv_pos.mpr hp
  have heq : (Real.sqrt n)⁻¹ * Real.sqrt n = 1 := inv_mul_cancel₀ (ne_of_gt hp)
  constructor
  · exact hi
  · nlinarith

private theorem conductor_eq_natConductor (n : ℕ) :
    conductor (Real.sqrt n)⁻¹ (Real.log n) = natConductor n := by
  unfold conductor natConductor
  have hh : (Real.sqrt n)⁻¹ ^ 2 = (n : ℝ)⁻¹ := by
    simpa only [inv_pow] using congrArg (fun x : ℝ => x⁻¹)
      (Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity))
  rw [hh]

theorem natInverse_mul_natConductor {n : ℕ} (hn : 1 < n) :
    natInverse n * natConductor n = 1 := by
  obtain ⟨h0,h1⟩ := sqrt_inv_pos_lt_one hn
  simpa only [natInverse, conductor_eq_natConductor] using
    inverse_mul_conductor h0 h1 (Real.log n)

theorem natConductor_mul_natInverse {n : ℕ} (hn : 1 < n) :
    natConductor n * natInverse n = 1 := by
  obtain ⟨h0,h1⟩ := sqrt_inv_pos_lt_one hn
  simpa only [natInverse, conductor_eq_natConductor] using
    conductor_mul_inverse h0 h1 (Real.log n)

theorem natInverse_hasSum {n : ℕ} (hn : 1 < n) :
    HasSum (fun j : ℕ => (-Real.sqrt n * (Real.sqrt n)⁻¹ ^ j) •
      translate (-((j : ℝ) + 1) * Real.log n)) (natInverse n) := by
  obtain ⟨h0,h1⟩ := sqrt_inv_pos_lt_one hn
  simpa only [natInverse, inv_inv] using inverse_hasSum_translations h0.le h1 (Real.log n)

theorem natInverse_norm_bound {n : ℕ} (hn : 1 < n) :
    ‖natInverse n‖ ≤ (n : ℝ) / (Real.sqrt n - 1) := by
  obtain ⟨h0,h1⟩ := sqrt_inv_pos_lt_one hn
  have hb := inverse_norm_bound h0 h1 (Real.log n)
  have hs0 : Real.sqrt n ≠ 0 := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
    exact ne_of_gt (Real.sqrt_pos.mpr hn0)
  have hs1 : Real.sqrt n - 1 ≠ 0 := by
    intro h
    have hh : Real.sqrt n = 1 := by linarith
    simp [hh] at h1
  have heq : ((Real.sqrt n)⁻¹)⁻¹ * (1 - (Real.sqrt n)⁻¹)⁻¹ =
      (n : ℝ) / (Real.sqrt n - 1) := by
    rw [inv_inv]
    have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    field_simp
    nlinarith
  simpa only [natInverse, heq] using hb

/-- Every L² input has exactly one L² inverse image. -/
theorem natConductor_bijective {n : ℕ} (hn : 1 < n) :
    Function.Bijective (natConductor n) := by
  constructor
  · intro f g h
    have hh := congrArg (natInverse n) h
    have hf : natInverse n (natConductor n f) = f := by
      change (natInverse n * natConductor n) f = f
      rw [natInverse_mul_natConductor hn]
      rfl
    have hg : natInverse n (natConductor n g) = g := by
      change (natInverse n * natConductor n) g = g
      rw [natInverse_mul_natConductor hn]
      rfl
    rwa [hf, hg] at hh
  · intro f
    refine ⟨natInverse n f, ?_⟩
    change (natConductor n * natInverse n) f = f
    rw [natConductor_mul_natInverse hn]
    rfl

end RiemannResearch.Analysis.ConductorL2Inverse
