/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoCompactSourceLimits
import RiemannResearch.RH.CanonicalMobiusPNT
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact compact trial decomposition and unconditional sublinear full energy

Source: user-requested actual-source arithmetic work, 7 October 2026.
The fourfold identity is derived from the existing shifted Mobius formula
and canonical floor expansions. All conductors, boundaries, signed cross
terms and complete physical norms are retained. The asymptotic input is
the already formalized unconditional canonicalMobiusHilbert_sublinear
in CanonicalMobiusPNT.lean, which records its PNT provenance.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.NumberTheory

private theorem shifted_floor_sum_dilation (Y j h : ℕ) (hh : 0 < h) :
    (∑ d ∈ Finset.Icc 1 Y,
      (if h ∣ d then (ArithmeticFunction.moebius (d / h) : ℝ) else 0) *
        ((j / d : ℕ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 (Y / h),
        (ArithmeticFunction.moebius d : ℝ) * (((j / h) / d : ℕ) : ℝ) := by
  have he (d : ℕ) :
      (if h ∣ d then (ArithmeticFunction.moebius (d / h) : ℝ) else 0) *
          ((j / d : ℕ) : ℝ) =
        if h ∣ d then
          (ArithmeticFunction.moebius (d / h) : ℝ) *
            (((j / h) / (d / h) : ℕ) : ℝ)
        else 0 := by
    by_cases hd : h ∣ d
    · have hq : (j / h) / (d / h) = j / d := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' hd]
      simp [hd, hq]
    · simp [hd]
  simp_rw [he]
  exact positive_dilation_sum Y h hh
    (fun d => (ArithmeticFunction.moebius d : ℝ) * (((j / h) / d : ℕ) : ℝ))

theorem compactShiftedMobius_floor_sum_eq_dilations (Y j : ℕ) :
    (∑ d ∈ Finset.Icc 1 Y,
      compactShiftedMobius d * ((j / d : ℕ) : ℝ)) =
      14 * (∑ d ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius d : ℝ) * ((j / d : ℕ) : ℝ)) -
      26 * (∑ d ∈ Finset.Icc 1 (Y / 2),
        (ArithmeticFunction.moebius d : ℝ) * (((j / 2) / d : ℕ) : ℝ)) +
      12 * (∑ d ∈ Finset.Icc 1 (Y / 4),
        (ArithmeticFunction.moebius d : ℝ) * (((j / 4) / d : ℕ) : ℝ)) := by
  simp only [compactShiftedMobius_formula, add_mul, sub_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [shifted_floor_sum_dilation Y j 2 (by decide),
    shifted_floor_sum_dilation Y j 4 (by decide)]

/-- Full floor identity on every site, with no head-window restriction. -/
theorem compactCorrectedTrial_floor_expansion_all (N j : ℕ) (hN : 0 < N) :
    compactCorrectedTrial N j =
      (∑ d ∈ Finset.Icc 1 N, compactShiftedMobius d * ((j / d : ℕ) : ℝ)) -
        (N : ℝ) * compactReciprocalSum N * ((j / N : ℕ) : ℝ) := by
  have hsum :
      (∑ d ∈ Finset.Icc 1 N, compactShiftedMobius d * residueFraction d j) =
        (j : ℝ) * compactReciprocalSum N -
          ∑ d ∈ Finset.Icc 1 N, compactShiftedMobius d * ((j / d : ℕ) : ℝ) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 N,
          ((j : ℝ) * (compactShiftedMobius d / (d : ℝ)) -
            compactShiftedMobius d * ((j / d : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [residueFraction_eq_div_sub_floor d j (Finset.mem_Icc.mp hd).1]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
  unfold compactCorrectedTrial
  rw [hsum, residueFraction_eq_div_sub_floor N j hN]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp [hNR]
  ring

/-- The last shifted-Mobius term cancels the exact boundary charge increment. -/
theorem compactCorrectedTrial_succ_floor_expansion (Y j : ℕ) :
    compactCorrectedTrial (Y + 1) j =
      (∑ d ∈ Finset.Icc 1 Y, compactShiftedMobius d * ((j / d : ℕ) : ℝ)) -
        ((Y + 1 : ℕ) : ℝ) * compactReciprocalSum Y * ((j / (Y + 1) : ℕ) : ℝ) := by
  have hcharge : compactReciprocalSum (Y + 1) = compactReciprocalSum Y +
      compactShiftedMobius (Y + 1) / ((Y + 1 : ℕ) : ℝ) := by
    unfold compactReciprocalSum
    rw [Finset.sum_Icc_succ_top (by omega)]
  rw [compactCorrectedTrial_floor_expansion_all (Y + 1) j (by omega),
    Finset.sum_Icc_succ_top (by omega), hcharge]
  have hYR : ((Y + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hYR]
  ring

/-- Exact cofinal arithmetic decomposition into three existing full canonical families. -/
theorem compactCorrectedHilbert_fourfold_eq_canonical (m : ℕ) :
    compactCorrectedHilbert (4 * m + 4) (by omega) =
      (14 : ℝ) • canonicalMobiusHilbert (4 * m + 3) -
        (13 : ℝ) • hilbertDilation 2 (by decide) (canonicalMobiusHilbert (2 * m + 1)) +
        (3 : ℝ) • hilbertDilation 4 (by decide) (canonicalMobiusHilbert m) := by
  apply hilbertSequence_injective
  rw [compactCorrectedHilbert_sequence]
  simp only [hilbertSequence_add, hilbertSequence_sub, hilbertSequence_smul,
    hilbertDilation_sequence, canonicalMobiusHilbert_sequence]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dilation]
  have hN : 4 * m + 3 + 1 = 4 * m + 4 := by omega
  have h2 : (4 * m + 3) / 2 = 2 * m + 1 := by omega
  have h4 : (4 * m + 3) / 4 = m := by omega
  have hu := compactCorrectedTrial_succ_floor_expansion (4 * m + 3) j
  rw [hN, compactShiftedMobius_floor_sum_eq_dilations,
    compactReciprocalSum_eq_dilations, h2, h4] at hu
  rw [hu]
  rw [canonicalMobiusHead_floor_expansion (4 * m + 3) j,
    canonicalMobiusHead_floor_expansion (2 * m + 1) (j / 2),
    canonicalMobiusHead_floor_expansion m (j / 4)]
  have hdiv2 : (j / 2) / (2 * m + 1 + 1) = j / (4 * m + 4) := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    omega
  have hdiv4 : (j / 4) / (m + 1) = j / (4 * m + 4) := by
    rw [Nat.div_div_eq_div_mul]
    congr 1
  rw [hN, hdiv2, hdiv4]
  push_cast
  ring

/-- Complete signed norm expansion before any upper estimate. -/
theorem compactCorrectedHilbert_fourfold_norm_sq_exact (m : ℕ) :
    ‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2 =
      196 * ‖canonicalMobiusHilbert (4 * m + 3)‖ ^ 2 +
      338 * ‖canonicalMobiusHilbert (2 * m + 1)‖ ^ 2 +
      36 * ‖canonicalMobiusHilbert m‖ ^ 2 -
      364 * inner ℝ (canonicalMobiusHilbert (4 * m + 3))
        (hilbertDilation 2 (by decide) (canonicalMobiusHilbert (2 * m + 1))) +
      84 * inner ℝ (canonicalMobiusHilbert (4 * m + 3))
        (hilbertDilation 4 (by decide) (canonicalMobiusHilbert m)) -
      78 * inner ℝ (hilbertDilation 2 (by decide) (canonicalMobiusHilbert (2 * m + 1)))
        (hilbertDilation 4 (by decide) (canonicalMobiusHilbert m)) := by
  rw [compactCorrectedHilbert_fourfold_eq_canonical, norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    hilbertDilation_norm_sq, inner_sub_left, inner_smul_left, inner_smul_right]
  norm_num
  ring

/-- All three complete squares dominate the complete signed expression. -/
theorem compactCorrectedHilbert_fourfold_norm_sq_le (m : ℕ) :
    ‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2 ≤
      3 * (196 * ‖canonicalMobiusHilbert (4 * m + 3)‖ ^ 2 +
        338 * ‖canonicalMobiusHilbert (2 * m + 1)‖ ^ 2 +
        36 * ‖canonicalMobiusHilbert m‖ ^ 2) := by
  rw [compactCorrectedHilbert_fourfold_eq_canonical]
  let a := (14 : ℝ) • canonicalMobiusHilbert (4 * m + 3)
  let b := (13 : ℝ) • hilbertDilation 2 (by decide) (canonicalMobiusHilbert (2 * m + 1))
  let c := (3 : ℝ) • hilbertDilation 4 (by decide) (canonicalMobiusHilbert m)
  have hn : ‖a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le (a - b) c).trans
      (by nlinarith [norm_sub_le a b])
  have hs := mul_self_le_mul_self (norm_nonneg (a - b + c)) hn
  have h3 : ‖a - b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]
  dsimp [a, b, c] at h3
  simp only [norm_smul, Real.norm_eq_abs, mul_pow,
    show |(14 : ℝ)| = 14 by norm_num,
    show |(13 : ℝ)| = 13 by norm_num,
    show |(3 : ℝ)| = 3 by norm_num,
    hilbertDilation_norm_sq] at h3
  norm_num at h3
  nlinarith

open Filter
open scoped Topology

private theorem affine_cutoff_tendsto (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun m : ℕ => a * m + b) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with m hm
  nlinarith

/-- The actual legal compact trial has unconditional sublinear full energy
on a specified cofinal sequence; no norm or arithmetic provider is assumed. -/
theorem compactCorrectedHilbert_fourfold_sublinear :
    Tendsto (fun m : ℕ =>
      ‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2 / (4 * m + 4 : ℕ))
      atTop (𝓝 0) := by
  have h4 := canonicalMobiusHilbert_sublinear.comp
    (affine_cutoff_tendsto 4 3 (by decide))
  have h2 := canonicalMobiusHilbert_sublinear.comp
    (affine_cutoff_tendsto 2 1 (by decide))
  have h1 := canonicalMobiusHilbert_sublinear
  have hlim : Tendsto (fun m : ℕ =>
      3 * (196 * (‖canonicalMobiusHilbert (4 * m + 3)‖ ^ 2 / (4 * m + 3 : ℕ)) +
        338 * (‖canonicalMobiusHilbert (2 * m + 1)‖ ^ 2 / (2 * m + 1 : ℕ)) +
        36 * (‖canonicalMobiusHilbert m‖ ^ 2 / (m : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using
      (((h4.const_mul 196).add (h2.const_mul 338)).add (h1.const_mul 36)).const_mul 3
  apply squeeze_zero' (Eventually.of_forall (fun m =>
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))) _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hN : (0 : ℝ) < (4 * m + 4 : ℕ) := by positivity
  have h4pos : (0 : ℝ) < (4 * m + 3 : ℕ) := by positivity
  have h2pos : (0 : ℝ) < (2 * m + 1 : ℕ) := by positivity
  have h1pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h4le : (4 * m + 3 : ℕ) ≤ 4 * m + 4 := by omega
  have h2le : (2 * m + 1 : ℕ) ≤ 4 * m + 4 := by omega
  have h1le : m ≤ 4 * m + 4 := by omega
  have h4div : ‖canonicalMobiusHilbert (4 * m + 3)‖ ^ 2 / (4 * m + 4 : ℕ) ≤
      ‖canonicalMobiusHilbert (4 * m + 3)‖ ^ 2 / (4 * m + 3 : ℕ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) h4pos (by exact_mod_cast h4le)
  have h2div : ‖canonicalMobiusHilbert (2 * m + 1)‖ ^ 2 / (4 * m + 4 : ℕ) ≤
      ‖canonicalMobiusHilbert (2 * m + 1)‖ ^ 2 / (2 * m + 1 : ℕ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) h2pos (by exact_mod_cast h2le)
  have h1div : ‖canonicalMobiusHilbert m‖ ^ 2 / (4 * m + 4 : ℕ) ≤
      ‖canonicalMobiusHilbert m‖ ^ 2 / (m : ℝ) :=
    div_le_div_of_nonneg_left (sq_nonneg _) h1pos (by exact_mod_cast h1le)
  have hnorm := div_le_div_of_nonneg_right
    (compactCorrectedHilbert_fourfold_norm_sq_le m) hN.le
  calc
    _ ≤ (3 * (196 * ‖canonicalMobiusHilbert (4 * m + 3)‖ ^ 2 +
        338 * ‖canonicalMobiusHilbert (2 * m + 1)‖ ^ 2 +
        36 * ‖canonicalMobiusHilbert m‖ ^ 2)) / (4 * m + 4 : ℕ) := hnorm
    _ = 3 * (196 * (‖canonicalMobiusHilbert (4 * m + 3)‖ ^ 2 / (4 * m + 4 : ℕ)) +
        338 * (‖canonicalMobiusHilbert (2 * m + 1)‖ ^ 2 / (4 * m + 4 : ℕ)) +
        36 * (‖canonicalMobiusHilbert m‖ ^ 2 / (4 * m + 4 : ℕ))) := by ring
    _ ≤ _ := by nlinarith

end RiemannResearch.RH.Pareto.CoefficientStabilization
