/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdSampling
import RiemannResearch.NumberTheory.DivisorEscapeTail
import RiemannResearch.NumberTheory.GcdSampleTail
import RiemannResearch.Analysis.WeightedComplexPairing
import RiemannResearch.RH.QMellinWitness
import RiemannResearch.Analysis.MellinDifferenceBounds
import RiemannResearch.RH.QCRTZeroObstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual gcd-sampled Mellin witness and complete residual energy

Source: the user-provided CRT collocation handoff, Section 7, continued from
QCRTZeroObstruction. The Mellin zero-annihilator strategy is supported by
Bagchi (2006), Proc. Indian Acad. Sci. Math. Sci. 116, 137--146, Theorems 2/5.
The sampler estimate is derived for the actual existing physical witness.
The separated energy bound retains both the raw escape tail and the actual
gcd-sample tail, improving the universal proper-divisor factor.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QCRTProjectedMellin
open ZetaTwoHilbert ZetaTwoProbability QMellinTransfer QMellinWitness
open QCRTFiniteCollocation QCRTZeroObstruction
open RiemannResearch.Analysis.Cesaro

/-- The actual signed first-difference witness, divided by the physical Q weight.
No division by s is used, so its pairing represents s times the Mellin map. -/
def rawWitness (s : ℂ) (n : ℕ) : ℂ :=
  ((zetaTwo * (n : ℝ)^2 : ℝ) : ℂ) * mellinFirst s n

theorem weight_rawWitness (s : ℂ) (n : ℕ) (hn : 0 < n) :
    (positiveQWeight n : ℂ) * rawWitness s n = mellinFirst s n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hz : (zetaTwo : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt zetaTwo_pos
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp only [rawWitness, positiveQWeight, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  field_simp

theorem rawWitness_norm_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 0 < n) :
    ‖rawWitness s n‖ ≤ zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) := by
  have hZ := zetaTwo_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ)^2 * (n : ℝ)^(-s.re-1) = (n : ℝ)^(1-s.re) := by
    rw [← Real.rpow_two, ← Real.rpow_add hnR]
    congr 1
    ring
  rw [rawWitness, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc
    _ ≤ (zetaTwo * (n : ℝ)^2) * (‖s‖ * (n : ℝ)^(-s.re-1)) :=
      mul_le_mul_of_nonneg_left (mellinFirst_norm_le s hs n hn) (by positivity)
    _ = _ := by rw [show zetaTwo * (n : ℝ)^2 * (‖s‖ * (n : ℝ)^(-s.re-1)) =
        zetaTwo * ‖s‖ * ((n : ℝ)^2 * (n : ℝ)^(-s.re-1)) by ring, hp]

/-- The full complex sampler defect, prior to any arithmetic tail estimate. -/
def defectTerm (s : ℂ) (L n : ℕ) : ℝ :=
  positiveQWeight n * ‖rawWitness s n - rawWitness s (Nat.gcd n L)‖^2

theorem defectTerm_nonneg (s : ℂ) (L n : ℕ) : 0 ≤ defectTerm s L n :=
  mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)

theorem defectTerm_eq_zero_of_dvd (s : ℂ) (L n : ℕ) (hnL : n ∣ L) :
    defectTerm s L n = 0 := by
  simp [defectTerm, Nat.gcd_eq_left hnL]

theorem defectTerm_le (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (L n : ℕ) (hn : 0 < n) :
    defectTerm s L n ≤ 4 * zetaTwo * ‖s‖^2 * (n : ℝ)^(-2*s.re) := by
  have hZ := zetaTwo_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : 0 < Nat.gcd n L := Nat.gcd_pos_of_pos_left L hn
  have hgR : (Nat.gcd n L : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hn (Nat.gcd_dvd_left n L)
  have hgp : (Nat.gcd n L : ℝ)^(1-s.re) ≤ (n : ℝ)^(1-s.re) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hgR (sub_nonneg.mpr hs1)
  have hb : ‖rawWitness s n - rawWitness s (Nat.gcd n L)‖ ≤
      2 * zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) := by
    calc
      _ ≤ ‖rawWitness s n‖ + ‖rawWitness s (Nat.gcd n L)‖ := norm_sub_le _ _
      _ ≤ zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) +
          zetaTwo * ‖s‖ * (Nat.gcd n L : ℝ)^(1-s.re) :=
        add_le_add (rawWitness_norm_le s hs n hn) (rawWitness_norm_le s hs _ hg)
      _ ≤ zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) +
          zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hgp (by positivity))
      _ = _ := by ring
  have hp : ((n : ℝ)^(1-s.re))^2 = (n : ℝ)^2 * (n : ℝ)^(-2*s.re) := by
    rw [pow_two, ← Real.rpow_add hnR, ← Real.rpow_two, ← Real.rpow_add hnR]
    congr 1
    ring
  unfold defectTerm
  calc
    _ ≤ positiveQWeight n * (2 * zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2)
        (positiveQWeight_nonneg n)
    _ = _ := by
      rw [mul_pow, hp]
      unfold positiveQWeight
      field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hnR]
      ring

open RiemannResearch.NumberTheory.DivisorEscapeTail
open RiemannResearch.Analysis.WeightedPairing QGcdSampling

theorem defectTerm_le_escape (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (L n : ℕ) (hn : 0 < n) :
    defectTerm s L n ≤ (4 * zetaTwo * ‖s‖^2) * term (2*s.re) L n := by
  by_cases hdiv : n ∣ L
  · rw [defectTerm_eq_zero_of_dvd s L n hdiv]
    simp [term, hdiv]
  · simpa only [term, if_neg hdiv, neg_mul] using defectTerm_le s hs hs1 L n hn

theorem defectTerm_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) :
    Summable (fun n : ℕ => defectTerm s L (n+1)) := by
  have hZ := zetaTwo_pos
  apply Summable.of_nonneg_of_le (fun n => defectTerm_nonneg s L (n+1))
    (fun n => defectTerm_le_escape s (by linarith) hs1 L (n+1) (Nat.succ_pos n))
  exact (summable_shifted_term (2*s.re) (by linarith) L).mul_left _

/-- The exact dual residual energy after gcd sampling. -/
def defectEnergy (s : ℂ) (L : ℕ) : ℝ := ∑' n : ℕ, defectTerm s L (n+1)

theorem defectEnergy_nonneg (s : ℂ) (L : ℕ) : 0 ≤ defectEnergy s L :=
  tsum_nonneg (fun n => defectTerm_nonneg s L (n+1))

theorem defectEnergy_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) :
    defectEnergy s L ≤ (4 * zetaTwo * ‖s‖^2) * tail (2*s.re) L := by
  calc
    _ ≤ ∑' n : ℕ, (4 * zetaTwo * ‖s‖^2) * term (2*s.re) L (n+1) :=
      Summable.tsum_le_tsum
        (fun n => defectTerm_le_escape s (by linarith) hs1 L (n+1) (Nat.succ_pos n))
        (defectTerm_summable s hs hs1 L)
        ((summable_shifted_term (2*s.re) (by linarith) L).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_shifted_term (2*s.re) (by linarith) L]

def dualResidual (s : ℂ) (L n : ℕ) : ℂ :=
  mellinFirst s (n+1) - (qWeight n : ℂ) * rawWitness s (Nat.gcd (n+1) L)

theorem dualResidual_energy (s : ℂ) (L n : ℕ) :
    ‖dualResidual s L n‖^2 / qWeight n = defectTerm s L (n+1) := by
  have he : dualResidual s L n = (qWeight n : ℂ) *
      (rawWitness s (n+1) - rawWitness s (Nat.gcd (n+1) L)) := by
    unfold dualResidual
    rw [mul_sub]
    change _ = (positiveQWeight (n+1) : ℂ) * rawWitness s (n+1) - _
    rw [weight_rawWitness s (n+1) (Nat.succ_pos n)]
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (qWeight_pos n), mul_pow]
  change (qWeight n)^2 * _ / qWeight n = qWeight n * _
  field_simp

theorem dualResidual_pairing_hasSum (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (L : ℕ) (hL : 0 < L) (f : QHilbert) (hf : conditionalProjection L f = 0) :
    HasSum (fun n : ℕ => dualResidual s L n * (qSequence f (n+1) : ℂ))
      (s * qMellin f s) := by
  have h := (qMellin_hasSum f s hs).sub
    (complex_sample_pairing_hasSum L hL f hf (rawWitness s))
  simp only [sub_zero] at h
  simpa only [dualResidual, sub_mul] using h

/-- Complete signed-pairing bound before replacing the actual defect energy. -/
theorem mellin_sq_le_defectEnergy (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : conditionalProjection L f = 0) :
    ‖s * qMellin f s‖^2 ≤ defectEnergy s L * ‖f‖^2 := by
  have hb : Summable (fun n : ℕ => ‖dualResidual s L n‖^2 / qWeight n) := by
    simpa only [dualResidual_energy] using defectTerm_summable s hs hs1 L
  have hM : Summable (fun n : ℕ => qWeight n * ‖(qSequence f (n+1) : ℂ)‖^2) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, qWeight,
      qSequence_weighted_square] using qCoordinate_square_summable f
  have h := pairing_norm_sq_le qWeight qWeight_pos (dualResidual s L)
    (fun n => (qSequence f (n+1) : ℂ)) hb hM
  rw [(dualResidual_pairing_hasSum s hs L hL f hf).tsum_eq] at h
  simp_rw [dualResidual_energy] at h
  simpa only [defectEnergy, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, qWeight, qSequence_weighted_square, ← qNorm_sq] using h

/-- The explicit Euler/divisor tail controls the actual projected Mellin witness. -/
theorem mellin_sq_le_escapeTail (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : conditionalProjection L f = 0) :
    ‖qMellin f s‖^2 ≤ (4 * zetaTwo * tail (2*s.re) L) * ‖f‖^2 := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hp : 0 < ‖s‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs0)
  have h := (mellin_sq_le_defectEnergy s hs hs1 L hL f hf).trans
    (mul_le_mul_of_nonneg_right (defectEnergy_le s hs hs1 L) (sq_nonneg ‖f‖))
  rw [norm_mul, mul_pow] at h
  nlinarith

/-- The actual projected functional satisfies the explicit arithmetic estimate. -/
theorem tailMellin_norm_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L) :
    ‖tailMellin L s hs‖ ≤ 2 * Real.sqrt (zetaTwo * tail (2*s.re) L) := by
  have hZ := zetaTwo_pos
  have hD := tail_nonneg (2*s.re) L
  have hC : 0 ≤ 2 * Real.sqrt (zetaTwo * tail (2*s.re) L) := by positivity
  have hC2 : (2 * Real.sqrt (zetaTwo * tail (2*s.re) L))^2 =
      4 * zetaTwo * tail (2*s.re) L := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  apply (tailMellin L s hs).opNorm_le_bound hC
  intro f
  let g : QHilbert := f - conditionalProjection L f
  have hg : conditionalProjection L g = 0 := by
    change (cellSpace L).starProjection
      (f - (cellSpace L).starProjection f) = 0
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr
      ((cellSpace L).starProjection_apply_mem f), sub_self]
  have hgn : ‖g‖ ≤ ‖f‖ := by
    have he : g = (cellSpace L)ᗮ.starProjection f := by
      rw [Submodule.starProjection_orthogonal]
      rfl
    rw [he]
    exact ((cellSpace L)ᗮ.starProjection.le_opNorm f).trans
      (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le ((cellSpace L)ᗮ)) (norm_nonneg f))
  have h := (mellin_sq_le_escapeTail s hs hs1 L hL g hg).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hgn 2)
      (show 0 ≤ 4 * zetaTwo * tail (2*s.re) L by positivity))
  change ‖qMellin g s‖ ≤ (2 * Real.sqrt (zetaTwo * tail (2*s.re) L)) * ‖f‖
  have he : ((2 * Real.sqrt (zetaTwo * tail (2*s.re) L)) * ‖f‖)^2 =
      (4 * zetaTwo * tail (2*s.re) L) * ‖f‖^2 := by rw [mul_pow, hC2]
  have hp := mul_nonneg hC (norm_nonneg f)
  nlinarith [norm_nonneg (qMellin g s)]


/-- The improved arithmetic sampler factor. -/
def escapeFactor (s : ℂ) : ℝ := 1 + (2 : ℝ)^(s.re-1)

theorem escapeFactor_pos (s : ℂ) : 0 < escapeFactor s := by
  unfold escapeFactor
  positivity

theorem escapeFactor_lt_two (s : ℂ) (hs1 : s.re < 1) : escapeFactor s < 2 := by
  have hp : (2 : ℝ)^(s.re-1) < (2 : ℝ)^(0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  rw [Real.rpow_zero] at hp
  unfold escapeFactor
  linarith

/-- Sharpened pointwise estimate only on the actual escape set. -/
theorem defectTerm_le_sharp_of_not_dvd (s : ℂ) (hs : 0 < s.re)
    (hs1 : s.re ≤ 1) (L n : ℕ) (hn : 0 < n) (hnL : ¬ n ∣ L) :
    defectTerm s L n ≤ (escapeFactor s)^2 * zetaTwo * ‖s‖^2 *
      (n : ℝ)^(-2*s.re) := by
  have hZ := zetaTwo_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : 0 < Nat.gcd n L := Nat.gcd_pos_of_pos_left L hn
  have hgp := gcd_rpow_le_half L n hn hnL (1-s.re) (sub_nonneg.mpr hs1)
  rw [show -(1-s.re) = s.re-1 by ring] at hgp
  have hb : ‖rawWitness s n - rawWitness s (Nat.gcd n L)‖ ≤
      escapeFactor s * zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) := by
    calc
      _ ≤ ‖rawWitness s n‖ + ‖rawWitness s (Nat.gcd n L)‖ := norm_sub_le _ _
      _ ≤ zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) +
          zetaTwo * ‖s‖ * (Nat.gcd n L : ℝ)^(1-s.re) :=
        add_le_add (rawWitness_norm_le s hs n hn) (rawWitness_norm_le s hs _ hg)
      _ ≤ zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re) +
          zetaTwo * ‖s‖ * ((2 : ℝ)^(s.re-1) * (n : ℝ)^(1-s.re)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hgp (by positivity))
      _ = _ := by unfold escapeFactor; ring
  have hp : ((n : ℝ)^(1-s.re))^2 = (n : ℝ)^2 * (n : ℝ)^(-2*s.re) := by
    rw [pow_two, ← Real.rpow_add hnR, ← Real.rpow_two, ← Real.rpow_add hnR]
    congr 1
    ring
  unfold defectTerm
  calc
    _ ≤ positiveQWeight n *
        (escapeFactor s * zetaTwo * ‖s‖ * (n : ℝ)^(1-s.re))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2)
        (positiveQWeight_nonneg n)
    _ = _ := by
      rw [mul_pow, hp]
      unfold positiveQWeight
      field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hnR]

/-- The exact zero on divisors is retained before taking the complete sum. -/
theorem defectTerm_le_sharp_escape (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (L n : ℕ) (hn : 0 < n) :
    defectTerm s L n ≤ ((escapeFactor s)^2 * zetaTwo * ‖s‖^2) *
      term (2*s.re) L n := by
  by_cases hnL : n ∣ L
  · rw [defectTerm_eq_zero_of_dvd s L n hnL]
    simp [term, hnL]
  · simpa only [term, if_neg hnL, neg_mul] using
      defectTerm_le_sharp_of_not_dvd s hs hs1 L n hn hnL

/-- The improved complete divisor-tail estimate for the actual defect energy. -/
theorem defectEnergy_le_sharp (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) :
    defectEnergy s L ≤ ((escapeFactor s)^2 * zetaTwo * ‖s‖^2) *
      tail (2*s.re) L := by
  calc
    _ ≤ ∑' n : ℕ, ((escapeFactor s)^2 * zetaTwo * ‖s‖^2) *
        term (2*s.re) L (n+1) :=
      Summable.tsum_le_tsum
        (fun n => defectTerm_le_sharp_escape s (by linarith) hs1 L (n+1)
          (Nat.succ_pos n))
        (defectTerm_summable s hs hs1 L)
        ((summable_shifted_term (2*s.re) (by linarith) L).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_shifted_term (2*s.re) (by linarith) L]

/-- The sharper coefficient applies to every vector orthogonal to the gcd cells. -/
theorem mellin_sq_le_sharp_escapeTail (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : conditionalProjection L f = 0) :
    ‖qMellin f s‖^2 ≤ ((escapeFactor s)^2 * zetaTwo * tail (2*s.re) L) * ‖f‖^2 := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hp : 0 < ‖s‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs0)
  have h := (mellin_sq_le_defectEnergy s hs hs1 L hL f hf).trans
    (mul_le_mul_of_nonneg_right (defectEnergy_le_sharp s hs hs1 L) (sq_nonneg ‖f‖))
  rw [norm_mul, mul_pow] at h
  apply (mul_le_mul_iff_right₀ hp).mp
  convert h using 1 <;> ring

/-- Strictly smaller sampler coefficient in the open strip. -/
theorem tailMellin_norm_le_sharp (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L) :
    ‖tailMellin L s hs‖ ≤ escapeFactor s *
      Real.sqrt (zetaTwo * tail (2*s.re) L) := by
  have hZ := zetaTwo_pos
  have hD := tail_nonneg (2*s.re) L
  have hA := escapeFactor_pos s
  have hC : 0 ≤ escapeFactor s * Real.sqrt (zetaTwo * tail (2*s.re) L) := by
    positivity
  have hC2 : (escapeFactor s * Real.sqrt (zetaTwo * tail (2*s.re) L))^2 =
      (escapeFactor s)^2 * zetaTwo * tail (2*s.re) L := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  apply (tailMellin L s hs).opNorm_le_bound hC
  intro f
  let g : QHilbert := f - conditionalProjection L f
  have hg : conditionalProjection L g = 0 := by
    change (cellSpace L).starProjection
      (f - (cellSpace L).starProjection f) = 0
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr
      ((cellSpace L).starProjection_apply_mem f), sub_self]
  have hgn : ‖g‖ ≤ ‖f‖ := by
    have he : g = ((cellSpace L)ᗮ).starProjection f := by
      rw [Submodule.starProjection_orthogonal]
      rfl
    rw [he]
    exact (((cellSpace L)ᗮ).starProjection.le_opNorm f).trans
      (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le ((cellSpace L)ᗮ)) (norm_nonneg f))
  have h := (mellin_sq_le_sharp_escapeTail s hs hs1 L hL g hg).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hgn 2)
      (show 0 ≤ (escapeFactor s)^2 * zetaTwo * tail (2*s.re) L by positivity))
  change ‖qMellin g s‖ ≤
    (escapeFactor s * Real.sqrt (zetaTwo * tail (2*s.re) L)) * ‖f‖
  have he : ((escapeFactor s * Real.sqrt (zetaTwo * tail (2*s.re) L)) * ‖f‖)^2 =
      ((escapeFactor s)^2 * zetaTwo * tail (2*s.re) L) * ‖f‖^2 := by
    rw [mul_pow, hC2]
  have hp := mul_nonneg hC (norm_nonneg f)
  nlinarith [norm_nonneg (qMellin g s)]


private theorem young_sum_sq (a b δ : ℝ) (hδ : 0 < δ) :
    (a + b) ^ 2 ≤ (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 := by
  have he : (1 + δ) * a ^ 2 + (1 + 1 / δ) * b ^ 2 =
      (a + b) ^ 2 + (δ * a - b) ^ 2 / δ := by field_simp [ne_of_gt hδ] <;> ring
  rw [he]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hδ.le)

/-- A tunable estimate preserving the separate raw and gcd-sampled energies. -/
theorem defectTerm_le_young_escape (s : ℂ) (hs : 0 < s.re)
    (L n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    defectTerm s L n ≤ zetaTwo * ‖s‖ ^ 2 *
      ((1 + δ) * term (2 * s.re) L n + (1 + 1 / δ) * sampleTerm (2 * s.re) L n) := by
  by_cases hnL : n ∣ L
  · rw [defectTerm_eq_zero_of_dvd s L n hnL]
    simp [term, sampleTerm, hnL]
  · have hZ := zetaTwo_pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hg : 0 < Nat.gcd n L := Nat.gcd_pos_of_pos_left L hn
    have hgR : (0 : ℝ) < Nat.gcd n L := by exact_mod_cast hg
    have hnPow : ((n : ℝ) ^ (1 - s.re)) ^ 2 =
        (n : ℝ) ^ 2 * (n : ℝ) ^ (-2 * s.re) := by
      rw [pow_two, ← Real.rpow_add hnR, ← Real.rpow_two, ← Real.rpow_add hnR]
      congr 1
      ring
    have hgPow : ((Nat.gcd n L : ℝ) ^ (1 - s.re)) ^ 2 =
        (Nat.gcd n L : ℝ) ^ (2 - 2 * s.re) := by
      rw [pow_two, ← Real.rpow_add hgR]
      congr 1
      ring
    have hb : ‖rawWitness s n - rawWitness s (Nat.gcd n L)‖ ≤
        zetaTwo * ‖s‖ * ((n : ℝ) ^ (1 - s.re) + (Nat.gcd n L : ℝ) ^ (1 - s.re)) := by
      calc
        _ ≤ ‖rawWitness s n‖ + ‖rawWitness s (Nat.gcd n L)‖ := norm_sub_le _ _
        _ ≤ zetaTwo * ‖s‖ * (n : ℝ) ^ (1 - s.re) +
            zetaTwo * ‖s‖ * (Nat.gcd n L : ℝ) ^ (1 - s.re) :=
          add_le_add (rawWitness_norm_le s hs n hn) (rawWitness_norm_le s hs _ hg)
        _ = _ := by ring
    unfold defectTerm
    calc
      _ ≤ positiveQWeight n *
          (zetaTwo * ‖s‖ * ((n : ℝ) ^ (1 - s.re) + (Nat.gcd n L : ℝ) ^ (1 - s.re))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2)
          (positiveQWeight_nonneg n)
      _ = positiveQWeight n * (zetaTwo * ‖s‖) ^ 2 *
          ((n : ℝ) ^ (1 - s.re) + (Nat.gcd n L : ℝ) ^ (1 - s.re)) ^ 2 := by ring
      _ ≤ positiveQWeight n * (zetaTwo * ‖s‖) ^ 2 *
          ((1 + δ) * ((n : ℝ) ^ (1 - s.re)) ^ 2 +
            (1 + 1 / δ) * ((Nat.gcd n L : ℝ) ^ (1 - s.re)) ^ 2) :=
        mul_le_mul_of_nonneg_left (young_sum_sq _ _ δ hδ)
          (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
      _ = _ := by
        simp only [term, sampleTerm, if_neg hnL]
        rw [hnPow, hgPow]
        unfold positiveQWeight
        field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hnR, ne_of_gt hδ] <;> ring

/-- The complete two-energy inequality before selecting the Young parameter. -/
theorem defectEnergy_le_young_tails (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    defectEnergy s L ≤ zetaTwo * ‖s‖ ^ 2 *
      ((1 + δ) * tail (2 * s.re) L + (1 + 1 / δ) * sampleTail (2 * s.re) L) := by
  have hD := summable_shifted_term (2 * s.re) (by linarith) L
  have hS := sampleTerm_summable (2 * s.re) (by linarith) (by linarith) L
  have hr := ((hD.mul_left (1 + δ)).add (hS.mul_left (1 + 1 / δ))).mul_left
    (zetaTwo * ‖s‖ ^ 2)
  calc
    _ ≤ ∑' n : ℕ, zetaTwo * ‖s‖ ^ 2 *
        ((1 + δ) * term (2 * s.re) L (n + 1) + (1 + 1 / δ) * sampleTerm (2 * s.re) L (n + 1)) :=
      Summable.tsum_le_tsum
        (fun n => defectTerm_le_young_escape s (by linarith) L (n + 1)
          (Nat.succ_pos n) δ hδ)
        (defectTerm_summable s hs hs1 L) hr
    _ = _ := by
      rw [tsum_mul_left, (hD.mul_left (1 + δ)).tsum_add (hS.mul_left (1 + 1 / δ)),
        tsum_mul_left, tsum_mul_left, tsum_shifted_term (2 * s.re) (by linarith) L] <;> rfl

/-- Optimizing the exact Young parameter retains the smaller actual gcd-sample tail. -/
theorem defectEnergy_le_separated_tails (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L) :
    defectEnergy s L ≤ zetaTwo * ‖s‖ ^ 2 *
      (Real.sqrt (tail (2 * s.re) L) + Real.sqrt (sampleTail (2 * s.re) L)) ^ 2 := by
  let D := tail (2 * s.re) L
  let S := sampleTail (2 * s.re) L
  have hD : 0 < D := tail_pos (2 * s.re) (by linarith) (by linarith) L hL
  have hS : 0 < S := sampleTail_pos (2 * s.re) (by linarith) (by linarith) L hL
  have hd : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hs' : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hδ : 0 < Real.sqrt S / Real.sqrt D := div_pos hs' hd
  have he : (1 + Real.sqrt S / Real.sqrt D) * D +
      (1 + 1 / (Real.sqrt S / Real.sqrt D)) * S = (Real.sqrt D + Real.sqrt S) ^ 2 := by
    calc
      _ = (1 + Real.sqrt S / Real.sqrt D) * (Real.sqrt D) ^ 2 +
          (1 + 1 / (Real.sqrt S / Real.sqrt D)) * (Real.sqrt S) ^ 2 := by
        rw [Real.sq_sqrt hD.le, Real.sq_sqrt hS.le]
      _ = _ := by field_simp [ne_of_gt hd, ne_of_gt hs'] <;> ring
  calc
    _ ≤ zetaTwo * ‖s‖ ^ 2 *
        ((1 + Real.sqrt S / Real.sqrt D) * D + (1 + 1 / (Real.sqrt S / Real.sqrt D)) * S) :=
      defectEnergy_le_young_tails s hs hs1 L _ hδ
    _ = _ := by rw [he]

/-- Complete Mellin bound with both actual arithmetic tails retained. -/
theorem mellin_sq_le_separated_tails (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L)
    (f : QHilbert) (hf : conditionalProjection L f = 0) :
    ‖qMellin f s‖ ^ 2 ≤ zetaTwo *
      (Real.sqrt (tail (2 * s.re) L) + Real.sqrt (sampleTail (2 * s.re) L)) ^ 2 * ‖f‖ ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hp : 0 < ‖s‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs0)
  have h := (mellin_sq_le_defectEnergy s hs hs1 L hL f hf).trans
    (mul_le_mul_of_nonneg_right (defectEnergy_le_separated_tails s hs hs1 L hL)
      (sq_nonneg ‖f‖))
  rw [norm_mul, mul_pow] at h
  apply (mul_le_mul_iff_right₀ hp).mp
  convert h using 1 <;> ring

/-- The actual operator bound separates raw escape from the smaller gcd-sample energy. -/
theorem tailMellin_norm_le_separated (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s.re ≤ 1) (L : ℕ) (hL : 0 < L) :
    ‖tailMellin L s hs‖ ≤ Real.sqrt zetaTwo *
      (Real.sqrt (tail (2 * s.re) L) + Real.sqrt (sampleTail (2 * s.re) L)) := by
  have hZ := zetaTwo_pos
  let B := Real.sqrt (tail (2 * s.re) L) + Real.sqrt (sampleTail (2 * s.re) L)
  have hB : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hC : 0 ≤ Real.sqrt zetaTwo * B := mul_nonneg (Real.sqrt_nonneg _) hB
  have hC2 : (Real.sqrt zetaTwo * B) ^ 2 = zetaTwo * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hZ.le]
  apply (tailMellin L s hs).opNorm_le_bound hC
  intro f
  let g : QHilbert := f - conditionalProjection L f
  have hg : conditionalProjection L g = 0 := by
    change (cellSpace L).starProjection (f - (cellSpace L).starProjection f) = 0
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr
      ((cellSpace L).starProjection_apply_mem f), sub_self]
  have hgn : ‖g‖ ≤ ‖f‖ := by
    have he : g = ((cellSpace L)ᗮ).starProjection f := by
      rw [Submodule.starProjection_orthogonal]
      rfl
    rw [he]
    exact (((cellSpace L)ᗮ).starProjection.le_opNorm f).trans
      (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le ((cellSpace L)ᗮ)) (norm_nonneg f))
  have h := (mellin_sq_le_separated_tails s hs hs1 L hL g hg).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hgn 2)
      (mul_nonneg hZ.le (sq_nonneg B)))
  change ‖qMellin g s‖ ≤ (Real.sqrt zetaTwo * B) * ‖f‖
  change ‖qMellin g s‖ ^ 2 ≤ zetaTwo * B ^ 2 * ‖f‖ ^ 2 at h
  have he : ((Real.sqrt zetaTwo * B) * ‖f‖) ^ 2 = zetaTwo * B ^ 2 * ‖f‖ ^ 2 := by
    rw [mul_pow, hC2]
  have hp := mul_nonneg hC (norm_nonneg f)
  nlinarith [norm_nonneg (qMellin g s)]


/-- For each fixed half-strip parameter the actual Mellin functional on the
orthogonal CRT remainder tends to zero in operator norm, unconditionally. -/
theorem tailMellin_lcmUpto_norm_tendsto_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s.re ≤ 1) :
    Tendsto (fun M : ℕ => ‖tailMellin (Nat.lcmUpto M) s hs‖) atTop (𝓝 0) := by
  have ht := (tail_lcmUpto_tendsto_zero (2 * s.re) (by linarith)).const_mul zetaTwo
  have hsqrt := (Real.continuous_sqrt.tendsto (zetaTwo * 0)).comp ht
  have hb : Tendsto (fun M : ℕ => escapeFactor s *
      Real.sqrt (zetaTwo * tail (2 * s.re) (Nat.lcmUpto M))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      hsqrt.const_mul (escapeFactor s)
  apply squeeze_zero (fun M => norm_nonneg _) ?_ hb
  intro M
  exact tailMellin_norm_le_sharp s hs hs1 (Nat.lcmUpto M) (Nat.lcmUpto_pos M)

end RiemannResearch.RH.QCRTProjectedMellin
