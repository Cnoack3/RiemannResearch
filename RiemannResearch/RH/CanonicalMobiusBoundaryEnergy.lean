/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.HardyMobiusFamily
import RiemannResearch.RH.ParetoBoundedMellinLinearity
import RiemannResearch.RH.ParetoResidualBoundaryEnergy
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.Analysis.MellinNormalizedResidue
import Mathlib.Tactic.Ring

/-!
# Exact critical-line energy of the corrected Möbius family
Source: the user's signed Mellin--Plancherel argument, 30 October 2026.
Finite boundedness extends the actual Mellin identity to Re(s)>0, including
the critical line. The complete correction is retained inside the square.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MeasureTheory Set
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

theorem canonicalMobiusHilbert_mellin_positive (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (canonicalMobiusHilbert N) s = correctedHardyMobiusSum N s := by
  let g : ℕ → ℝ → ℂ := fun d x =>
    (residueFraction d ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)
  have hi (d : ℕ) (hd : 0 < d) : IntegrableOn (g d) (Ioi 1) := by
    have hb : ∀ k, |hilbertSequence (normalizedResidueHilbert d hd) k| ≤ 1 := by
      intro k
      rw [normalizedResidueHilbert_sequence]
      exact residueFraction_abs_le_one d k hd
    simpa only [g, normalizedResidueHilbert_sequence] using
      paretoMellin_step_integrable_of_bounded _ hb s hs
  have hI (d : ℕ) (hd : 0 < d) :
      (∫ x in Ioi (1 : ℝ), g d x) = -hardyMobiusGenerator d s := by
    rw [← normalizedResidue_mellin_eq_neg_hardyMobiusGenerator d hd s hs,
      paretoMellin_eq_step_integral]
    simp only [g, normalizedResidueHilbert_sequence]
  let a : ℂ := ((N + 1 : ℕ) : ℂ) * (mobiusReciprocalSum N : ℂ)
  have hraw : IntegrableOn (fun x => ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℂ) * g d x) (Ioi 1) :=
    integrable_finsetSum _ (fun d hd => (hi d (Finset.mem_Icc.mp hd).1).const_mul _)
  have hanchor := (hi (N + 1) (Nat.succ_pos N)).const_mul a
  have he : (fun x : ℝ =>
      (hilbertSequence (canonicalMobiusHilbert N) ⌊x⌋₊ : ℂ) *
        (x : ℂ) ^ (-s - 1)) =
      fun x : ℝ => -(∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℂ) * g d x) + a * g (N + 1) x := by
    funext x
    rw [canonicalMobiusHilbert_sequence]
    simp only [canonicalMobiusHead, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.ofReal_natCast, g, a, add_mul, neg_mul, Finset.sum_mul, mul_assoc]
  have hrawneg : IntegrableOn (fun x : ℝ => -(∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℂ) * g d x)) (Ioi 1) := hraw.neg
  rw [paretoMellin_eq_step_integral, he, integral_add hrawneg hanchor,
    integral_neg, integral_finsetSum _ (fun d hd =>
      (hi d (Finset.mem_Icc.mp hd).1).const_mul _), integral_const_mul,
    hI (N + 1) (Nat.succ_pos N)]
  have hsum : (∑ d ∈ Finset.Icc 1 N,
      ∫ x in Ioi (1 : ℝ), (ArithmeticFunction.moebius d : ℂ) * g d x) =
      -rawHardyMobiusSum N s := by
    rw [rawHardyMobiusSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [integral_const_mul, hI d (Finset.mem_Icc.mp hd).1, mul_neg]
  rw [hsum, neg_neg]
  simp only [correctedHardyMobiusSum, a, mul_neg, sub_eq_add_neg]

theorem canonicalMobius_boundary_energy (N : ℕ) (hN : 0 < N) :
    ‖canonicalMobiusHilbert N‖ ^ 2 =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖correctedHardyMobiusSum N (MellinFrequency.criticalPoint t)‖ ^ 2 := by
  have hb : ∀ k, |hilbertSequence (canonicalMobiusHilbert N) k| ≤ 2 * (N : ℝ) := by
    intro k
    rw [canonicalMobiusHilbert_sequence]
    exact canonicalMobiusHead_abs_le_two_mul N hN k
  rw [← ParetoResidualBoundaryEnergy.paretoMellin_boundary_energy_of_bounded _ hb]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [canonicalMobiusHilbert_mellin_positive N _ (by simp [MellinFrequency.criticalPoint])]
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open MeasureTheory
noncomputable section
def mobiusDirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s)

def correctedMobiusSymbol (N : ℕ) (s : ℂ) : ℂ :=
  mobiusDirichletPolynomial N s -
    (((N + 1 : ℕ) : ℂ) * (mobiusReciprocalSum N : ℂ)) * ((N + 1 : ℕ) : ℂ) ^ (-s)

theorem correctedHardyMobiusSum_zeta (N : ℕ) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    correctedHardyMobiusSum N s = riemannZeta s / s * correctedMobiusSymbol N s := by
  have hrec : (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℂ) / (d : ℂ)) = (mobiusReciprocalSum N : ℂ) := by
    simp only [mobiusReciprocalSum, Complex.ofReal_sum, Complex.ofReal_div,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
  have hraw : rawHardyMobiusSum N s =
      (mobiusDirichletPolynomial N s - (mobiusReciprocalSum N : ℂ)) * (riemannZeta s / s) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-s) -
          (ArithmeticFunction.moebius d : ℂ) / (d : ℂ)) * (riemannZeta s / s) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [hardyMobiusGenerator_eq_zeta d (Finset.mem_Icc.mp hd).1 s hs hs1]
        ring
      _ = _ := by
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, hrec]
        rfl
  have hp : (((N + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [correctedHardyMobiusSum, hraw, hardyMobiusGenerator_eq_zeta (N + 1)
    (Nat.succ_pos N) s hs hs1]
  unfold correctedMobiusSymbol
  field_simp [hp, hs0]
  ring

/-- Exact complete energy: neither the mixed term nor the anchor is discarded. -/
theorem canonicalMobius_boundary_zeta_energy (N : ℕ) (hN : 0 < N) :
    ‖canonicalMobiusHilbert N‖ ^ 2 =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        (‖riemannZeta (MellinFrequency.criticalPoint t)‖ ^ 2 / (1 / 4 + t ^ 2)) *
          ‖correctedMobiusSymbol N (MellinFrequency.criticalPoint t)‖ ^ 2 := by
  rw [canonicalMobius_boundary_energy N hN]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hn : ‖MellinFrequency.criticalPoint t‖ ^ 2 = (1 / 4 : ℝ) + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [MellinFrequency.criticalPoint]
    ring
  rw [correctedHardyMobiusSum_zeta N _ (by simp [MellinFrequency.criticalPoint])
    (MellinFrequency.criticalPoint_ne_one t), norm_mul, norm_div, mul_pow, div_pow, hn]

theorem canonicalMobius_normalized_boundary_energy (N : ℕ) (hN : 0 < N) :
    ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ) =
      (1 / (2 * Real.pi * (N : ℝ))) * ∫ t : ℝ,
        (‖riemannZeta (MellinFrequency.criticalPoint t)‖ ^ 2 / (1 / 4 + t ^ 2)) *
          ‖correctedMobiusSymbol N (MellinFrequency.criticalPoint t)‖ ^ 2 := by
  rw [canonicalMobius_boundary_zeta_energy N hN]
  ring
end
end RiemannResearch.RH.Pareto
