/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalStageGain
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Signed correlation certificates for actual rational-stage displacement

Source: user-provided signed-tail continuation agenda, 20 October 2026,
Priority 1. The exact square completion is retained before taking a lower
bound. All correlations use the later rational metric and the actual
minimizers. No lower arithmetic estimate for these correlations is assumed
to have been established.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open ZetaTwoHilbert QSquarefreePrimorialCofinality ArithmeticCumulative
open Pareto.SquarefreeStageExhaustion

/-- Bilinear form for the full rational residue weights, including residue zero. -/
def rationalPair (L : ℕ) (f g : ℕ → ℝ) : ℝ :=
  ∑ a ∈ sites L, weight L a * f a * g a

theorem rationalPair_comm (L : ℕ) (f g : ℕ → ℝ) :
    rationalPair L f g = rationalPair L g f := by
  unfold rationalPair
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem rationalPair_sub_left (L : ℕ) (f g v : ℕ → ℝ) :
    rationalPair L (fun a => f a - g a) v =
      rationalPair L f v - rationalPair L g v := by
  simp only [rationalPair, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem rationalPair_sub_right (L : ℕ) (f g v : ℕ → ℝ) :
    rationalPair L f (fun a => g a - v a) =
      rationalPair L f g - rationalPair L f v := by
  simp only [rationalPair, mul_sub, Finset.sum_sub_distrib]

theorem rationalPair_self_nonneg (L : ℕ) (f : ℕ → ℝ) :
    0 ≤ rationalPair L f f := by
  apply Finset.sum_nonneg
  intro a ha
  simpa only [mul_assoc, ← sq] using mul_nonneg (weight_nonneg L a) (sq_nonneg (f a))

/-- Exact signed square completion for any direction of positive energy. -/
theorem rationalPair_completion (L : ℕ) (f g : ℕ → ℝ)
    (hg : 0 < rationalPair L g g) :
    rationalPair L f f = rationalPair L f g ^ 2 / rationalPair L g g +
      rationalPair L
        (fun a => f a - (rationalPair L f g / rationalPair L g g) * g a)
        (fun a => f a - (rationalPair L f g / rationalPair L g g) * g a) := by
  have hex (t : ℝ) :
      rationalPair L (fun a => f a - t * g a) (fun a => f a - t * g a) =
        rationalPair L f f - 2 * t * rationalPair L f g + t^2 * rationalPair L g g := by
    unfold rationalPair
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [hex]
  field_simp [ne_of_gt hg]
  ring

theorem rationalPair_cauchy_div (L : ℕ) (f g : ℕ → ℝ)
    (hg : 0 < rationalPair L g g) :
    rationalPair L f g ^ 2 / rationalPair L g g ≤ rationalPair L f f := by
  rw [rationalPair_completion L f g hg]
  exact le_add_of_nonneg_right (rationalPair_self_nonneg _ _)

/-- The actual normal equations extend to every divisor synthesis. -/
theorem rationalMinimizer_normal_fit (L : ℕ) (b : ℕ → ℝ) :
    rationalPair L (fun a => 1 - divisorFit L (rationalCoefficients L) a)
      (divisorFit L b) = 0 := by
  unfold rationalPair divisorFit
  simp_rw [Finset.mul_sum]
  have he : (∑ a ∈ sites L, ∑ d ∈ L.divisors,
      weight L a * (1 - ∑ i ∈ L.divisors, rationalCoefficients L i * residueFraction i a) *
        (b d * residueFraction d a)) =
      ∑ d ∈ L.divisors, b d * (∑ a ∈ sites L,
        weight L a * (1 - divisorFit L (rationalCoefficients L) a) * residueFraction d a) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    unfold divisorFit
    ring
  rw [he]
  apply Finset.sum_eq_zero
  intro d hd
  rw [rationalCoefficients_normal L d hd, mul_zero]

theorem rationalMinimizer_normal_mem {m : ℕ} {v : QHilbert}
    (hv : v ∈ primorialStage m) :
    rationalPair (primorialPeriod m)
      (fun a => 1 - qSequence (rationalMinimizer (primorialPeriod m)) a)
      (qSequence v) = 0 := by
  obtain ⟨b, rfl⟩ := exists_qDivisorFit_of_mem hv
  simpa only [rationalMinimizer, qSequence_qDivisorFit] using
    rationalMinimizer_normal_fit (primorialPeriod m) b

/-- Signed correlation of the old residual with a later legal vector. -/
def rationalStageCorrelation (n m : ℕ) (v : QHilbert) : ℝ :=
  rationalPair (primorialPeriod m)
    (fun a => 1 - qSequence (rationalMinimizer (primorialPeriod n)) a) (qSequence v)

theorem rationalStageCorrelation_eq_displacement {n m : ℕ} {v : QHilbert}
    (hv : v ∈ primorialStage m) :
    rationalStageCorrelation n m v = rationalPair (primorialPeriod m)
      (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
        qSequence (rationalMinimizer (primorialPeriod n)) a) (qSequence v) := by
  have h := rationalMinimizer_normal_mem hv
  rw [rationalPair_sub_left] at h
  unfold rationalStageCorrelation
  rw [rationalPair_sub_left, rationalPair_sub_left]
  linarith

theorem rationalStageDisplacement_eq_pair (n m : ℕ) :
    rationalStageDisplacement n m = rationalPair (primorialPeriod m)
      (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
        qSequence (rationalMinimizer (primorialPeriod n)) a)
      (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
        qSequence (rationalMinimizer (primorialPeriod n)) a) := by
  unfold rationalStageDisplacement rationalPair
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Actual displacement equals the signed one-direction certificate plus
the full nonnegative remaining square. -/
theorem rationalStageDisplacement_completion {n m : ℕ} {v : QHilbert}
    (hv : v ∈ primorialStage m)
    (hpos : 0 < rationalPair (primorialPeriod m) (qSequence v) (qSequence v)) :
    rationalStageDisplacement n m =
      rationalStageCorrelation n m v ^ 2 /
        rationalPair (primorialPeriod m) (qSequence v) (qSequence v) +
      rationalPair (primorialPeriod m)
        (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
          qSequence (rationalMinimizer (primorialPeriod n)) a -
          (rationalStageCorrelation n m v /
            rationalPair (primorialPeriod m) (qSequence v) (qSequence v)) * qSequence v a)
        (fun a => qSequence (rationalMinimizer (primorialPeriod m)) a -
          qSequence (rationalMinimizer (primorialPeriod n)) a -
          (rationalStageCorrelation n m v /
            rationalPair (primorialPeriod m) (qSequence v) (qSequence v)) * qSequence v a) := by
  rw [rationalStageDisplacement_eq_pair, rationalStageCorrelation_eq_displacement hv]
  exact rationalPair_completion _ _ _ hpos

theorem rationalStageDisplacement_ge_correlation {n m : ℕ} {v : QHilbert}
    (hv : v ∈ primorialStage m)
    (hpos : 0 < rationalPair (primorialPeriod m) (qSequence v) (qSequence v)) :
    rationalStageCorrelation n m v ^ 2 /
      rationalPair (primorialPeriod m) (qSequence v) (qSequence v) ≤
        rationalStageDisplacement n m := by
  rw [rationalStageDisplacement_eq_pair, rationalStageCorrelation_eq_displacement hv]
  exact rationalPair_cauchy_div _ _ _ hpos

/-- The quartic refund and actual signed certificate contribute to the same drop. -/
theorem rationalMinimum_drop_ge_refund_correlation {n m k : ℕ}
    (hnm : n ≤ m) (hperiod : primorialPeriod m = primorialPeriod n * k)
    (hk : 2 ≤ k) {v : QHilbert} (hv : v ∈ primorialStage m)
    (hpos : 0 < rationalPair (primorialPeriod m) (qSequence v) (qSequence v)) :
    (1 - 20 / (3 * (k : ℝ))) * rationalGap (primorialPeriod n)
        (qSequence (rationalMinimizer (primorialPeriod n))) +
      rationalStageCorrelation n m v ^ 2 /
        rationalPair (primorialPeriod m) (qSequence v) (qSequence v) ≤
      rationalMinimum (primorialPeriod n) - rationalMinimum (primorialPeriod m) := by
  have hc := rationalStageDisplacement_ge_correlation hv hpos (n := n)
  have hd := rationalMinimum_drop_ge_quartic_refund hnm hperiod hk
  linarith

/-- Every nonzero residue atom has positive later rational energy. The site 1
already certifies this, including composite squarefree conductors. -/
theorem rationalPair_residue_pos {L d : ℕ} (hL : 0 < L) (hd : 2 ≤ d) :
    0 < rationalPair L (residueFraction d) (residueFraction d) := by
  have hweight : 0 < weight L 1 := by
    unfold weight
    positivity
  have hres : 0 < residueFraction d 1 := by
    unfold residueFraction
    rw [Nat.mod_eq_of_lt (by omega : 1 < d)]
    positivity
  apply Finset.sum_pos'
  · intro a ha
    simpa only [mul_assoc, ← sq] using
      mul_nonneg (weight_nonneg L a) (sq_nonneg (residueFraction d a))
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩,
      mul_pos (mul_pos hweight hres) hres⟩

/-- A fully instantiated certificate for any divisor atom of the later period.
All composite squarefree candidates remain available. -/
theorem rationalStageDisplacement_ge_divisor_correlation {n m d : ℕ}
    (hd : 2 ≤ d) (hdvd : d ∣ primorialPeriod m) :
    rationalStageCorrelation n m (qResidue d) ^ 2 /
      rationalPair (primorialPeriod m) (qSequence (qResidue d))
        (qSequence (qResidue d)) ≤ rationalStageDisplacement n m := by
  apply rationalStageDisplacement_ge_correlation
  · exact Submodule.subset_span ⟨d, hd, hdvd, rfl⟩
  · simpa only [qSequence_qResidue] using
      rationalPair_residue_pos (primorialPeriod_pos m) hd

end RiemannResearch.RH.QRationalCoprimeTail
