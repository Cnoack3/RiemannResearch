/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusSquarefreeClosure
import RiemannResearch.RH.HardyMobiusFamily
import RiemannResearch.RH.ParetoMellinHardyNorm
import RiemannResearch.RH.ParetoMellinFunctional
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.CRTSquarefreeConverse
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact Hardy norm bridge for Bagchi's actual squarefree Möbius cutoffs

Source: B. Bagchi, arXiv:math/0607733, proof of Theorem 2 and Remarks 4 and 8,
for the damped family and the two-limit argument. The complete finite
Mellin identity and norm-bound equivalence are proved here. The analytic
RH-to-approximation estimate is not assumed as an axiom or claimed proved.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

/-- The exact finite Mellin polynomial, with removable values inherited from the atoms. -/
def dampedHardyMobiusSum (ε : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range N,
    (dampedMobiusWeight ε (m + 1) : ℂ) * hardyMobiusGenerator (m + 1) s

/-- No boundary correction appears in the exact transform. -/
theorem dampedMobius_partial_mellin (ε : ℝ) (N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) s =
      dampedHardyMobiusSum ε N s := by
  change (paretoMellinContinuous s hs)
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) = _
  unfold arithmeticFloorHilbertPartial
  rw [map_neg, map_sum]
  simp only [arithmeticResidueTerm_eq_normalized, map_smul]
  change -(∑ m ∈ Finset.range N, dampedMobiusWeight ε (m + 1) •
    paretoMellin (normalizedResidueHilbert (m + 1) (by omega)) s) = _
  simp_rw [normalizedResidue_mellin_eq_neg_hardyMobiusGenerator _ _ s (by linarith)]
  simp only [Complex.real_smul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rfl

/-- Exact finite zeta expression, keeping the full signed charge. -/
theorem dampedHardyMobiusSum_eq_zeta (ε : ℝ) (N : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    dampedHardyMobiusSum ε N s = riemannZeta s / s *
      ((∑ m ∈ Finset.range N,
        (dampedMobiusWeight ε (m + 1) : ℂ) * ((m + 1 : ℕ) : ℂ) ^ (-s)) -
       (∑ m ∈ Finset.range N,
        (dampedMobiusWeight ε (m + 1) : ℂ) / ((m + 1 : ℕ) : ℂ))) := by
  unfold dampedHardyMobiusSum
  have hg (m : ℕ) : hardyMobiusGenerator (m + 1) s =
      (((m + 1 : ℕ) : ℂ) ^ (-s) - 1 / ((m + 1 : ℕ) : ℂ)) * riemannZeta s / s :=
    hardyMobiusGenerator_eq_zeta (m + 1) (Nat.succ_pos m) s hs hs1
  simp_rw [hg]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Residual transform with all signs and the constant target retained. -/
theorem dampedMobius_residual_mellin (ε : ℝ) (N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) s =
      1 / s - dampedHardyMobiusSum ε N s := by
  change (paretoMellinContinuous s hs)
    (hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) = _
  rw [map_sub]
  exact congrArg₂ (· - ·) (paretoMellin_one s hs) (dampedMobius_partial_mellin ε N s hs)

/-- An exact equivalence with a uniform analytic estimate on the entire critical half-plane. -/
theorem dampedMobius_residual_norm_sq_le_iff (ε : ℝ) (N : ℕ) (B : ℝ) :
    ‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 ≤ B ↔
      ∀ σ : ℝ, (1 / 2 : ℝ) < σ →
        (∫ w : ℝ, ‖1 / WeightedMellin.verticalPoint σ w -
          dampedHardyMobiusSum ε N (WeightedMellin.verticalPoint σ w)‖ ^ 2) ≤ B := by
  have he (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) :
      (∫ w : ℝ, ‖paretoMellin
        (hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N)
          (WeightedMellin.verticalPoint σ w)‖ ^ 2) =
      (∫ w : ℝ, ‖1 / WeightedMellin.verticalPoint σ w -
        dampedHardyMobiusSum ε N (WeightedMellin.verticalPoint σ w)‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [] with w
    rw [dampedMobius_residual_mellin]
    simpa only [WeightedMellin.verticalPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hσ
  rw [paretoMellin_norm_sq_le_iff]
  constructor
  · intro h σ hσ
    rw [← he σ hσ]
    exact h σ hσ
  · intro h σ hσ
    rw [he σ hσ]
    exact h σ hσ

/-- The actual finite residual has the exact ordinary critical-line norm.
Its required physical boundedness is proved here, not supplied by the caller. -/
theorem dampedMobius_residual_critical_line_norm (ε : ℝ) (N : ℕ) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ,
      ‖paretoMellin (hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N)
        ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) =
      ‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 := by
  apply paretoMellin_critical_line_norm _
    (1 + ∑ m ∈ Finset.range N, |dampedMobiusWeight ε (m + 1)|)
  intro n
  have he := congrFun (hilbertSequenceLinear.map_sub hilbertOne
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N)) n
  change hilbertSequence (_ - _) n =
    hilbertSequence hilbertOne n -
      hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) n at he
  rw [he]
  apply (abs_sub _ _).trans
  apply add_le_add _ (dampedMobius_partial_abs_le ε N n)
  rw [hilbertOne_sequence]
  by_cases hn : n = 0 <;> simp [zeroAnchor, hn]

/-- The concrete analytic estimate still to be proved from RH. This definition
does not assert it, and the theorems below retain it as an explicit premise. -/
def DampedHardyApproximation : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
    ∀ σ : ℝ, (1 / 2 : ℝ) < σ →
      (∫ w : ℝ, ‖1 / WeightedMellin.verticalPoint σ w -
        dampedHardyMobiusSum ε N (WeightedMellin.verticalPoint σ w)‖ ^ 2) ≤ δ

/-- Conditional research reduction: the literal uniform line estimate supplies
squarefree closure membership. Legality and the complete norm identification
are proved internally; the displayed analytic estimate remains the premise. -/
theorem squarefreeClosure_of_dampedHardyApproximation
    (h : DampedHardyApproximation) :
    hilbertOne ∈ squarefreeCRTSpan.topologicalClosure := by
  apply Metric.mem_closure_iff.mpr
  intro η hη
  obtain ⟨ε, _, N, hN⟩ := h ((η / 2) ^ 2) (sq_pos_of_pos (half_pos hη))
  refine ⟨arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N,
    dampedMobius_partial_mem_squarefreeSpan ε N, ?_⟩
  have hb := (dampedMobius_residual_norm_sq_le_iff ε N ((η / 2) ^ 2)).mpr hN
  rw [dist_eq_norm]
  nlinarith [norm_nonneg
    (hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N)]

/-- The same conditional analytic estimate gives the actual Q target. -/
theorem qSquarefreeClosure_of_dampedHardyApproximation
    (h : DampedHardyApproximation) :
    ZetaTwoHilbert.qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure :=
  ZetaTwoProbability.qSquarefreeClosure_iff_paretoSquarefreeClosure.mpr
    (squarefreeClosure_of_dampedHardyApproximation h)

/-- Conditional research reduction to Mathlib's RH. No external density
theorem is used by this direction of the bridge. -/
theorem riemannHypothesis_of_dampedHardyApproximation
    (h : DampedHardyApproximation) : RiemannHypothesis := by
  have ht := squarefreeClosure_iff_exact_head_tail_bound.mp
    (squarefreeClosure_of_dampedHardyApproximation h)
  obtain ⟨C, hC⟩ := ht
  choose L F hL hF hh hb using hC
  apply riemannHypothesis_of_squarefree_span_bounded_tail (fun n => n) L F
    tendsto_id hL hF hh
  exact ⟨C, by rintro x ⟨j, rfl⟩; exact hb j⟩

end RiemannResearch.RH.Pareto
