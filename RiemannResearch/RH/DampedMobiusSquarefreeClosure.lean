/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusHalfHilbertConvergence
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ArithmeticFloorHilbertSeries
import RiemannResearch.RH.DampedMobiusSeed
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.CRTSquarefreeConverse
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual squarefree legality of the damped Möbius cutoffs and their limits

Source for the squarefree support argument: B. Bagchi, "On Nyman, Beurling
and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis",
arXiv:math/0607733, Remarks 4 and 8. This reference supports the support
restriction and the two-limit proof strategy, not an unconditional RH claim.

The cutoff is exactly `-∑ μ(d) d^(-ε) g_d`, with no boundary correction
and no nonsquarefree conductor introduced. The existing natural-order
convergence theorem for `ε ≥ 1/2` now gives actual vectors in the closed
squarefree span in both P and Q. Extending convergence to every positive
damping under RH, and passing to damping zero, remain analytic obligations.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- Exact normalization, retaining the sign of every arithmetic coefficient. -/
theorem arithmeticResidueTerm_eq_normalized (w : ℕ → ℝ) (m : ℕ) :
    arithmeticResidueTerm w m =
      w (m + 1) • normalizedResidueHilbert (m + 1) (by omega) := by
  apply hilbertSequence_injective
  funext n
  rw [arithmeticResidueTerm_sequence]
  have h := congrFun (hilbertSequenceLinear.map_smul (w (m + 1))
    (normalizedResidueHilbert (m + 1) (by omega))) n
  change hilbertSequence (_ • _) n = _ at h
  rw [h]
  change w (m + 1) / ((m + 1 : ℕ) : ℝ) * residue (m + 1) n =
    w (m + 1) * hilbertSequence (normalizedResidueHilbert (m + 1) (by omega)) n
  rw [normalizedResidueHilbert_sequence]
  simp only [residue, residueFraction]
  ring

/-- Literal signed physical coordinates of the finite Bagchi cutoff. -/
theorem dampedMobius_partial_sequence (ε : ℝ) (N n : ℕ) :
    hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) n =
      -(∑ m ∈ Finset.range N, dampedMobiusWeight ε (m + 1) * residueFraction (m + 1) n) := by
  change hilbertSequenceLinear
    (-(∑ m ∈ Finset.range N, arithmeticResidueTerm (dampedMobiusWeight ε) m)) n = _
  rw [map_neg, map_sum]
  simp only [arithmeticResidueTerm_eq_normalized, map_smul, Pi.neg_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change -(∑ m ∈ Finset.range N, dampedMobiusWeight ε (m + 1) *
    hilbertSequence (normalizedResidueHilbert (m + 1) (by omega)) n) = _
  simp only [normalizedResidueHilbert_sequence]

/-- A finite physical bound for the boundary integral. It depends on N and
is not a uniform estimate as the damping decreases or the cutoff grows. -/
theorem dampedMobius_partial_abs_le (ε : ℝ) (N n : ℕ) :
    |hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) n| ≤
      ∑ m ∈ Finset.range N, |dampedMobiusWeight ε (m + 1)| := by
  rw [dampedMobius_partial_sequence, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro m _
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (residueFraction_abs_le_one (m + 1) n (Nat.succ_pos m)) (abs_nonneg _)

/-- Möbius damping never introduces an illegal nonsquarefree conductor. -/
theorem dampedMobius_partial_mem_squarefreeSpan (ε : ℝ) (N : ℕ) :
    arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N ∈ squarefreeCRTSpan := by
  classical
  apply squarefreeCRTSpan.neg_mem
  apply squarefreeCRTSpan.sum_mem
  intro m _
  rw [arithmeticResidueTerm_eq_normalized]
  by_cases hsf : Squarefree (m + 1)
  · by_cases htwo : 2 ≤ m + 1
    · apply squarefreeCRTSpan.smul_mem
      rw [squarefreeCRTSpan_eq_span]
      exact Submodule.subset_span ⟨⟨m + 1, htwo, hsf⟩, rfl⟩
    · have he : m + 1 = 1 := by omega
      have hz : normalizedResidueHilbert (m + 1) (by omega) = 0 := by
        apply hilbertSequence_injective
        rw [normalizedResidueHilbert_sequence]
        change residueFraction (m + 1) = hilbertSequenceLinear 0
        rw [map_zero]
        ext n
        simp [he, residueFraction, Nat.mod_one]
      rw [hz, smul_zero]
      exact squarefreeCRTSpan.zero_mem
  · have hz : dampedMobiusWeight ε (m + 1) = 0 := by
      simp [dampedMobiusWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    rw [hz, zero_smul]
    exact squarefreeCRTSpan.zero_mem

/-- Every naturally ordered Hilbert limit of these exact cutoffs is squarefree legal. -/
theorem dampedMobius_limit_mem_squarefreeClosure (ε : ℝ) (f : ThresholdHilbert)
    (hf : Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f)) :
    f ∈ squarefreeCRTSpan.topologicalClosure :=
  squarefreeCRTSpan.isClosed_topologicalClosure.mem_of_tendsto hf
    (Eventually.of_forall (fun N => squarefreeCRTSpan.le_topologicalClosure
      (dampedMobius_partial_mem_squarefreeSpan ε N)))

/-- Unconditional squarefree legal limits throughout the closed half-damping range. -/
theorem dampedMobius_squarefree_limits_of_half_le {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    ∃ f : ThresholdHilbert, f ∈ squarefreeCRTSpan.topologicalClosure ∧
      (∀ n : ℕ, hilbertSequence f n = dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ∧
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  obtain ⟨f, hc, hf⟩ := dampedMobius_cutoffs_converge_of_half_le hε
  exact ⟨f, dampedMobius_limit_mem_squarefreeClosure ε f hf, hc, hf⟩

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.DampedMobiusSquarefreeClosure
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence

/-- The same finite legal combination, reencoded with Q weights. -/
def qDampedMobiusPartial (ε : ℝ) (N : ℕ) : QHilbert :=
  toQ (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N)

/-- Complete squarefree closure transfer for an arbitrary target vector. -/
theorem toQ_mem_squarefreeClosure_iff (f : ThresholdHilbert) :
    toQ f ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      f ∈ squarefreeCRTSpan.topologicalClosure := by
  have h := mem_closure_map_iff qSquarefreeCRTSpan (toQ f)
  change toPareto (toQ f) ∈
    (qSquarefreeCRTSpan.map toParetoLinear).topologicalClosure ↔
      toQ f ∈ qSquarefreeCRTSpan.topologicalClosure at h
  rw [qSquarefreeCRTSpan_map, toPareto_toQ] at h
  exact h.symm

/-- Literal Q residue coefficients, with no modification at the cutoff. -/
theorem qDampedMobiusPartial_eq (ε : ℝ) (N : ℕ) :
    qDampedMobiusPartial ε N =
      -(∑ m ∈ Finset.range N, dampedMobiusWeight ε (m + 1) • qResidue (m + 1)) := by
  change toQLinear (-(∑ m ∈ Finset.range N,
    arithmeticResidueTerm (dampedMobiusWeight ε) m)) = _
  rw [map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [arithmeticResidueTerm_eq_normalized, map_smul]
  change dampedMobiusWeight ε (m + 1) •
    toQ (normalizedResidueHilbert (m + 1) (by omega)) = _
  have he : normalizedResidueHilbert (m + 1) (by omega) =
      BaezDuarte.residueVector (m + 1) := by simp [BaezDuarte.residueVector]
  rw [he, toQ_residueVector (m + 1) (by omega)]

/-- The actual Q cutoffs converge to squarefree legal vectors for ε ≥ 1/2. -/
theorem qDampedMobius_squarefree_limits_of_half_le {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    ∃ f : QHilbert, f ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      (∀ n : ℕ, qSequence f n = dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ∧
      Tendsto (qDampedMobiusPartial ε) atTop (𝓝 f) := by
  obtain ⟨f, hm, hc, hf⟩ := dampedMobius_squarefree_limits_of_half_le hε
  refine ⟨toQ f, (toQ_mem_squarefreeClosure_iff f).mpr hm, ?_, ?_⟩
  · simpa only [toQ_sequence] using hc
  · exact toQCLM.continuous.continuousAt.tendsto.comp hf

end RiemannResearch.RH.DampedMobiusSquarefreeClosure
