/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.QConductorLimits
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Singleton, product, and reflected-atom squarefree obstructions

Source: user-provided `Squarefree_Infinite_CRT_Continuation_2026-10-16`,
Sections 5--6. These are applications of the existing exact four-site
Riesz decomposition, retaining its entire norm-square remainder.
The singleton and the square of the legal atom g_3 are outside the legal
closure. Reflected squarefree atoms are individually outside the closure
even though their ambient limit is one. No limit of their legal distances
is asserted to vanish.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeJumpDistance
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open SquarefreeRadicalDifference QDivisorLegality ArithmeticCumulative

/-- The singleton at the physical site one has square-jump defect one. -/
theorem qPoint_zero_squareJump : squareJumpFunctional 2 (qPoint 0) = 1 := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, qSequence_qPoint]
  norm_num [qPointSequence]

/-- Exact singleton error, including the complete orthogonal remainder. -/
theorem qPoint_zero_error_energy_exact
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    ‖qPoint 0 - F‖ ^ 2 = 1 / (30 * zetaTwo) +
      ‖qPoint 0 - F - (1 / (30 * zetaTwo)) • squareJumpWitness 2‖ ^ 2 := by
  have h := squarefree_error_energy_exact 2 (by decide) (qPoint 0) F hF
  rw [qPoint_zero_squareJump] at h
  simp only [Nat.cast_ofNat] at h
  have hD : 2 * zetaTwo * ((2 : ℝ)^4 - 2 + 1) = 30 * zetaTwo := by
    norm_num
    ring
  simpa only [hD, one_pow] using h

theorem qPoint_zero_error_sq_lower_bound
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    1 / (30 * zetaTwo) ≤ ‖qPoint 0 - F‖ ^ 2 := by
  rw [qPoint_zero_error_energy_exact F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- In particular, e_1 cannot be a squarefree legal Q limit. -/
theorem qPoint_zero_not_mem_squarefreeClosure :
    qPoint 0 ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro h
  have hh := qPoint_zero_error_sq_lower_bound (qPoint 0) h
  have hp : 0 < 1 / (30 * zetaTwo) := by positivity [zetaTwo_pos]
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
  linarith

/-- Pointwise square of a bounded residue atom as an actual Q vector. -/
def qResidueSquare (d : ℕ) : QHilbert :=
  encodeQ (fun k => (residueFraction d k) ^ 2)
    (boundedQ_square_summable _ 1 zero_le_one (by
      intro k
      have hb : |residueFraction d k| ≤ 1 := by
        by_cases hd : d = 0
        · simp [residueFraction, hd]
        · have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
          unfold residueFraction
          rw [abs_of_nonneg (by positivity)]
          apply (div_le_iff₀ hdR).mpr
          simpa only [one_mul] using
            (show ((k % d : ℕ) : ℝ) ≤ d by
              exact_mod_cast (Nat.mod_lt k (Nat.pos_of_ne_zero hd)).le)
      rw [abs_of_nonneg (sq_nonneg _)]
      have hh := mul_le_mul hb hb (abs_nonneg _) zero_le_one
      simpa only [← pow_two, sq_abs, one_pow] using hh))

@[simp] theorem qResidueSquare_sequence (d : ℕ) :
    qSequence (qResidueSquare d) = fun k => (residueFraction d k) ^ 2 :=
  qSequence_encodeQ _ _ (by simp [residueFraction])

theorem qResidueSquare_three_squareJump :
    squareJumpFunctional 2 (qResidueSquare 3) = -(2 / 9 : ℝ) := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, qResidueSquare_sequence]
  norm_num [residueFraction]

/-- The full product error retains the signed projection coefficient. -/
theorem qResidueSquare_three_error_energy_exact
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    ‖qResidueSquare 3 - F‖ ^ 2 = 2 / (1215 * zetaTwo) +
      ‖qResidueSquare 3 - F + (1 / (135 * zetaTwo)) • squareJumpWitness 2‖ ^ 2 := by
  have h := squarefree_error_energy_exact 2 (by decide) (qResidueSquare 3) F hF
  rw [qResidueSquare_three_squareJump] at h
  simp only [Nat.cast_ofNat] at h
  have hc : (-(2 / 9 : ℝ)) / (2 * zetaTwo * ((2 : ℝ)^4 - 2 + 1)) =
      -(1 / (135 * zetaTwo)) := by
    norm_num
    field_simp
    ring
  have hv : (-(2 / 9 : ℝ))^2 / (2 * zetaTwo * ((2 : ℝ)^4 - 2 + 1)) =
      2 / (1215 * zetaTwo) := by
    norm_num
    field_simp
    ring
  rw [hc, hv, neg_smul, sub_neg_eq_add] at h
  exact h

theorem qResidueSquare_three_error_sq_lower_bound
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    2 / (1215 * zetaTwo) ≤ ‖qResidueSquare 3 - F‖ ^ 2 := by
  rw [qResidueSquare_three_error_energy_exact F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- A legal atom whose pointwise square is outside the closed legal span. -/
theorem qResidue_three_legal_but_square_not :
    qResidue 3 ∈ qSquarefreeCRTSpan ∧
      qResidueSquare 3 ∉ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · exact Submodule.subset_span ⟨⟨3, by decide, Nat.prime_three.squarefree⟩, rfl⟩
  · intro h
    have hh := qResidueSquare_three_error_sq_lower_bound (qResidueSquare 3) h
    have hp : 0 < 2 / (1215 * zetaTwo) := by positivity [zetaTwo_pos]
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
    linarith

/-- Each reflected squarefree atom has defect one at a = d - 1. -/
theorem qReflected_squareJump (d : ℕ) (hd : 3 ≤ d) (hsf : Squarefree d) :
    squareJumpFunctional (d - 1) (qReflected d) = 1 := by
  have ha : 2 ≤ d - 1 := by omega
  have hmem : qResidue d ∈ qSquarefreeCRTSpan.topologicalClosure :=
    qSquarefreeCRTSpan.le_topologicalClosure
      (Submodule.subset_span ⟨⟨d, by omega, hsf⟩, rfl⟩)
  have hres : squareJumpFunctional (d - 1) (qResidue d) = 0 :=
    squareJumpWitness_inner_eq_zero (d - 1) ha _ hmem
  have hone : squareJumpFunctional (d - 1) qOne = 0 := by
    rw [squareJumpFunctional_apply _ ha, qDifference_qOne _ (by nlinarith),
      qDifference_qOne _ ha, sub_self]
  have hdiv : squareJumpFunctional (d - 1) (qDivisor d) = -1 := by
    rw [squareJumpFunctional_apply _ ha]
    exact qDivisor_square_jump_defect d hd
  simp only [qReflected, map_sub, hone, hres, hdiv]
  norm_num

/-- A positive distance obstruction for every individual reflected squarefree atom. -/
theorem qReflected_error_sq_lower_bound (d : ℕ) (hd : 3 ≤ d) (hsf : Squarefree d)
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    1 / (2 * zetaTwo * (((d - 1 : ℕ) : ℝ) ^ 4 - (d - 1 : ℕ) + 1)) ≤
      ‖qReflected d - F‖ ^ 2 := by
  have h := squarefree_error_sq_lower_bound (d - 1) (by omega) (qReflected d) F hF
  simpa only [qReflected_squareJump d hd hsf, one_pow] using h

theorem qReflected_not_mem_squarefreeClosure (d : ℕ) (hd : 3 ≤ d)
    (hsf : Squarefree d) : qReflected d ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro h
  have hz := squareJumpWitness_inner_eq_zero (d - 1) (by omega) _ h
  change squareJumpFunctional (d - 1) (qReflected d) = 0 at hz
  rw [qReflected_squareJump d hd hsf] at hz
  norm_num at hz

/-- Continuity of distance identifies the asymptotic reflected-atom obstruction.
Distance here is the infimum over the algebraic legal span, equivalently its closure. -/
theorem qReflected_legalDistance_tendsto (d : ℕ → ℕ)
    (hd : Filter.Tendsto d Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => Metric.infDist (qReflected (d j))
      (qSquarefreeCRTSpan : Set QHilbert)) Filter.atTop
      (nhds (Metric.infDist qOne (qSquarefreeCRTSpan : Set QHilbert))) :=
  (Metric.continuous_infDist_pt _).continuousAt.tendsto.comp (qReflected_tendsto_one d hd)

/-- Reflected atoms become arbitrarily well approximable legally exactly when
the constant belongs to the closed squarefree span. No provider is asserted. -/
theorem qOne_mem_closure_iff_reflected_legalDistance_zero (d : ℕ → ℕ)
    (hd : Filter.Tendsto d Filter.atTop Filter.atTop) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      Filter.Tendsto (fun j => Metric.infDist (qReflected (d j))
        (qSquarefreeCRTSpan : Set QHilbert)) Filter.atTop (nhds 0) := by
  constructor
  · intro h
    have hz : Metric.infDist qOne (qSquarefreeCRTSpan : Set QHilbert) = 0 :=
      Metric.infDist_zero_of_mem_closure h
    simpa only [hz] using
      qReflected_legalDistance_tendsto d hd
  · intro h
    have hz := tendsto_nhds_unique (qReflected_legalDistance_tendsto d hd) h
    exact (Metric.mem_closure_iff_infDist_zero
      (show (qSquarefreeCRTSpan : Set QHilbert).Nonempty from
        ⟨0, qSquarefreeCRTSpan.zero_mem⟩)).mpr hz

end RiemannResearch.RH.QSquarefreeJumpDistance
