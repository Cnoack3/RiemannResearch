/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.ZetaTwoCoordinateDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Exact quantitative squarefree jump obstructions

For a >= 2, the four-site square-jump functional annihilates the actual
closed squarefree residue span. Its Riesz vector has squared norm
2 * zetaTwo * (a^4 - a + 1). Every approximation error decomposes exactly
into its squared signed defect divided by this norm and a full norm-square
remainder.

For m >= 3, the exact indicator defect at a = m - 1 yields a positive
distance bound. Constants cannot cancel this individual indicator defect.
Finite signed indicator sums retain every signed contribution.

Source: the user-provided QDivisorLegality research handoff,
16 October 2026, especially its quantitative-obstruction and signed-sum
research targets. The energy proof is the standard Hilbert-space
decomposition along the explicitly constructed witness.

RH consumer: these tests certify obstructions to legality of divisibility
coordinate candidates. The constant passes every test, and no sufficiency
theorem, constant approximation estimate, or RH conclusion is asserted.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.QSquarefreeJumpDistance
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open SquarefreeRadicalDifference QDivisorLegality

/-- The complete four-site Riesz vector of the square-jump defect. -/
def squareJumpWitness (a : ℕ) : QHilbert :=
  qSiteRiesz (a ^ 2) - qSiteRiesz (a ^ 2 - 1) -
    qSiteRiesz a + qSiteRiesz (a - 1)

/-- Pairing with the witness is exactly the signed difference of the two jumps. -/
theorem squareJumpWitness_inner (a : ℕ) (ha : 2 ≤ a) (x : QHilbert) :
    inner ℝ (squareJumpWitness a) x =
      qDifference x (a ^ 2) - qDifference x a := by
  have ha2 : 4 ≤ a ^ 2 := by nlinarith
  rw [squareJumpWitness, inner_add_left, inner_sub_left, inner_sub_left]
  rw [qSiteRiesz_inner _ (by omega), qSiteRiesz_inner _ (by omega),
    qSiteRiesz_inner _ (by omega), qSiteRiesz_inner _ (by omega)]
  simp only [qDifference]
  ring

/-- Exact witness norm; all four disjoint support contributions are retained. -/
theorem squareJumpWitness_norm_sq (a : ℕ) (ha : 2 ≤ a) :
    ‖squareJumpWitness a‖ ^ 2 =
      2 * zetaTwo * ((a : ℝ) ^ 4 - a + 1) := by
  have h2 : 4 ≤ a ^ 2 := by nlinarith
  have hmul : 2 * a ≤ a ^ 2 := by nlinarith [Nat.mul_le_mul_left a ha]
  have hg : a < a ^ 2 - 1 := by omega
  have hw : ∀ n : ℕ, (positiveQWeight n)⁻¹ = zetaTwo * (n : ℝ) ^ 2 := by
    intro n
    simp [positiveQWeight]
  rw [← real_inner_self_eq_norm_sq, squareJumpWitness_inner a ha]
  simp only [qDifference]
  have hadd (x y : QHilbert) (n : ℕ) :
      qSequence (x + y) n = qSequence x n + qSequence y n :=
    congrFun (qSequenceLinear.map_add x y) n
  have hsub (x y : QHilbert) (n : ℕ) :
      qSequence (x - y) n = qSequence x n - qSequence y n :=
    congrFun (qSequenceLinear.map_sub x y) n
  simp only [squareJumpWitness, hadd, hsub,
    qSequence_qSiteRiesz (a ^ 2) (by omega),
    qSequence_qSiteRiesz (a ^ 2 - 1) (by omega),
    qSequence_qSiteRiesz a (by omega),
    qSequence_qSiteRiesz (a - 1) (by omega)]
  simp only [if_neg (show a ^ 2 ≠ a ^ 2 - 1 by omega),
    if_neg (show a ^ 2 ≠ a by omega),
    if_neg (show a ^ 2 ≠ a - 1 by omega),
    if_neg (show a ^ 2 - 1 ≠ a ^ 2 by omega),
    if_neg (show a ^ 2 - 1 ≠ a by omega),
    if_neg (show a ^ 2 - 1 ≠ a - 1 by omega),
    if_neg (show a ≠ a ^ 2 by omega),
    if_neg (show a ≠ a ^ 2 - 1 by omega),
    if_neg (show a ≠ a - 1 by omega),
    if_neg (show a - 1 ≠ a ^ 2 by omega),
    if_neg (show a - 1 ≠ a ^ 2 - 1 by omega),
    if_neg (show a - 1 ≠ a by omega)]
  simp only [ite_true]
  simp only [hw, Nat.cast_sub (by omega : 1 ≤ a),
    Nat.cast_sub (by omega : 1 ≤ a ^ 2), Nat.cast_pow, Nat.cast_one]
  ring


/-- The witness is orthogonal to the entire closed squarefree legal subspace. -/
theorem squareJumpWitness_inner_eq_zero (a : ℕ) (ha : 2 ≤ a)
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    inner ℝ (squareJumpWitness a) F = 0 := by
  rw [squareJumpWitness_inner a ha, squarefree_closure_difference_square a ha F hF, sub_self]

/-- Strict positivity of the exact squared witness norm. -/
theorem squareJumpDenominator_pos (a : ℕ) (ha : 2 ≤ a) :
    0 < 2 * zetaTwo * ((a : ℝ) ^ 4 - a + 1) := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hs : (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
  have hs4 : (a : ℝ) ^ 2 ≤ (a : ℝ) ^ 4 := by nlinarith [sq_nonneg ((a : ℝ)^2 - 1)]
  have hp : 0 < (a : ℝ)^4 - a + 1 := by linarith
  exact mul_pos (mul_pos (by norm_num) zetaTwo_pos) hp

/-- Complete Hilbert energy decomposition, with the entire squared-norm remainder. -/
theorem squareJump_energy_exact (a : ℕ) (ha : 2 ≤ a) (x : QHilbert) :
    ‖x‖ ^ 2 =
      (qDifference x (a ^ 2) - qDifference x a) ^ 2 /
        (2 * zetaTwo * ((a : ℝ)^4 - a + 1)) +
      ‖x - ((qDifference x (a ^ 2) - qDifference x a) /
        (2 * zetaTwo * ((a : ℝ)^4 - a + 1))) • squareJumpWitness a‖ ^ 2 := by
  have hD := ne_of_gt (squareJumpDenominator_pos a ha)
  have hi : inner ℝ x (squareJumpWitness a) =
      qDifference x (a ^ 2) - qDifference x a := by
    rw [real_inner_comm]
    exact squareJumpWitness_inner a ha x
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, squareJumpWitness_norm_sq a ha]
  field_simp [hD]
  ring

/-- The exact minus-one indicator defect extracts a fixed positive error energy. -/
theorem qDivisor_error_energy_exact (m : ℕ) (hm : 3 ≤ m)
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    ‖qDivisor m - F‖ ^ 2 =
      1 / (2 * zetaTwo * (((m - 1 : ℕ) : ℝ)^4 - (m - 1 : ℕ) + 1)) +
      ‖qDivisor m - F +
        (1 / (2 * zetaTwo * (((m - 1 : ℕ) : ℝ)^4 - (m - 1 : ℕ) + 1))) •
          squareJumpWitness (m - 1)‖ ^ 2 := by
  have ha : 2 ≤ m - 1 := by omega
  have he : qDifference (qDivisor m - F) ((m - 1)^2) -
      qDifference (qDivisor m - F) (m - 1) = -1 := by
    rw [qDifference_sub, qDifference_sub,
      squarefree_closure_difference_square (m - 1) ha F hF]
    linarith [qDivisor_square_jump_defect m hm]
  rw [squareJump_energy_exact (m - 1) ha (qDivisor m - F), he]
  simp only [neg_one_sq, neg_div, neg_smul, sub_neg_eq_add]

/-- A positive squared distance bound valid against every closed-span legal vector. -/
theorem qDivisor_error_sq_lower_bound (m : ℕ) (hm : 3 ≤ m)
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    1 / (2 * zetaTwo * (((m - 1 : ℕ) : ℝ)^4 - (m - 1 : ℕ) + 1)) ≤
      ‖qDivisor m - F‖ ^ 2 := by
  rw [qDivisor_error_energy_exact m hm F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)


/-- The continuous linear square-jump test represented by the actual witness. -/
def squareJumpFunctional (a : ℕ) : QHilbert →L[ℝ] ℝ :=
  innerSL ℝ (squareJumpWitness a)

/-- The continuous functional agrees with the literal four-site signed test. -/
theorem squareJumpFunctional_apply (a : ℕ) (ha : 2 ≤ a) (x : QHilbert) :
    squareJumpFunctional a x = qDifference x (a ^ 2) - qDifference x a :=
  squareJumpWitness_inner a ha x

/-- The operator norm of the test is computed exactly. -/
theorem squareJumpFunctional_norm_sq (a : ℕ) (ha : 2 ≤ a) :
    ‖squareJumpFunctional a‖ ^ 2 =
      2 * zetaTwo * ((a : ℝ) ^ 4 - a + 1) := by
  rw [squareJumpFunctional, innerSL_apply_norm, squareJumpWitness_norm_sq a ha]


/-- Exact one-row decomposition of every legal approximation error. -/
theorem squarefree_error_energy_exact (a : ℕ) (ha : 2 ≤ a)
    (x F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    ‖x - F‖ ^ 2 =
      (squareJumpFunctional a x) ^ 2 /
        (2 * zetaTwo * ((a : ℝ)^4 - a + 1)) +
      ‖x - F - ((squareJumpFunctional a x) /
        (2 * zetaTwo * ((a : ℝ)^4 - a + 1))) • squareJumpWitness a‖ ^ 2 := by
  have he : qDifference (x - F) (a ^ 2) - qDifference (x - F) a =
      squareJumpFunctional a x := by
    rw [squareJumpFunctional_apply a ha, qDifference_sub, qDifference_sub,
      squarefree_closure_difference_square a ha F hF]
    ring
  rw [squareJump_energy_exact a ha (x - F), he]

/-- The signed target defect gives a quantitative lower bound for every legal error. -/
theorem squarefree_error_sq_lower_bound (a : ℕ) (ha : 2 ≤ a)
    (x F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    (squareJumpFunctional a x) ^ 2 /
        (2 * zetaTwo * ((a : ℝ)^4 - a + 1)) ≤ ‖x - F‖ ^ 2 := by
  rw [squarefree_error_energy_exact a ha x F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- All coefficients and all four site contributions are retained. -/
theorem squareJumpFunctional_sum_divisors (a : ℕ) (ha : 2 ≤ a)
    (s : Finset ℕ) (b : ℕ → ℝ) :
    squareJumpFunctional a (∑ m ∈ s, b m • qDivisor m) =
      ∑ m ∈ s, b m * (positiveDivisor m (a ^ 2) -
        positiveDivisor m (a ^ 2 - 1) - positiveDivisor m a +
        positiveDivisor m (a - 1)) := by
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [squareJumpFunctional_apply a ha]
  simp only [qDifference, qSequence_qDivisor]
  ring

/-- Adding a constant cannot cancel an individual indicator's square-jump obstruction. -/
theorem affine_qDivisor_mem_squarefreeClosure_iff (m : ℕ) (hm : 3 ≤ m)
    (α β : ℝ) :
    α • qOne + β • qDivisor m ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      β = 0 ∧ α • qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  have ha : 2 ≤ m - 1 := by omega
  constructor
  · intro h
    have hz := squareJumpWitness_inner_eq_zero (m - 1) ha _ h
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      squareJumpWitness_inner (m - 1) ha qOne,
      squareJumpWitness_inner (m - 1) ha (qDivisor m),
      qDifference_qOne ((m - 1)^2) (by nlinarith),
      qDifference_qOne (m - 1) ha, qDivisor_square_jump_defect m hm] at hz
    have hβ : β = 0 := by linarith
    exact ⟨hβ, by simpa only [hβ, zero_smul, add_zero] using h⟩
  · rintro ⟨rfl, h⟩
    simpa only [zero_smul, add_zero] using h

/-- Smallest indicator witness: an explicit positive squared distance from the legal closure. -/
theorem qDivisor_three_error_sq_lower_bound
    (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    1 / (30 * zetaTwo) ≤ ‖qDivisor 3 - F‖ ^ 2 := by
  convert qDivisor_error_sq_lower_bound 3 (by decide) F hF using 1
  norm_num
  ring


end RiemannResearch.RH.QSquarefreeJumpDistance
