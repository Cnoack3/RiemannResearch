/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.QRationalWeightComparison
import RiemannResearch.RH.QSquarefreeJumpApplications
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Conditional nonlegality at the actual primorial six

Source: user-directed CRT/profinite continuation, 20 October 2026;
`QPrimorialSixConditionalObstruction20261020.md` gives the ordinary argument.
The target is the actual complete-Q conditional image C_6 g_5. Four initial
terms in each fiber are retained exactly; the complete remaining tail is
bounded with the midpoint identity in QRationalWeightComparison. No numerical
approximation or RH hypothesis enters the certificate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimorialSixConditionalObstruction
open ZetaTwoProbability ZetaTwoHilbert ArithmeticCumulative
open QResidueConditional QSquarefreeJumpDistance QDivisorLegality
open SquarefreeRadicalDifference

private theorem five_bounds (n : ℕ) :
    0 ≤ residueFraction 5 n ∧ residueFraction 5 n ≤ (4 / 5 : ℝ) := by
  have hm : n % 5 ≤ 4 := by omega
  constructor
  · unfold residueFraction
    positivity
  · unfold residueFraction
    norm_num only [Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (by norm_num)

private theorem five_abs_bound (n : ℕ) : |residueFraction 5 n| ≤ (4 / 5 : ℝ) := by
  rw [abs_of_nonneg (five_bounds n).1]
  exact (five_bounds n).2

private theorem zeta_cancel (x : ℝ) :
    zetaTwo * (1 / (zetaTwo * x^2)) = 1 / x^2 := by
  calc
    _ = (zetaTwo * zetaTwo⁻¹) * (x^2)⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt zetaTwo_pos), one_mul, one_div]

private theorem zeta_weight_cancel (n : ℕ) :
    zetaTwo * positiveQWeight n = 1 / (n : ℝ)^2 := by
  exact zeta_cancel (n : ℝ)

def rawMass (a : ℕ) : ℝ :=
  ∑' j : ℕ, 1 / ((a + 6*j : ℕ) : ℝ)^2

def rawMoment (a : ℕ) : ℝ :=
  ∑' j : ℕ, residueFraction 5 (a + 6*j) / ((a + 6*j : ℕ) : ℝ)^2

private theorem rawMass_summable (a : ℕ) (ha : 0 < a) :
    Summable (fun j : ℕ => 1 / ((a + 6*j : ℕ) : ℝ)^2) := by
  have hs := (residuePowerWeight_summable 0 (by norm_num : (0 : ℝ) < 6)
    (by exact_mod_cast ha : (0 : ℝ) < a)).mul_left zetaTwo
  exact hs.congr (fun j => by
    simp only [Nat.zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_comm (j : ℝ) 6]
    exact zeta_cancel _)

private theorem rawMoment_summable (a : ℕ) (ha : 0 < a) :
    Summable (fun j : ℕ =>
      residueFraction 5 (a + 6*j) / ((a + 6*j : ℕ) : ℝ)^2) := by
  have hs := (fiber_terms_summable 6 a (by decide) ha
    (residueFraction 5) five_abs_bound).mul_left zetaTwo
  exact hs.congr (fun j => by
    calc
      zetaTwo * (positiveQWeight (a + 6*j) * residueFraction 5 (a + 6*j)) =
          (zetaTwo * positiveQWeight (a + 6*j)) * residueFraction 5 (a + 6*j) := by ring
      _ = _ := by rw [zeta_weight_cancel]; ring)

theorem rawMass_eq_complete (a : ℕ) :
    rawMass a = zetaTwo * residuePowerWeight 0 6 a := by
  unfold rawMass residuePowerWeight
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_comm (j : ℝ) 6]
  exact (zeta_cancel _).symm

theorem rawMoment_eq_complete (a : ℕ) :
    rawMoment a = zetaTwo * fiberSum 6 a (residueFraction 5) := by
  unfold rawMoment fiberSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  calc
    _ = (zetaTwo * positiveQWeight (a + 6*j)) * residueFraction 5 (a + 6*j) := by
      rw [zeta_weight_cancel]
      ring
    _ = _ := by ring

theorem rawMass_pos (a : ℕ) (ha : 0 < a) : 0 < rawMass a := by
  rw [rawMass_eq_complete]
  exact mul_pos zetaTwo_pos (residuePowerWeight_pos 0 (by norm_num) (by exact_mod_cast ha))

theorem conditional_eq_raw_ratio (a : ℕ) :
    conditionalValue 6 a (residueFraction 5) = rawMoment a / rawMass a := by
  rw [rawMoment_eq_complete, rawMass_eq_complete]
  unfold conditionalValue
  field_simp [ne_of_gt zetaTwo_pos]
  <;> norm_num

/-- Complete fiber moment inequalities; every remaining positive integer is included. -/
theorem rawMoment_bounds (a : ℕ) (ha : 0 < a) :
    0 ≤ rawMoment a ∧ rawMoment a ≤ (4 / 5 : ℝ) * rawMass a := by
  constructor
  · unfold rawMoment
    exact tsum_nonneg (fun j => div_nonneg (five_bounds _).1 (sq_nonneg _))
  · rw [rawMoment, rawMass, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (rawMoment_summable a ha)
      ((rawMass_summable a ha).mul_left (4 / 5 : ℝ))
    intro j
    convert div_le_div_of_nonneg_right (five_bounds (a + 6*j)).2
      (sq_nonneg (((a + 6*j : ℕ) : ℝ))) using 1 <;> ring

def headMass (a : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 4, 1 / ((a + 6*j : ℕ) : ℝ)^2

def headMoment (a : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 4,
    residueFraction 5 (a + 6*j) / ((a + 6*j : ℕ) : ℝ)^2

/-- Exact prefix and complete tail, before any bound is applied. -/
theorem rawMass_prefix_exact (a : ℕ) (ha : 0 < a) :
    rawMass a = headMass a + rawMass (a + 24) := by
  have h := (rawMass_summable a ha).sum_add_tsum_nat_add 4
  unfold rawMass
  rw [← h]
  unfold headMass
  congr 1
  apply tsum_congr
  intro j
  rw [show a + 6*(j+4) = a + 24 + 6*j by omega]

/-- Exact signed observable moment, retaining the complete remaining fiber. -/
theorem rawMoment_prefix_exact (a : ℕ) (ha : 0 < a) :
    rawMoment a = headMoment a + rawMoment (a + 24) := by
  have h := (rawMoment_summable a ha).sum_add_tsum_nat_add 4
  unfold rawMoment
  rw [← h]
  unfold headMoment
  congr 1
  apply tsum_congr
  intro j
  rw [show a + 6*(j+4) = a + 24 + 6*j by omega]

def tailCap (a : ℕ) : ℝ :=
  1 / ((a : ℝ) + 24)^2 + 2 / (6 * (2 * ((a : ℝ) + 24) + 6))

theorem complete_tail_le_cap (a : ℕ) : rawMass (a + 24) ≤ tailCap a := by
  rw [rawMass_eq_complete]
  unfold tailCap
  convert QRationalCoprimeTail.residueSquareWeight_le_rational
    (by norm_num : (0 : ℝ) < 6)
    (by positivity : (0 : ℝ) < (a : ℝ) + 24) using 1
  <;> push_cast <;> rfl

theorem headMoment_nonneg (a : ℕ) : 0 ≤ headMoment a := by
  unfold headMoment
  exact Finset.sum_nonneg (fun j _ => div_nonneg (five_bounds _).1 (sq_nonneg _))

/-- The literal complete conditional value has these certified rational endpoints. -/
theorem conditional_interval (a : ℕ) (ha : 0 < a) (hD : 0 < headMass a) :
    headMoment a / (headMass a + tailCap a) ≤ conditionalValue 6 a (residueFraction 5) ∧
      conditionalValue 6 a (residueFraction 5) ≤
        (headMoment a + (4 / 5 : ℝ) * tailCap a) / headMass a := by
  rw [conditional_eq_raw_ratio, rawMoment_prefix_exact a ha, rawMass_prefix_exact a ha]
  have ht : 0 ≤ rawMass (a+24) := (rawMass_pos (a+24) (by omega)).le
  have hcap := complete_tail_le_cap a
  have hn := headMoment_nonneg a
  have he := rawMoment_bounds (a+24) (by omega)
  have hcap0 : 0 ≤ tailCap a := ht.trans hcap
  have hden : 0 < headMass a + rawMass (a+24) := by linarith
  have hdenCap : 0 < headMass a + tailCap a := by linarith
  constructor
  · calc
      headMoment a / (headMass a + tailCap a) ≤
          headMoment a / (headMass a + rawMass (a+24)) :=
        div_le_div_of_nonneg_left hn hden (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith [he.1]) hden.le
  · calc
      (headMoment a + rawMoment (a+24)) / (headMass a + rawMass (a+24)) ≤
          (headMoment a + (4 / 5 : ℝ) * tailCap a) /
            (headMass a + rawMass (a+24)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        nlinarith [he.2]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hD (by linarith)

/-- Four exact rational endpoint checks; no floating-point arithmetic is used. -/
theorem conditional_four_bounds :
    conditionalValue 6 1 (residueFraction 5) ≤ (214 / 1000 : ℝ) ∧
    conditionalValue 6 4 (residueFraction 5) ≤ (726 / 1000 : ℝ) ∧
    (404 / 1000 : ℝ) ≤ conditionalValue 6 2 (residueFraction 5) ∧
    (561 / 1000 : ℝ) ≤ conditionalValue 6 3 (residueFraction 5) := by
  have h1 := conditional_interval 1 (by decide)
    (by norm_num [headMass, Finset.sum_range_succ])
  have h2 := conditional_interval 2 (by decide)
    (by norm_num [headMass, Finset.sum_range_succ])
  have h3 := conditional_interval 3 (by decide)
    (by norm_num [headMass, Finset.sum_range_succ])
  have h4 := conditional_interval 4 (by decide)
    (by norm_num [headMass, Finset.sum_range_succ])
  norm_num [headMass, headMoment, tailCap, Finset.sum_range_succ, residueFraction] at h1 h2 h3 h4
  constructor
  · linarith [h1.2]
  constructor
  · linarith [h4.2]
  constructor
  · linarith [h2.1]
  · linarith [h3.1]

theorem conditional_value_bounds (a : ℕ) (ha : 0 < a) :
    0 ≤ conditionalValue 6 a (residueFraction 5) ∧
      conditionalValue 6 a (residueFraction 5) ≤ (4 / 5 : ℝ) := by
  rw [conditional_eq_raw_ratio]
  have h := rawMoment_bounds a ha
  constructor
  · exact div_nonneg h.1 (rawMass_pos a ha).le
  · exact (div_le_iff₀ (rawMass_pos a ha)).mpr h.2

def conditionalSequence (n : ℕ) : ℝ :=
  if n = 0 then 0 else conditionalValue 6 ((n-1)%6+1) (residueFraction 5)

theorem conditionalSequence_bound (n : ℕ) : |conditionalSequence n| ≤ (4 / 5 : ℝ) := by
  unfold conditionalSequence
  split_ifs with hn
  · norm_num
  · have h := conditional_value_bounds ((n-1)%6+1) (by omega)
    rw [abs_of_nonneg h.1]
    exact h.2

/-- Actual complete-Q conditional image of the legal squarefree atom g_5. -/
def conditionalSixFive : QHilbert :=
  encodeQ conditionalSequence (boundedQ_square_summable _ (4 / 5 : ℝ)
    (by norm_num) conditionalSequence_bound)

@[simp] theorem conditionalSixFive_sequence : qSequence conditionalSixFive = conditionalSequence :=
  qSequence_encodeQ _ _ (by simp [conditionalSequence])

/-- Every physical positive coordinate is its complete residue-fiber conditional mean. -/
theorem conditionalSixFive_sequence_pos (n : ℕ) (hn : 0 < n) :
    qSequence conditionalSixFive n =
      conditionalValue 6 ((n-1)%6+1) (residueFraction 5) := by
  rw [conditionalSixFive_sequence]
  simp only [conditionalSequence, if_neg (ne_of_gt hn)]

def signedJump : ℝ := conditionalValue 6 4 (residueFraction 5) -
  conditionalValue 6 3 (residueFraction 5) - conditionalValue 6 2 (residueFraction 5) +
    conditionalValue 6 1 (residueFraction 5)

theorem signedJump_le : signedJump ≤ -(1 / 40 : ℝ) := by
  obtain ⟨h1,h4,h2,h3⟩ := conditional_four_bounds
  unfold signedJump
  linarith

theorem conditionalSixFive_squareJump :
    squareJumpFunctional 2 conditionalSixFive = signedJump := by
  rw [squareJumpFunctional_apply 2 (by decide)]
  simp only [qDifference, conditionalSixFive_sequence]
  norm_num [conditionalSequence, signedJump]
  ring

/-- The entire signed projection coefficient and orthogonal remainder are retained. -/
theorem conditionalSixFive_error_exact (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    ‖conditionalSixFive - F‖^2 = signedJump^2 / (30 * zetaTwo) +
      ‖conditionalSixFive - F - (signedJump / (30 * zetaTwo)) • squareJumpWitness 2‖^2 := by
  have h := squarefree_error_energy_exact 2 (by decide) conditionalSixFive F hF
  rw [conditionalSixFive_squareJump] at h
  norm_num at h
  convert h using 1 <;> congr 2 <;> ring

theorem conditionalSixFive_error_lower (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure) :
    1 / (48000 * zetaTwo) ≤ ‖conditionalSixFive - F‖^2 := by
  rw [conditionalSixFive_error_exact F hF]
  have hs : (1 / 1600 : ℝ) ≤ signedJump^2 := by nlinarith [signedJump_le]
  have hd : 0 < 30 * zetaTwo := by have := zetaTwo_pos; positivity
  have h := div_le_div_of_nonneg_right hs hd.le
  have he : (1 / 1600 : ℝ) / (30 * zetaTwo) = 1 / (48000 * zetaTwo) := by ring
  rw [he] at h
  exact h.trans (le_add_of_nonneg_right (sq_nonneg _))

theorem conditionalSixFive_not_mem_closure :
    conditionalSixFive ∉ qSquarefreeCRTSpan.topologicalClosure := by
  intro h
  have hz := squareJumpWitness_inner_eq_zero 2 (by decide) conditionalSixFive h
  change squareJumpFunctional 2 conditionalSixFive = 0 at hz
  rw [conditionalSixFive_squareJump] at hz
  linarith [signedJump_le]

theorem input_legal_output_not :
    qResidue 5 ∈ qSquarefreeCRTSpan.topologicalClosure ∧
      conditionalSixFive ∉ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · apply qSquarefreeCRTSpan.le_topologicalClosure
    exact Submodule.subset_span ⟨⟨5, by decide, (by norm_num : Nat.Prime 5).squarefree⟩, rfl⟩
  · exact conditionalSixFive_not_mem_closure

end RiemannResearch.RH.QPrimorialSixConditionalObstruction
