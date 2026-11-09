/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite Gram bounds from absolute row sums

The estimates apply to the energy of a synthesized vector and its observation
source. They have no dimension factor beyond the actual row sums.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [DecidableEq ι] in
theorem abs_quadratic_le_of_rowAbs (D : Matrix ι ι ℝ) (hD : ∀ i j, D i j = D j i)
    (d : ℝ) (hrow : ∀ i, (∑ j, |D i j|) ≤ d) (a : ι → ℝ) :
    |dotProduct a (D.mulVec a)| ≤ d * ∑ i, a i ^ 2 := by
  have habs (i j : ι) :
      |a i * (D i j * a j)| ≤ |D i j| * ((a i ^ 2 + a j ^ 2) / 2) := by
    rw [abs_mul, abs_mul]
    have h : |a i| * |a j| ≤ (a i ^ 2 + a j ^ 2) / 2 := by
      nlinarith [sq_nonneg (|a i| - |a j|), sq_abs (a i), sq_abs (a j)]
    calc
      _ = |D i j| * (|a i| * |a j|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  let S (i j : ι) := |D i j| * (a i ^ 2 / 2)
  have hswap : (∑ i, ∑ j, |D i j| * (a j ^ 2 / 2)) = ∑ i, ∑ j, S i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [S]
    rw [hD i j]
  have he : (∑ i, a i * ∑ j, D i j * a j) = ∑ i, ∑ j, a i * (D i j * a j) := by
    simp_rw [Finset.mul_sum]
  change |∑ i, a i * ∑ j, D i j * a j| ≤ _
  rw [he]
  calc
    _ ≤ ∑ i, |∑ j, a i * (D i j * a j)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (s := Finset.univ) (fun i => ∑ j, a i * (D i j * a j)))
    _ ≤ ∑ i, ∑ j, |a i * (D i j * a j)| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (s := Finset.univ) (fun j => a i * (D i j * a j)))
    _ ≤ ∑ i, ∑ j, |D i j| * ((a i ^ 2 + a j ^ 2) / 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => habs i j
    _ = ∑ i, (∑ j, |D i j|) * a i ^ 2 := by
      simp_rw [add_div, mul_add, Finset.sum_add_distrib]
      change (∑ i, ∑ j, S i j) + _ = _
      rw [hswap, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [S]
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)

theorem synthesis_quadratic_sub_le_of_rowDefect (v : ι → H) (α d : ℝ)
    (hrow : ∀ i, (∑ j, |gramMatrix v i j - (if i = j then α else 0)|) ≤ d)
    (a : ι → ℝ) :
    |‖Fintype.linearCombination ℝ v a‖ ^ 2 - α * ∑ i, a i ^ 2| ≤
      d * ∑ i, a i ^ 2 := by
  let D : Matrix ι ι ℝ := fun i j => gramMatrix v i j - (if i = j then α else 0)
  have hsym (i j : ι) : D i j = D j i := by
    by_cases h : i = j
    · subst j
      rfl
    · simp [D, gramMatrix, h, Ne.symm h, real_inner_comm]
  have hsum (i : ι) :
      (∑ j, D i j * a j) = (∑ j, gramMatrix v i j * a j) - α * a i := by
    simp [D, sub_mul, Finset.sum_sub_distrib, ite_mul]
  have hq : dotProduct a (D.mulVec a) =
      ‖Fintype.linearCombination ℝ v a‖ ^ 2 - α * ∑ i, a i ^ 2 := by
    rw [gramMatrix_quadratic]
    change (∑ i, a i * ∑ j, D i j * a j) =
      (∑ i, a i * ∑ j, gramMatrix v i j * a j) - α * ∑ i, a i ^ 2
    simp_rw [hsum, mul_sub, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [← hq]
  exact abs_quadratic_le_of_rowAbs D hsym d hrow a

/-- A quantitative energy sandwich from a comparison with a scalar diagonal. -/
theorem synthesis_energy_bounds_of_rowDefect (v : ι → H) (y : H)
    (hy : y ∈ synthesisSpan v) (α d : ℝ) (hd : 0 ≤ d) (hα : d < α)
    (hrow : ∀ i, (∑ j, |gramMatrix v i j - (if i = j then α else 0)|) ≤ d) :
    (∑ i, (cross v y i) ^ 2) / (α + d) ≤ ‖y‖ ^ 2 ∧
      ‖y‖ ^ 2 ≤ (∑ i, (cross v y i) ^ 2) / (α - d) := by
  let b := cross v y
  let S := ∑ i, b i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hαp : 0 < α + d := by linarith
  have hαm : 0 < α - d := sub_pos.mpr hα
  have hquad (c : ι → ℝ) :
      (α - d) * (∑ i, c i ^ 2) ≤ ‖Fintype.linearCombination ℝ v c‖ ^ 2 ∧
        ‖Fintype.linearCombination ℝ v c‖ ^ 2 ≤ (α + d) * (∑ i, c i ^ 2) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (synthesis_quadratic_sub_le_of_rowDefect v α d hrow c)
    constructor <;> linarith only [hlo, hhi]
  constructor
  · change S / (α + d) ≤ _
    let x := Fintype.linearCombination ℝ v b
    have hx : inner ℝ x y = S := by
      change inner ℝ (Fintype.linearCombination ℝ v b) y = S
      rw [inner_synthesis_left]
      exact Finset.sum_congr rfl (fun i _ => by simp [b, cross, pow_two])
    have hcs : S ≤ ‖x‖ * ‖y‖ := by
      simpa only [hx, Real.norm_eq_abs, abs_of_nonneg hS] using
        (norm_inner_le_norm (𝕜 := ℝ) x y)
    have hsq : S ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
      have h := mul_self_le_mul_self hS hcs
      nlinarith only [h]
    by_cases hs : S = 0
    · simp [hs]
    have hs' : 0 < S := lt_of_le_of_ne hS (Ne.symm hs)
    have hb := mul_le_mul_of_nonneg_right (hquad b).2 (sq_nonneg ‖y‖)
    change ‖x‖ ^ 2 * ‖y‖ ^ 2 ≤ _ at hb
    have hc : S * S ≤ S * ((α + d) * ‖y‖ ^ 2) := by
      nlinarith only [hsq.trans hb]
    exact (div_le_iff₀ hαp).2 (by
      rw [mul_comm]
      exact le_of_mul_le_mul_left hc hs')
  · change ‖y‖ ^ 2 ≤ S / (α - d)
    rw [synthesisSpan, ← Fintype.range_linearCombination] at hy
    obtain ⟨a, ha⟩ := hy
    have hyb : ‖y‖ ^ 2 = ∑ i, a i * b i := by
      rw [← real_inner_self_eq_norm_sq, ← ha, inner_synthesis_left, ha]
      rfl
    have hlo := (hquad a).1
    rw [ha] at hlo
    have hterm (i : ι) :
        2 * (a i * b i) ≤ (α - d) * a i ^ 2 + b i ^ 2 / (α - d) := by
      have hsq := sq_nonneg ((α - d) * a i - b i)
      have hh : 2 * (a i * b i) - (α - d) * a i ^ 2 ≤ b i ^ 2 / (α - d) :=
        (le_div_iff₀ hαm).mpr (by nlinarith only [hsq])
      linarith only [hh]
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← hyb] at hsum
    change 2 * ‖y‖ ^ 2 ≤ (α - d) * (∑ i, a i ^ 2) + S / (α - d) at hsum
    linarith only [hsum, hlo]

end RiemannResearch.Analysis.FiniteHilbertGram
