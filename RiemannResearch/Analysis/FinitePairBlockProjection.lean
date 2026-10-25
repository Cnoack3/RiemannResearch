/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Orthogonal projection onto common pair-difference constraints

Source: elementary weighted least-squares calculations developed in continuation
of the user's prime-square screening handoff of 25 October 2026.

The intended RH application groups odd pairs (j - 1, j) by their common radical.
This module proves the finite weighted projection identities and physical bounds.
It does not identify the infinite arithmetic projection or bound the subsequent
projection onto the actual legal squarefree stage.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FinitePairBlockProjection

variable {ι : Type*} [Fintype ι]

def weightedMean (w x : ι → ℝ) : ℝ := (∑ i, w i * x i) / (∑ i, w i)

theorem weightedMean_abs_le (w x : ι → ℝ) (M : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : 0 < ∑ i, w i) (hx : ∀ i, |x i| ≤ M) :
    |weightedMean w x| ≤ M := by
  unfold weightedMean
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  calc
    |∑ i, w i * x i| ≤ ∑ i, |w i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * M := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hw i)
    _ = M * ∑ i, w i := by rw [← Finset.sum_mul]; ring

theorem weightedMean_centered (w x : ι → ℝ) (hs : (∑ i, w i) ≠ 0) :
    ∑ i, w i * (x i - weightedMean w x) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold weightedMean
  field_simp [hs]
  ring

def pairMean (wp wm x y : ℝ) : ℝ := (wp * x + wm * y) / (wp + wm)
def pairPlus (wp wm x y c : ℝ) : ℝ := pairMean wp wm x y + wm / (wp + wm) * c
def pairMinus (wp wm x y c : ℝ) : ℝ := pairMean wp wm x y - wp / (wp + wm) * c
def harmonicWeight (wp wm : ℝ) : ℝ := wp * wm / (wp + wm)

theorem pair_difference (wp wm x y c : ℝ) (hs : wp + wm ≠ 0) :
    pairPlus wp wm x y c - pairMinus wp wm x y c = c := by
  unfold pairPlus pairMinus
  field_simp [hs]
  ring

theorem pair_weighted_mean_preserved (wp wm x y c : ℝ) (hs : wp + wm ≠ 0) :
    wp * pairPlus wp wm x y c + wm * pairMinus wp wm x y c = wp * x + wm * y := by
  unfold pairPlus pairMinus pairMean
  field_simp [hs]
  ring

theorem pair_residual_pairing (wp wm x y c u v : ℝ) (hs : wp + wm ≠ 0) :
    wp * (x - pairPlus wp wm x y c) * u +
      wm * (y - pairMinus wp wm x y c) * v =
      harmonicWeight wp wm * (x - y - c) * (u - v) := by
  unfold pairPlus pairMinus pairMean harmonicWeight
  field_simp [hs]
  ring

theorem pairMean_abs_le (wp wm x y M : ℝ)
    (hp : 0 ≤ wp) (hm : 0 ≤ wm) (hs : 0 < wp + wm)
    (hx : |x| ≤ M) (hy : |y| ≤ M) : |pairMean wp wm x y| ≤ M := by
  unfold pairMean
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  calc
    |wp * x + wm * y| ≤ |wp * x| + |wm * y| := abs_add_le _ _
    _ = wp * |x| + wm * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hm]
    _ ≤ wp * M + wm * M :=
      add_le_add (mul_le_mul_of_nonneg_left hx hp) (mul_le_mul_of_nonneg_left hy hm)
    _ = M * (wp + wm) := by ring

theorem pair_bound (wp wm x y c M A : ℝ)
    (hp : 0 ≤ wp) (hm : 0 ≤ wm) (hs : 0 < wp + wm)
    (hM : 0 ≤ M) (hx : |x| ≤ M) (hy : |y| ≤ M) (hc : |c| ≤ 2 * M)
    (ha : wm / (wp + wm) ≤ A) (hb : wp / (wp + wm) ≤ A) :
    |pairPlus wp wm x y c| ≤ (1 + 2 * A)*M ∧
      |pairMinus wp wm x y c| ≤ (1 + 2 * A)*M := by
  have hav : 0 ≤ wm / (wp + wm) := div_nonneg hm hs.le
  have hbv : 0 ≤ wp / (wp + wm) := div_nonneg hp hs.le
  have hmean := pairMean_abs_le wp wm x y M hp hm hs hx hy
  have hac : |wm / (wp + wm) * c| ≤ 2 * A*M := by
    rw [abs_mul, abs_of_nonneg hav]
    calc
      wm / (wp + wm) * |c| ≤ wm / (wp + wm) * (2 * M) := mul_le_mul_of_nonneg_left hc hav
      _ ≤ A * (2 * M) := mul_le_mul_of_nonneg_right ha (by positivity)
      _ = 2 * A*M := by ring
  have hbc : |wp / (wp + wm) * c| ≤ 2 * A*M := by
    rw [abs_mul, abs_of_nonneg hbv]
    calc
      wp / (wp + wm) * |c| ≤ wp / (wp + wm) * (2 * M) := mul_le_mul_of_nonneg_left hc hbv
      _ ≤ A * (2 * M) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 2 * A*M := by ring
  constructor
  · have h := abs_add_le (pairMean wp wm x y) (wm/(wp+wm)*c)
    unfold pairPlus
    nlinarith
  · have h : |pairMean wp wm x y - wp / (wp + wm) * c| ≤
        |pairMean wp wm x y| + |wp / (wp + wm) * c| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (pairMean wp wm x y) (-(wp / (wp + wm) * c)))
    unfold pairMinus
    nlinarith

theorem q_pair_ratios (j : ℝ) (hj : 3 ≤ j) :
    j^2 / (j^2 + (j-1)^2) ≤ 9/13 ∧
      (j-1)^2 / (j^2 + (j-1)^2) ≤ 9/13 := by
  have hjpos : 0 < j := by linarith
  have hd : 0 < j^2 + (j-1)^2 := by positivity
  have hprod : 0 ≤ (j-3)*(5*j-3) := mul_nonneg (by linarith) (by linarith)
  constructor
  · apply (div_le_iff₀ hd).2
    nlinarith
  · apply (div_le_iff₀ hd).2
    nlinarith


theorem pair_residual_norm (wp wm x y c : ℝ) (hs : wp + wm ≠ 0) :
    wp * (x - pairPlus wp wm x y c)^2 +
      wm * (y - pairMinus wp wm x y c)^2 =
      harmonicWeight wp wm * (x-y-c)^2 := by
  unfold pairPlus pairMinus pairMean harmonicWeight
  field_simp [hs]
  ring

def blockDifference (a b x y : ι → ℝ) : ℝ :=
  weightedMean (fun i => harmonicWeight (a i) (b i)) (fun i => x i - y i)

def blockPlus (a b x y : ι → ℝ) (i : ι) : ℝ :=
  pairPlus (a i) (b i) (x i) (y i) (blockDifference a b x y)

def blockMinus (a b x y : ι → ℝ) (i : ι) : ℝ :=
  pairMinus (a i) (b i) (x i) (y i) (blockDifference a b x y)

theorem block_common_difference (a b x y : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (i : ι) :
    blockPlus a b x y i - blockMinus a b x y i = blockDifference a b x y :=
  pair_difference _ _ _ _ _ (ne_of_gt (add_pos (ha i) (hb i)))

theorem block_mean_preserved (a b x y : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (i : ι) :
    a i * blockPlus a b x y i + b i * blockMinus a b x y i =
      a i * x i + b i * y i :=
  pair_weighted_mean_preserved _ _ _ _ _ (ne_of_gt (add_pos (ha i) (hb i)))

theorem block_residual_norm (a b x y : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∑ i, (a i * (x i - blockPlus a b x y i)^2 +
      b i * (y i - blockMinus a b x y i)^2)) =
      ∑ i, harmonicWeight (a i) (b i) * (x i-y i-blockDifference a b x y)^2 := by
  apply Finset.sum_congr rfl
  intro i _
  exact pair_residual_norm _ _ _ _ _ (ne_of_gt (add_pos (ha i) (hb i)))

variable [Nonempty ι]

theorem harmonic_sum_pos (a b : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) : 0 < ∑ i, harmonicWeight (a i) (b i) := by
  apply Finset.sum_pos
  · intro i _
    exact div_pos (mul_pos (ha i) (hb i)) (add_pos (ha i) (hb i))
  · exact Finset.univ_nonempty

theorem block_orthogonal (a b x y u v : ι → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hd : ∀ i, u i - v i = d) :
    (∑ i, (a i * (x i-blockPlus a b x y i) * u i +
      b i * (y i-blockMinus a b x y i) * v i)) = 0 := by
  have hs := harmonic_sum_pos a b ha hb
  calc
    _ = ∑ i, harmonicWeight (a i) (b i) *
        (x i-y i-blockDifference a b x y) * d := by
      apply Finset.sum_congr rfl
      intro i _
      unfold blockPlus blockMinus
      rw [pair_residual_pairing _ _ _ _ _ _ _ (ne_of_gt (add_pos (ha i) (hb i))), hd i]
    _ = (∑ i, harmonicWeight (a i) (b i) *
        (x i-y i-blockDifference a b x y)) * d := by rw [Finset.sum_mul]
    _ = 0 := by
      unfold blockDifference
      rw [weightedMean_centered _ _ (ne_of_gt hs), zero_mul]

theorem block_pythagorean (a b x y u v : ι → ℝ) (d : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hd : ∀ i, u i - v i = d) :
    (∑ i, (a i * (x i-u i)^2 + b i * (y i-v i)^2)) =
      (∑ i, (a i * (x i-blockPlus a b x y i)^2 +
        b i * (y i-blockMinus a b x y i)^2)) +
      (∑ i, (a i * (blockPlus a b x y i-u i)^2 +
        b i * (blockMinus a b x y i-v i)^2)) := by
  have hdiff : ∀ i,
      (blockPlus a b x y i-u i) - (blockMinus a b x y i-v i) =
        blockDifference a b x y-d := by
    intro i
    have h := block_common_difference a b x y ha hb i
    have hd' := hd i
    linarith
  have horth := block_orthogonal a b x y
    (fun i => blockPlus a b x y i-u i)
    (fun i => blockMinus a b x y i-v i)
    (blockDifference a b x y-d) ha hb hdiff
  calc
    _ = (∑ i, (a i * (x i-blockPlus a b x y i)^2 +
          b i * (y i-blockMinus a b x y i)^2)) +
        (∑ i, (a i * (blockPlus a b x y i-u i)^2 +
          b i * (blockMinus a b x y i-v i)^2)) +
        2 * (∑ i, (a i * (x i-blockPlus a b x y i) *
          (blockPlus a b x y i-u i) +
          b i * (y i-blockMinus a b x y i) *
          (blockMinus a b x y i-v i))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [horth]; ring

theorem blockDifference_abs_le (a b x y : ι → ℝ) (M : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hx : ∀ i, |x i| ≤ M) (hy : ∀ i, |y i| ≤ M) :
    |blockDifference a b x y| ≤ 2 * M := by
  apply weightedMean_abs_le
  · intro i
    unfold harmonicWeight
    exact le_of_lt (div_pos (mul_pos (ha i) (hb i)) (add_pos (ha i) (hb i)))
  · exact harmonic_sum_pos a b ha hb
  · intro i
    have h : |x i-y i| ≤ |x i|+|y i| := by
      simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le (x i) (-y i))
    linarith [hx i, hy i]

theorem block_sup_bound_of_ratios (a b x y : ι → ℝ) (M A : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hM : 0 ≤ M)
    (hx : ∀ i, |x i| ≤ M) (hy : ∀ i, |y i| ≤ M)
    (hba : ∀ i, b i / (a i + b i) ≤ A)
    (haa : ∀ i, a i / (a i + b i) ≤ A) (i : ι) :
    |blockPlus a b x y i| ≤ (1+2 * A)*M ∧
      |blockMinus a b x y i| ≤ (1+2 * A)*M := by
  have hc := blockDifference_abs_le a b x y M ha hb hx hy
  simpa only [blockPlus, blockMinus] using
    (pair_bound (a i) (b i) (x i) (y i) (blockDifference a b x y) M A
      (ha i).le (hb i).le (add_pos (ha i) (hb i)) hM
      (hx i) (hy i) hc (hba i) (haa i))

theorem inverseSquare_pair_identities (Z j : ℝ) (hZ : 0 < Z) (hj : 3 ≤ j) :
    (1/(Z*(j-1)^2)) / (1/(Z*j^2)+1/(Z*(j-1)^2)) =
        j^2/(j^2+(j-1)^2) ∧
      (1/(Z*j^2)) / (1/(Z*j^2)+1/(Z*(j-1)^2)) =
        (j-1)^2/(j^2+(j-1)^2) ∧
      harmonicWeight (1/(Z*j^2)) (1/(Z*(j-1)^2)) =
        1/(Z*(j^2+(j-1)^2)) := by
  have hjp : 0 < j := by linarith
  have hjm : 0 < j-1 := by linarith
  have hd : 0 < j^2+(j-1)^2 := by positivity
  have hs : 0 < 1/(Z*j^2)+1/(Z*(j-1)^2) := by positivity
  unfold harmonicWeight
  constructor
  · field_simp [ne_of_gt hZ, ne_of_gt hjp, ne_of_gt hjm, ne_of_gt hd, ne_of_gt hs]
    ring
  constructor
  · field_simp [ne_of_gt hZ, ne_of_gt hjp, ne_of_gt hjm, ne_of_gt hd, ne_of_gt hs]
    ring
  · field_simp [ne_of_gt hZ, ne_of_gt hjp, ne_of_gt hjm, ne_of_gt hd, ne_of_gt hs]
    ring

theorem inverseSquare_block_sup_bound (Z : ℝ) (j x y : ι → ℝ) (M : ℝ)
    (hZ : 0 < Z) (hj : ∀ i, 3 ≤ j i) (hM : 0 ≤ M)
    (hx : ∀ i, |x i| ≤ M) (hy : ∀ i, |y i| ≤ M) (i : ι) :
    |blockPlus (fun i => 1/(Z*(j i)^2)) (fun i => 1/(Z*(j i-1)^2)) x y i|
      ≤ (31/13)*M ∧
    |blockMinus (fun i => 1/(Z*(j i)^2)) (fun i => 1/(Z*(j i-1)^2)) x y i|
      ≤ (31/13)*M := by
  let a : ι → ℝ := fun i => 1/(Z*(j i)^2)
  let b : ι → ℝ := fun i => 1/(Z*(j i-1)^2)
  have ha : ∀ i, 0 < a i := by
    intro i
    have hji : 0 < j i := by linarith [hj i]
    dsimp [a]
    positivity
  have hb : ∀ i, 0 < b i := by
    intro i
    have hji : 0 < j i-1 := by linarith [hj i]
    dsimp [b]
    positivity
  have hba : ∀ i, b i / (a i + b i) ≤ 9/13 := by
    intro i
    dsimp [a, b]
    rw [(inverseSquare_pair_identities Z (j i) hZ (hj i)).1]
    exact (q_pair_ratios (j i) (hj i)).1
  have haa : ∀ i, a i / (a i + b i) ≤ 9/13 := by
    intro i
    dsimp [a, b]
    rw [(inverseSquare_pair_identities Z (j i) hZ (hj i)).2.1]
    exact (q_pair_ratios (j i) (hj i)).2
  have h := block_sup_bound_of_ratios a b x y M (9/13) ha hb hM hx hy hba haa i
  norm_num only at h
  exact h

end RiemannResearch.Analysis.FinitePairBlockProjection
