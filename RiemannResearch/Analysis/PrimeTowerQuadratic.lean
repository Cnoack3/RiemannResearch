/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ZeroSamplingQuadratic
import RiemannResearch.Analysis.GrowingPhaseCovarianceAssembly
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Exact finite prime-tower corrections, boundaries, and cancellation

Source: user-provided signed prime-power correction. The row sums, finite
boundaries, and cancellation examples are independently derived algebraic
refinements; no novelty claim is made. The geometric kernel is the
Kac--Murdock--Szego matrix (terminology and spectral context:
https://arxiv.org/pdf/1804.08140). Its general spectral theory is not
formalized here. All analytic phase laws remain external to this module.

Indices are zero based. signedCorrection uses ordered pairs, and
signedCorrection_eq_full_boundary retains half the ordered difference
energy and both finite endpoint terms. The five-coordinate kernel result
concerns that finite compression, not the infinite tower.
-/

noncomputable section


namespace RiemannResearch.Fourier
theorem primePowerCovarianceSignedEntry_prime_pow
    (p k l : ℕ) (hp : p.Prime) (hkl : k < l) :
    primePowerCovarianceSignedEntry (p ^ k) (p ^ l) =
      (((-1 / (2 * Real.pi)) *
        (Real.log p / Real.sqrt (p ^ (l - k) : ℕ)) : ℝ) : ℂ) := by
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  have hlt : p ^ k < p ^ l := Nat.pow_lt_pow_right hp.one_lt hkl
  rw [primePowerCovarianceSignedEntry,
    primePowerCovarianceSymmetricEntry_eq_of_lt_of_dvd
      (p ^ k) (p ^ l) hpos hlt (Nat.pow_dvd_pow p hkl.le),
    Nat.pow_div hkl.le hp.pos,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.sub_ne_zero_of_lt hkl),
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  push_cast
  rfl
end RiemannResearch.Fourier

namespace RiemannResearch.Analysis.PrimeTowerQuadratic

open scoped BigOperators

def geometricTail (r : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.range n, r ^ (d + 1)

def offDiagonalRow (r : ℝ) (K k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, if j = k then 0 else r ^ ((k - j) + (j - k))

theorem geometricTail_eq (r : ℝ) (n : ℕ) (hr : r ≠ 1) :
    geometricTail r n = r * (1 - r ^ n) / (1 - r) := by
  have hden : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have hs : geometricTail r n = r * ∑ d ∈ Finset.range n, r ^ d := by
    unfold geometricTail
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [pow_succ]
    ring
  apply (eq_div_iff hden).mpr
  rw [hs]
  calc
    (r * ∑ d ∈ Finset.range n, r ^ d) * (1 - r) =
        r * ((1 - r) * ∑ d ∈ Finset.range n, r ^ d) := by ring
    _ = r * (1 - r ^ n) := by rw [mul_neg_geom_sum]

/-- Exact reindexing: the two sides of row k have lengths k and K-1-k. -/
theorem offDiagonalRow_eq_two_tails (r : ℝ) (K k : ℕ) (hk : k < K) :
    offDiagonalRow r K k = geometricTail r k + geometricTail r (K - 1 - k) := by
  have hk1 : k + 1 ≤ K := by omega
  have hl :
      (∑ j ∈ Finset.range k, if j = k then 0 else r ^ ((k - j) + (j - k))) =
        geometricTail r k := by
    unfold geometricTail
    calc
      (∑ j ∈ Finset.range k, if j = k then 0 else r ^ ((k - j) + (j - k))) =
          ∑ j ∈ Finset.range k, r ^ ((k - 1 - j) + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hjne : j ≠ k := by omega
        rw [if_neg hjne]
        congr 1
        omega
      _ = ∑ j ∈ Finset.range k, r ^ (j + 1) :=
        Finset.sum_range_reflect (fun j : ℕ => r ^ (j + 1)) k
  have hu :
      (∑ j ∈ Finset.Ico (k + 1) K, if j = k then 0 else r ^ ((k - j) + (j - k))) =
        geometricTail r (K - 1 - k) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hend : K - (k + 1) = K - 1 - k := by omega
    rw [hend]
    unfold geometricTail
    apply Finset.sum_congr rfl
    intro d hd
    have hdne : k + 1 + d ≠ k := by omega
    rw [if_neg hdne]
    congr 1
    omega
  unfold offDiagonalRow
  calc
    (∑ j ∈ Finset.range K, if j = k then 0 else r ^ ((k - j) + (j - k))) =
        (∑ j ∈ Finset.range (k + 1), if j = k then 0 else r ^ ((k - j) + (j - k))) +
        (∑ j ∈ Finset.Ico (k + 1) K, if j = k then 0 else r ^ ((k - j) + (j - k))) :=
      (Finset.sum_range_add_sum_Ico
        (fun j : ℕ => if j = k then 0 else r ^ ((k - j) + (j - k))) hk1).symm
    _ = geometricTail r k + geometricTail r (K - 1 - k) := by
      rw [Finset.sum_range_succ, hl, hu]
      simp

theorem offDiagonalRow_eq_boundary (r : ℝ) (K k : ℕ)
    (hk : k < K) (hr : r ≠ 1) :
    offDiagonalRow r K k =
      r / (1 - r) * (2 - r ^ k - r ^ (K - 1 - k)) := by
  rw [offDiagonalRow_eq_two_tails r K k hk,
    geometricTail_eq r k hr, geometricTail_eq r (K - 1 - k) hr]
  ring

def rowDiagonal (r : ℝ) (K : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range K, offDiagonalRow r K k * Complex.normSq (a k)

/-- Both finite boundaries survive exactly; no positivity or limiting argument is used. -/
theorem rowDiagonal_eq_bulk_sub_boundary (r : ℝ) (K : ℕ) (a : ℕ → ℂ)
    (hr : r ≠ 1) :
    rowDiagonal r K a =
      (2 * r / (1 - r)) * (∑ k ∈ Finset.range K, Complex.normSq (a k)) -
      (r / (1 - r)) *
        (∑ k ∈ Finset.range K,
          (r ^ k + r ^ (K - 1 - k)) * Complex.normSq (a k)) := by
  unfold rowDiagonal
  calc
    (∑ k ∈ Finset.range K, offDiagonalRow r K k * Complex.normSq (a k)) =
        ∑ k ∈ Finset.range K,
          ((2 * r / (1 - r)) * Complex.normSq (a k) -
            (r / (1 - r)) *
              ((r ^ k + r ^ (K - 1 - k)) * Complex.normSq (a k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [offDiagonalRow_eq_boundary r K k (Finset.mem_range.mp hk) hr]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end RiemannResearch.Analysis.PrimeTowerQuadratic


namespace RiemannResearch.Analysis.PrimeTowerQuadratic
open RiemannResearch.Analysis.ZeroSamplingQuadratic
def towerWeight (r : ℝ) (k j : ℕ) : ℝ :=
  if j = k then 0 else r ^ ((k - j) + (j - k))
def signedCorrection (c r : ℝ) (K : ℕ) (a : ℕ → ℂ) : ℝ :=
  -c * ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
    towerWeight r k j * (a k * star (a j)).re
def towerDifferenceEnergy (r : ℝ) (K : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
    towerWeight r k j * ‖a k - a j‖ ^ 2

theorem signedCorrection_eq_graph (c r : ℝ) (K : ℕ) (a : ℕ → ℂ) :
    signedCorrection c r K a =
      c * ((1 / 2 : ℝ) * towerDifferenceEnergy r K a - rowDiagonal r K a) := by
  have hs (k j : ℕ) : towerWeight r k j = towerWeight r j k := by
    simp only [towerWeight, eq_comm, add_comm]
  have hp (k j : ℕ) :
      towerWeight r k j * ‖a k - a j‖ ^ 2 =
        towerWeight r k j * ‖a k‖ ^ 2 +
        towerWeight r k j * ‖a j‖ ^ 2 -
        2 * (towerWeight r k j * (a k * star (a j)).re) := by
    have he := edge_identity (a k) (a j)
    linear_combination towerWeight r k j * he
  have h : towerDifferenceEnergy r K a =
      (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
        towerWeight r k j * ‖a k‖ ^ 2) +
      (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
        towerWeight r k j * ‖a j‖ ^ 2) -
      2 * (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
        towerWeight r k j * (a k * star (a j)).re) := by
    unfold towerDifferenceEnergy
    simp_rw [hp]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hr :
      (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
        towerWeight r k j * ‖a k‖ ^ 2) = rowDiagonal r K a := by
    simp only [rowDiagonal, offDiagonalRow, ← Finset.sum_mul,
      towerWeight, Complex.sq_norm]
  have hc :
      (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
        towerWeight r k j * ‖a j‖ ^ 2) = rowDiagonal r K a := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range K,
          towerWeight r k j * ‖a k‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro j hj
        rw [hs j k]
      _ = _ := hr
  rw [hr, hc] at h
  unfold signedCorrection towerDifferenceEnergy
  dsimp only [towerDifferenceEnergy] at h
  linear_combination -(c / 2) * h

theorem signedCorrection_eq_full_boundary (c r : ℝ) (K : ℕ) (a : ℕ → ℂ)
    (hr : r ≠ 1) :
    signedCorrection c r K a =
      c * ((1 / 2 : ℝ) * towerDifferenceEnergy r K a -
        (2 * r / (1 - r)) * (∑ k ∈ Finset.range K, Complex.normSq (a k)) +
        (r / (1 - r)) * (∑ k ∈ Finset.range K,
          (r ^ k + r ^ (K - 1 - k)) * Complex.normSq (a k))) := by
  rw [signedCorrection_eq_graph, rowDiagonal_eq_bulk_sub_boundary r K a hr]
  ring
end RiemannResearch.Analysis.PrimeTowerQuadratic

namespace RiemannResearch.Analysis.PrimeTowerQuadratic

open scoped BigOperators

def fiveTowerCoeff (r : ℝ) (i : Fin 5) : ℝ :=
  if i.val = 0 then 1
  else if i.val = 1 then r
  else if i.val = 3 then -r
  else if i.val = 4 then -1
  else 0

def towerKernel (r : ℝ) (i j : Fin 5) : ℝ :=
  r ^ ((i.val - j.val) + (j.val - i.val))

theorem fiveTower_kernel_fixed (r : ℝ) (hr : 2 * r ^ 2 = 1) (i : Fin 5) :
    (∑ j : Fin 5, towerKernel r i j * fiveTowerCoeff r j) = fiveTowerCoeff r i := by
  have hr2 : r ^ 2 = (1 / 2 : ℝ) := by linarith
  have hr3 : r ^ 3 = r / 2 := by
    calc
      r ^ 3 = r * r ^ 2 := by ring
      _ = r * (1 / 2 : ℝ) := by rw [hr2]
      _ = r / 2 := by ring
  have hr4 : r ^ 4 = (1 / 4 : ℝ) := by
    calc
      r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = ((1 / 2 : ℝ)) ^ 2 := by rw [hr2]
      _ = (1 / 4 : ℝ) := by norm_num
  fin_cases i <;>
    norm_num [towerKernel, fiveTowerCoeff, Fin.sum_univ_succ] <;>
    nlinarith [hr2, hr3, hr4]

/-- The fixed vector is nonzero; its first coordinate is exactly one. -/
theorem fiveTowerCoeff_nonzero (r : ℝ) : ∃ i : Fin 5, fiveTowerCoeff r i ≠ 0 := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  norm_num [fiveTowerCoeff]

/-- Exact quadratic equality, obtained from the stronger coordinatewise kernel theorem. -/
theorem fiveTower_quadratic_eq_norm (r : ℝ) (hr : 2 * r ^ 2 = 1) :
    (∑ i : Fin 5, fiveTowerCoeff r i *
      (∑ j : Fin 5, towerKernel r i j * fiveTowerCoeff r j)) =
      ∑ i : Fin 5, (fiveTowerCoeff r i) ^ 2 := by
  simp_rw [fiveTower_kernel_fixed r hr]
  simp only [pow_two]

/-- The corresponding signed correction is zero for every scalar prefactor. -/
theorem fiveTower_signed_correction_zero (c r : ℝ) (hr : 2 * r ^ 2 = 1) :
    c * ((∑ i : Fin 5, (fiveTowerCoeff r i) ^ 2) -
      (∑ i : Fin 5, fiveTowerCoeff r i *
        (∑ j : Fin 5, towerKernel r i j * fiveTowerCoeff r j))) = 0 := by
  rw [fiveTower_quadratic_eq_norm r hr]
  ring

end RiemannResearch.Analysis.PrimeTowerQuadratic

namespace RiemannResearch.Analysis.PrimeTowerQuadratic
theorem fiveTower_two_fixed (i : Fin 5) :
    (∑ j : Fin 5, towerKernel (1 / Real.sqrt 2) i j *
      fiveTowerCoeff (1 / Real.sqrt 2) j) =
      fiveTowerCoeff (1 / Real.sqrt 2) i := by
  apply fiveTower_kernel_fixed
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
end RiemannResearch.Analysis.PrimeTowerQuadratic

namespace RiemannResearch.Analysis.PrimeTowerQuadratic
theorem fiveTower_normSq (r : ℝ) (hr : 2 * r ^ 2 = 1) :
    (∑ i : Fin 5, (fiveTowerCoeff r i) ^ 2) = 3 := by
  norm_num [fiveTowerCoeff, Fin.sum_univ_succ]
  nlinarith [hr]
end RiemannResearch.Analysis.PrimeTowerQuadratic


namespace RiemannResearch.Analysis.PrimeTowerQuadratic
def threeTowerCoeff (r : ℝ) (i : Fin 3) : ℝ :=
  if i.val = 1 then -r / 2 else 1
theorem threeTower_signed_correction_zero (c r : ℝ) :
    c * ((∑ i : Fin 3, (threeTowerCoeff r i) ^ 2) -
      (∑ i : Fin 3, threeTowerCoeff r i *
        (∑ j : Fin 3, r ^ ((i.val - j.val) + (j.val - i.val)) *
          threeTowerCoeff r j))) = 0 := by
  rw [mul_eq_zero]
  right
  norm_num [threeTowerCoeff, Fin.sum_univ_succ]
  ring
theorem threeTower_normSq (r : ℝ) :
    (∑ i : Fin 3, (threeTowerCoeff r i) ^ 2) = 2 + r ^ 2 / 4 := by
  norm_num [threeTowerCoeff, Fin.sum_univ_succ]
  ring
end RiemannResearch.Analysis.PrimeTowerQuadratic
