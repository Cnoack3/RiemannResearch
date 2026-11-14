/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MertensWeightedEnergy
import RiemannResearch.LinearAlgebra.FiniteCumulativeSignedEnergy
import RiemannResearch.Analysis.DyadicWeightedContrast
import RiemannResearch.Analysis.DyadicBlockSummability
import RiemannResearch.Analysis.DyadicBlockDecomposition
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic Mertens energy with complete signed block accounting

Source: user-provided Mertens_Weighted_Energy_Weak_Star_Continuation (1).md
and agenda Steps 3 and 4 in Reciprocal_Residue_Density_and_Direct_RH_Agenda (1).tex.
The finite decomposition and dyadic comparisons are elementary exact algebra
and geometric summation. For background on the RH/Mertens relationship see
K. Soundararajan, Partial sums of the Mobius function, introduction,
https://arxiv.org/abs/0705.0723 . That reference is context, not a Lean provider.

Write H(X) = sum_{X < n <= 2X} M(n)^2. For each epsilon >= 0, finite
weighted energy is equivalent to summability of
(2^j)^(-2-2epsilon) H(2^j). Thus all positive weighted energies are finite
if and only if, for every delta > 0, H(2^j) <= C_delta (2^j)^(2+2delta)
uniformly in j. The reverse implication uses delta < epsilon.

The exact signed expansion retains X M(X)^2 and the interaction of M(X)
with the new block. CRT information about within-block terms alone does not
remove either contribution. The arithmetic bounds at losses approaching zero
remain Open. The RH implications are assembled in MertensEnergyRH.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.MertensWeightedEnergy
open RiemannResearch.LinearAlgebra.CumulativeCellEnergy
open RiemannResearch.Analysis.DyadicWeightedContrast
open RiemannResearch.Analysis.DyadicBlockDecomposition

/-- The complete block X < n ≤ 2X, with no subtraction of the inherited M(X). -/
def blockSquareSum (X : ℕ) : ℝ :=
  ∑ i ∈ Finset.range X, mertensPrefix (X+i+1)^2

/-- Unweighted block energy normalized at the exact damping exponent. -/
def dyadicNormalizedEnergy (ε : ℝ) (j : ℕ) : ℝ :=
  ((2^j : ℕ) : ℝ)^(-2-2*ε) * blockSquareSum (2^j)

theorem blockSquareSum_nonneg (X : ℕ) : 0 ≤ blockSquareSum X :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem dyadicNormalizedEnergy_nonneg (ε : ℝ) (j : ℕ) :
    0 ≤ dyadicNormalizedEnergy ε j :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (blockSquareSum_nonneg _)

/-- Exact finite regrouping, including the initial contribution M(1)^2 = 1. -/
theorem finiteEnergy_dyadic_identity (ε : ℝ) (J : ℕ) :
    finiteEnergy ε (2^J) =
      1 + ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range (2^j),
        weight ε (2^j+i) * mertensPrefix (2^j+i+1)^2 := by
  have h := dyadic_block_sum_eq
    (fun n => weight ε n * mertensPrefix (n+1)^2) J
  have hz : weight ε 0 * mertensPrefix 1 ^ 2 = 1 := by
    norm_num [weight, mertensPrefix, cumulative, mobiusCoefficients]
  change _ = finiteEnergy ε (2^J) - weight ε 0 * mertensPrefix 1 ^ 2 at h
  rw [hz] at h
  linarith

theorem weighted_block_le_normalized (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) :
    (∑ i ∈ Finset.range (2^j),
      weight ε (2^j+i) * mertensPrefix (2^j+i+1)^2) ≤
      dyadicNormalizedEnergy ε j := by
  unfold dyadicNormalizedEnergy blockSquareSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.rpow_le_rpow_of_nonpos
  · positivity
  · norm_num only [Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  · linarith

theorem normalized_le_weighted_block (ε : ℝ) (hε : 0 ≤ ε) (j : ℕ) :
    dyadicNormalizedEnergy ε j ≤
      (2:ℝ)^(2+2*ε) * (∑ i ∈ Finset.range (2^j),
        weight ε (2^j+i) * mertensPrefix (2^j+i+1)^2) := by
  let X : ℕ := 2^j
  have hX : (0:ℝ) < (X:ℝ) := by dsimp [X]; positivity
  have hc : (0:ℝ) < (2:ℝ)^(2+2*ε) := Real.rpow_pos_of_pos (by norm_num) _
  have hid : (2:ℝ)^(2+2*ε) * (2*(X:ℝ))^(-2-2*ε) =
      (X:ℝ)^(-2-2*ε) := by
    rw [Real.mul_rpow (by norm_num) hX.le, ← mul_assoc,
      ← Real.rpow_add (by norm_num)]
    norm_num
  unfold dyadicNormalizedEnergy blockSquareSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < X := Finset.mem_range.mp hi
  have hw : (2*(X:ℝ))^(-2-2*ε) ≤ weight ε (X+i) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · have hr : (i:ℝ)+1 ≤ X := by exact_mod_cast hi'
      norm_num only [Nat.cast_add]
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_left hw hc.le
  rw [hid] at hm
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm
    (sq_nonneg (mertensPrefix (X+i+1)))

/-- Exact summability criterion at a fixed nonnegative damping. -/
theorem hasFiniteEnergy_iff_summable_dyadic (ε : ℝ) (hε : 0 ≤ ε) :
    HasFiniteEnergy ε ↔ Summable (dyadicNormalizedEnergy ε) := by
  constructor
  · intro hE
    have hs := (summable_scaledDyadicBlock
      (fun n => weight ε n * mertensPrefix (n+1)^2) 1
      (fun n => mul_nonneg (weight_pos ε n).le (sq_nonneg _)) hE).mul_left
        ((2:ℝ)^(2+2*ε))
    apply Summable.of_nonneg_of_le (dyadicNormalizedEnergy_nonneg ε) _ hs
    intro j
    simpa only [scaledDyadicBlock, one_mul] using normalized_le_weighted_block ε hε j
  · intro hs
    exact summable_of_dyadic_block_majorant
      (fun n => weight ε n * mertensPrefix (n+1)^2)
      (dyadicNormalizedEnergy ε)
      (fun n => mul_nonneg (weight_pos ε n).le (sq_nonneg _))
      (dyadicNormalizedEnergy_nonneg ε) hs (weighted_block_le_normalized ε hε)

theorem dyadicNormalizedEnergy_le_geometric
    (ε δ C : ℝ) (hblock : ∀ j : ℕ, blockSquareSum (2^j) ≤
      C * ((2^j : ℕ) : ℝ)^(2+2*δ)) (j : ℕ) :
    dyadicNormalizedEnergy ε j ≤ C * ((2:ℝ)^(2*δ-2*ε))^j := by
  have hx : (0:ℝ) < ((2^j : ℕ) : ℝ) := by positivity
  calc
    _ ≤ ((2^j : ℕ) : ℝ)^(-2-2*ε) *
        (C * ((2^j : ℕ) : ℝ)^(2+2*δ)) :=
      mul_le_mul_of_nonneg_left (hblock j) (Real.rpow_nonneg hx.le _)
    _ = C * ((2^j : ℕ) : ℝ)^(2*δ-2*ε) := by
      rw [mul_left_comm, ← Real.rpow_add hx]
      congr 2
      ring
    _ = _ := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      rw [mul_comm (j:ℝ), Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- A strict exponent margin supplies a summable geometric block majorant. -/
theorem hasFiniteEnergy_of_dyadic_block_bound
    (ε δ C : ℝ) (hε : 0 ≤ ε) (hδε : δ < ε)
    (hblock : ∀ j : ℕ, blockSquareSum (2^j) ≤
      C * ((2^j : ℕ) : ℝ)^(2+2*δ)) : HasFiniteEnergy ε := by
  apply (hasFiniteEnergy_iff_summable_dyadic ε hε).mpr
  have hs := (summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (2*δ-2*ε))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2)
      (by linarith : 2*δ-2*ε < 0))).mul_left C
  exact Summable.of_nonneg_of_le (dyadicNormalizedEnergy_nonneg ε)
    (dyadicNormalizedEnergy_le_geometric ε δ C hblock) hs


theorem blockSquareSum_eq_scaledNormalized (ε : ℝ) (j : ℕ) :
    blockSquareSum (2^j) =
      ((2^j : ℕ) : ℝ)^(2+2*ε) * dyadicNormalizedEnergy ε j := by
  unfold dyadicNormalizedEnergy
  rw [← mul_assoc, ← Real.rpow_add (by positivity)]
  simp

theorem dyadic_block_bound_of_hasFiniteEnergy (ε : ℝ) (hε : 0 ≤ ε)
    (hE : HasFiniteEnergy ε) :
    ∃ C : ℝ, ∀ j : ℕ, blockSquareSum (2^j) ≤
      C * ((2^j : ℕ) : ℝ)^(2+2*ε) := by
  have hs := (hasFiniteEnergy_iff_summable_dyadic ε hε).mp hE
  refine ⟨∑' j, dyadicNormalizedEnergy ε j, fun j => ?_⟩
  have ht : dyadicNormalizedEnergy ε j ≤ ∑' k, dyadicNormalizedEnergy ε k := by
    simpa only [Finset.sum_singleton] using
      hs.sum_le_tsum {j} (fun k _ => dyadicNormalizedEnergy_nonneg ε k)
  have hx : (0:ℝ) < ((2^j : ℕ) : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left ht
    (Real.rpow_nonneg hx.le (2+2*ε))
  have he := (blockSquareSum_eq_scaledNormalized ε j).symm
  rw [he, mul_comm] at hm
  exact hm

/-- The all-positive-damping energy premise is equivalent to dyadic mean-square bounds with every positive exponent loss. This equivalence supplies no arithmetic bound. -/
theorem energy_forall_iff_dyadic_block_bounds :
    (∀ ε : ℝ, 0 < ε → HasFiniteEnergy ε) ↔
      ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ j : ℕ,
        blockSquareSum (2^j) ≤ C * ((2^j : ℕ) : ℝ)^(2+2*δ) := by
  constructor
  · intro h δ hδ
    exact dyadic_block_bound_of_hasFiniteEnergy δ hδ.le (h δ hδ)
  · intro h ε hε
    obtain ⟨C, hC⟩ := h (ε/2) (by linarith)
    exact hasFiniteEnergy_of_dyadic_block_bound ε (ε/2) C hε.le (by linarith) hC

/-- Finite energy forces normalized complete blocks to vanish. -/
theorem dyadicNormalizedEnergy_tendsto_zero (ε : ℝ) (hε : 0 ≤ ε)
    (hE : HasFiniteEnergy ε) :
    Tendsto (dyadicNormalizedEnergy ε) atTop (𝓝 0) :=
  ((hasFiniteEnergy_iff_summable_dyadic ε hε).mp hE).tendsto_atTop_zero

/-- The nonnegative within-block diagonal, with complete triangular weights. -/
def blockDiagonal (X : ℕ) : ℝ :=
  diagonalEnergy (fun _ => 1) (fun i => mobiusCoefficients (X+i)) X

/-- Both signed contributions: the interaction with M(X) and the full within-block upper triangle. -/
def signedBlockCross (X : ℕ) : ℝ :=
  2 * mertensPrefix X *
    (∑ j ∈ Finset.range X, mobiusCoefficients (X+j) * ((X:ℝ)-(j:ℝ))) +
  2 * ∑ j ∈ Finset.range X, ∑ i ∈ Finset.range j,
    mobiusCoefficients (X+i) * mobiusCoefficients (X+j) * ((X:ℝ)-(j:ℝ))

theorem blockDiagonal_eq (X : ℕ) :
    blockDiagonal X =
      ∑ j ∈ Finset.range X, mobiusCoefficients (X+j)^2 * ((X:ℝ)-(j:ℝ)) := by
  simp [blockDiagonal, diagonalEnergy, tailWeight, cumulative]

/-- Exact shifted Mobius identity, retaining the inherited head square, its signed interaction, the diagonal, and every off-diagonal pair. -/
theorem blockSquareSum_signed_identity (X : ℕ) :
    blockSquareSum X =
      (X:ℝ) * mertensPrefix X^2 + blockDiagonal X + signedBlockCross X := by
  have h := shifted_weightedPrefixEnergy_identity (fun _ => 1) mobiusCoefficients X X
  have ht (j : ℕ) : tailWeight (fun _ => 1) X j = (X:ℝ)-(j:ℝ) := by
    simp [tailWeight, cumulative]
  have hc : cumulative (fun _ : ℕ => (1:ℝ)) X = (X:ℝ) := by simp [cumulative]
  simp only [one_mul, hc, offDiagonalEnergy_eq_pair_sum, ht] at h
  change blockSquareSum X = mertensPrefix X^2 * (X:ℝ) +
    2 * mertensPrefix X * _ + blockDiagonal X + _ at h
  unfold signedBlockCross
  rw [h]
  ring

theorem blockDiagonal_nonneg (X : ℕ) : 0 ≤ blockDiagonal X :=
  diagonalEnergy_nonneg _ _ (by intro n; norm_num) X

theorem blockDiagonal_le_sq (X : ℕ) : blockDiagonal X ≤ (X:ℝ)^2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range X, ((i+1:ℕ):ℝ) := by
      simpa only [blockDiagonal, one_mul] using
        diagonalEnergy_le_linear_weight (fun _ => 1)
          (fun i => mobiusCoefficients (X+i)) (by intro n; norm_num)
          (fun i => mobiusCoefficients_sq_le_one (X+i)) X
    _ ≤ ∑ _i ∈ Finset.range X, (X:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact_mod_cast (Finset.mem_range.mp hi)
    _ = _ := by simp [pow_two]

/-- The diagonal costs at most X^2. The remaining signed criterion must still include X * M(X)^2. -/
theorem dyadic_block_bounds_iff_signed_cancellation :
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ j : ℕ,
      blockSquareSum (2^j) ≤ C * ((2^j : ℕ) : ℝ)^(2+2*δ)) ↔
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ j : ℕ,
      ((2^j : ℕ) : ℝ) * mertensPrefix (2^j)^2 + signedBlockCross (2^j) ≤
        C * ((2^j : ℕ) : ℝ)^(2+2*δ)) := by
  constructor
  · intro h δ hδ
    obtain ⟨C, hC⟩ := h δ hδ
    refine ⟨C, fun j => ?_⟩
    have hid := blockSquareSum_signed_identity (2^j)
    linarith [hC j, blockDiagonal_nonneg (2^j)]
  · intro h δ hδ
    obtain ⟨C, hC⟩ := h δ hδ
    refine ⟨C+1, fun j => ?_⟩
    have hp : (((2^j : ℕ) : ℝ))^2 ≤ ((2^j : ℕ) : ℝ)^(2+2*δ) := by
      rw [← Real.rpow_two]
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2:ℕ)))
      · linarith
    have hd := (blockDiagonal_le_sq (2^j)).trans hp
    have hid := blockSquareSum_signed_identity (2^j)
    nlinarith [hC j]

end RiemannResearch.RH.MertensWeightedEnergy
