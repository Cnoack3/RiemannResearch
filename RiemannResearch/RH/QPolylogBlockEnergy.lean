/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DyadicBlockSummability
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete logarithmic energy from physical block means

Source: SquarefreeShortHeadSchurResearch20261030.md, section 6.
These estimates apply to every Q-Hilbert vector. Dyadic unweighted mean-square
bounds supply complete summable logarithmic energy without a pointwise envelope.
The concrete consumer is QSquarefreeDyadicMeanSquare.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QPolylogTailEnergy
open ZetaTwoHilbert ZetaTwoProbability QAnnihilatorTailEscape
open RiemannResearch.Analysis.LogTailWeights
open RiemannResearch.Analysis.DyadicWeightedContrast

theorem polylogWeightedEnergyTerm_le_block_factor (u : QHilbert)
    (m M n : ℕ) (hM : 0 < M) (hMn : M ≤ n) :
    polylogWeightedEnergyTerm (2 * m + 2) u n ≤
      (1 / (zetaTwo * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * m + 2))) *
        qSequence u n ^ 2 := by
  have hz := zetaTwo_pos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hn : 0 < n := lt_of_lt_of_le hM hMn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMnR : (M : ℝ) ≤ n := by exact_mod_cast hMn
  have hlog : Real.log (M : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hMR hMnR
  have hL : 0 < 6 + Real.log (M : ℝ) := by linarith [Real.log_nonneg hM1]
  have hpow : (6 + Real.log (M : ℝ)) ^ (2 * m + 2) ≤
      (((2 * m + 2 : ℕ) : ℝ) + 6 + Real.log (n : ℝ)) ^ (2 * m + 2) := by
    apply pow_le_pow_left₀ hL.le
    linarith [Nat.cast_nonneg (α := ℝ) (2 * m + 2)]
  have hden : zetaTwo * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * m + 2) ≤
      zetaTwo * (n : ℝ) * (((2 * m + 2 : ℕ) : ℝ) + 6 + Real.log (n : ℝ)) ^ (2 * m + 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hMnR zetaTwo_pos.le) hpow
      (pow_nonneg hL.le _) (mul_nonneg zetaTwo_pos.le hnR.le)
  rw [polylogWeightedEnergyTerm_eq (2 * m + 2) n u hn]
  calc
    _ ≤ qSequence u n ^ 2 /
        (zetaTwo * (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (2 * m + 2)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
    _ = _ := by ring

/-- An unweighted mean-square envelope on dyadic physical blocks yields a
summable logarithmic weighted energy. No pointwise envelope is assumed. -/
theorem weightedEnergy_summable_of_dyadic_meanSquare
    (u : QHilbert) (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hblock : ∀ j : ℕ,
      (∑ i ∈ Finset.range (2 ^ j), qSequence u (2 ^ j + i + 1) ^ 2) ≤
        C * ((2 ^ j : ℕ) : ℝ) * (6 + Real.log ((2 ^ j : ℕ) : ℝ)) ^ (2 * m)) :
    Summable (polylogWeightedEnergyTerm (2 * m + 2) u) := by
  have hz := zetaTwo_pos
  let c : ℝ := min 6 (Real.log 2)
  have hc : 0 < c := lt_min (by norm_num) (Real.log_pos (by norm_num))
  let a : ℕ → ℝ := fun n => polylogWeightedEnergyTerm (2 * m + 2) u (n + 1)
  let b : ℕ → ℝ := fun j => (C / (zetaTwo * c ^ 2)) *
    (1 / ((j + 1 : ℕ) : ℝ) ^ 2)
  have ha : ∀ n, 0 ≤ a n := fun n => polylogWeightedEnergyTerm_nonneg _ _ _
  have hb : ∀ j, 0 ≤ b j := by intro j; dsimp [b]; positivity
  have hs0 : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hs : Summable b := hs0.mul_left (C / (zetaTwo * c ^ 2))
  have hmajor (j : ℕ) : (∑ i ∈ Finset.range (2 ^ j), a (2 ^ j + i)) ≤ b j := by
    let M : ℕ := 2 ^ j
    let L : ℝ := 6 + Real.log (M : ℝ)
    have hM : 0 < M := pow_pos (by norm_num) j
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hM1]
    have hfactor : 0 ≤ 1 / (zetaTwo * (M : ℝ) * L ^ (2 * m + 2)) := by positivity
    have hfinite : (∑ i ∈ Finset.range M,
        polylogWeightedEnergyTerm (2 * m + 2) u (M + i + 1)) ≤
        C / (zetaTwo * L ^ 2) := by
      calc
        _ ≤ ∑ i ∈ Finset.range M,
            (1 / (zetaTwo * (M : ℝ) * L ^ (2 * m + 2))) * qSequence u (M + i + 1) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          exact polylogWeightedEnergyTerm_le_block_factor u m M (M + i + 1) hM (by omega)
        _ = (1 / (zetaTwo * (M : ℝ) * L ^ (2 * m + 2))) *
            (∑ i ∈ Finset.range M, qSequence u (M + i + 1) ^ 2) := by rw [Finset.mul_sum]
        _ ≤ (1 / (zetaTwo * (M : ℝ) * L ^ (2 * m + 2))) *
            (C * (M : ℝ) * L ^ (2 * m)) :=
          mul_le_mul_of_nonneg_left (hblock j) hfactor
        _ = _ := by
          rw [pow_add]
          field_simp [zetaTwo_pos.ne', hMR.ne', hL.ne']
    have heL : L = 6 + (j : ℝ) * Real.log 2 := by
      dsimp [L, M]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hlinear : c * ((j + 1 : ℕ) : ℝ) ≤ L := by
      have h6 : c ≤ 6 := min_le_left _ _
      have h2 : c ≤ Real.log 2 := min_le_right _ _
      have hm := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) j)
      rw [heL]
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hsq := mul_self_le_mul_self
      (mul_nonneg hc.le (Nat.cast_nonneg (j + 1))) hlinear
    have hden : zetaTwo * c ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 2 ≤ zetaTwo * L ^ 2 := by
      have hz := mul_le_mul_of_nonneg_left hsq zetaTwo_pos.le
      nlinarith
    change (∑ i ∈ Finset.range M,
      polylogWeightedEnergyTerm (2 * m + 2) u (M + i + 1)) ≤ b j
    apply hfinite.trans
    calc
      C / (zetaTwo * L ^ 2) ≤ C / (zetaTwo * c ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left hC (by positivity) hden
      _ = b j := by dsimp [b]; ring
  have hsa : Summable a := summable_of_dyadic_block_majorant a b ha hb hs hmajor
  exact (summable_nat_add_iff 1).mp hsa

end RiemannResearch.RH.QPolylogTailEnergy
