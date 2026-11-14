/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MertensWeightedEnergy
import RiemannResearch.LinearAlgebra.FiniteCumulativeSignedEnergy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith

/-!
# Complete signed Mertens-energy convergence

Source: the user's weighted-energy agenda, Sections 6-7, and the exact finite
identity in MertensWeightedEnergy. The proofs below pass to the limit without
discarding the signed cross term or its diagonal. Positive damping makes the
diagonal summable unconditionally. Finiteness of the total energy, and hence
convergence of the signed term, remains a conditional research reduction at
the small dampings needed for RH.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.MertensWeightedEnergy

open RiemannResearch.LinearAlgebra.CumulativeCellEnergy

/-- The complete diagonal is summable at every positive damping. -/
theorem summable_diagonal_integrand (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n => weight ε n *
      cumulative (fun i => mobiusCoefficients i^2) (n+1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (weight_pos ε n).le
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))) _ (diagonal_majorant_summable ε hε)
  intro n
  rw [← weight_mul_index]
  apply mul_le_mul_of_nonneg_left _ (weight_pos ε n).le
  calc
    _ ≤ ∑ _i ∈ Finset.range (n+1), (1:ℝ) :=
      Finset.sum_le_sum (fun i _ => mobiusCoefficients_sq_le_one i)
    _ = _ := by simp

/-- Exact signed limiting identity, with no removal of the diagonal. -/
theorem offDiagonal_tendsto_of_hasFiniteEnergy (ε : ℝ) (hε : 0 < ε)
    (hE : HasFiniteEnergy ε) :
    Tendsto (offDiagonal ε) atTop
      (𝓝 ((∑' n, weight ε n * mertensPrefix (n+1)^2) -
        ∑' n, weight ε n * cumulative (fun i => mobiusCoefficients i^2) (n+1))) := by
  have ht := hE.hasSum.tendsto_sum_nat
  have hd := (summable_diagonal_integrand ε hε).hasSum.tendsto_sum_nat
  convert ht.sub hd using 1
  funext N
  change offDiagonal ε N = finiteEnergy ε N - _
  have he := finiteEnergy_identity ε N
  rw [diagonal, diagonalEnergy_eq_weighted_square_prefix] at he
  linarith

/-- Bounded signed energy can be strengthened to actual convergence. -/
theorem hasFiniteEnergy_iff_offDiagonal_converges (ε : ℝ) (hε : 0 < ε) :
    HasFiniteEnergy ε ↔ ∃ L : ℝ, Tendsto (offDiagonal ε) atTop (𝓝 L) := by
  constructor
  · intro hE
    exact ⟨_, offDiagonal_tendsto_of_hasFiniteEnergy ε hε hE⟩
  · rintro ⟨L, hL⟩
    apply (hasFiniteEnergy_iff_frequently_bounded_offDiagonal ε hε).mpr
    refine ⟨L+1, ?_⟩
    exact ((hL.eventually (gt_mem_nhds (by linarith : L < L+1))).mono
      (fun N hN => hN.le)).frequently


#print axioms offDiagonal_tendsto_of_hasFiniteEnergy
#print axioms hasFiniteEnergy_iff_offDiagonal_converges
end RiemannResearch.RH.MertensWeightedEnergy
