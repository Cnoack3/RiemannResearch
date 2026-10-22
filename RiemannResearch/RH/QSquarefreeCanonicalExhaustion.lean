/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreeCanonicalCoordinates
import RiemannResearch.RH.CanonicalResidualGramMinimum
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Exhaustive legal canonical heads in Q and a prime-only obstruction

Source: independently developed in the user's sparse-power-cost program,
17 October 2026. The checked Pareto support elimination is transferred by
equality of complete physical sequences, so no Q tail or signed coefficient
is changed. Every finite squarefree-legal exact-head vector is a finite
affine combination of legal canonical heads beyond that positive head.

The squarefree anchor 6 is a concrete legal candidate missing from the
linear span of all prime-anchor canonical heads. This is an algebraic
obstruction to prime-only exhaustion, not a lower bound on its optimal
asymptotic cost and not a refutation of prime-only sparse power costs.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QSquarefreeCanonicalExhaustion
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto
open Pareto.CoefficientStabilization
theorem exists_affine_expansion (H : ℕ) (hH : 0 < H) (f : QHilbert)
    (hf : f ∈ qSquarefreeCRTSpan)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    ∃ M, H ≤ M ∧ ∃ c : Fin (M - H + 1) → ℝ, (∑ i, c i) = 1 ∧
      (∀ i, ¬Squarefree (H + i.val + 1) → c i = 0) ∧
      f = ∑ i, c i • QMobiusExactHead.exactHead (H + i.val) := by
  have hsf : toPareto f ∈ squarefreeCRTSpan := by
    rw [← qSquarefreeCRTSpan_map]
    exact ⟨f, hf, rfl⟩
  obtain ⟨M, hHM, hfin⟩ := exists_finiteSpace_of_squarefree H hsf
  obtain ⟨c, hc, hmask, he⟩ := exists_squarefree_canonical_affine_expansion
    H M hH hHM (toPareto f) hfin hsf
    (by intro n hn hnH; rw [toPareto_sequence]; exact hh n hn hnH)
  refine ⟨M, hHM, c, hc, hmask, ?_⟩
  apply qSequence_injective
  have hp : toPareto f =
      toParetoLinear (∑ i, c i • QMobiusExactHead.exactHead (H + i.val)) := by
    rw [map_sum]
    simp only [map_smul]
    have hcanon (Y : ℕ) : toParetoLinear (QMobiusExactHead.exactHead Y) =
        canonicalMobiusHilbert Y := QSquarefreeSublinearHeads.toPareto_exactHead Y
    simpa only [hcanon] using he
  have hseq := congrArg hilbertSequence hp
  change hilbertSequence (toPareto f) =
    hilbertSequence (toPareto (∑ i, c i • QMobiusExactHead.exactHead (H + i.val))) at hseq
  simpa only [toPareto_sequence] using hseq

theorem six_not_prime_expansion (M : ℕ) (hM : 5 ≤ M) (c : Fin M → ℝ)
    (hc : ∀ i, ¬Nat.Prime (i.val + 2) → c i = 0) :
    QMobiusExactHead.exactHead 5 ≠
      ∑ i, c i • QMobiusExactHead.exactHead (i.val + 1) := by
  classical
  intro he
  have hp := congrArg toParetoLinear he
  have hcanon (Y : ℕ) : toParetoLinear (QMobiusExactHead.exactHead Y) =
      canonicalMobiusHilbert Y := QSquarefreeSublinearHeads.toPareto_exactHead Y
  simp only [map_sum, map_smul, hcanon] at hp
  let j : Fin M := ⟨4, by omega⟩
  let b : Fin M → ℝ := fun i => if i = j then 1 else 0
  have hb : (∑ i, b i • canonicalMobiusHilbert (i.val + 1)) =
      canonicalMobiusHilbert 5 := by simp [b, j]
  have heq : c = b :=
    (canonicalMobiusHilbert_finite_linearIndependent M).fintypeLinearCombination_injective
      (by
        change (∑ i, c i • canonicalMobiusHilbert (i.val + 1)) =
          ∑ i, b i • canonicalMobiusHilbert (i.val + 1)
        rw [hb, hp])
  have hz : c j = 0 := hc j (by norm_num [j])
  have ho : c j = 1 := by simpa only [b, if_pos rfl] using congrFun heq j
  linarith only [hz, ho]

end RiemannResearch.RH.QSquarefreeCanonicalExhaustion
