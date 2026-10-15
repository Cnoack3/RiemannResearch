/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ParetoBoundedCoordinateClosure
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QDivisorHilbertBasis
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Bounded coordinate and arithmetic-energy closure criteria under Q

Source: the bounded-coordinate argument in `ParetoBoundedCoordinateClosure`,
transported by the sequence-preserving equivalence, and the user's Q
divisibility/Parseval research program, 15 October 2026.

The subspace theorem is unconditional and applies to every restricted legal
dictionary. The RH conclusions remain conditional research reductions:
their uniform full-energy budgets are explicit Open arithmetic hypotheses.
A complete orthonormal divisor basis does not establish such a budget for
legal residue approximants.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QBoundedCoordinateClosure
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QDivisorHilbert

/-- Weak closure from bounded physical coordinate limits, for any Q subspace. -/
theorem mem_closure_of_bounded_coordinate_limits
    (S : Submodule ℝ QHilbert) (f : ℕ → QHilbert) (x : QHilbert)
    (hmem : ∀ N, f N ∈ S)
    (hcoord : ∀ k, 0 < k → Tendsto (fun N => qSequence (f N) k) atTop
      (𝓝 (qSequence x k)))
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ≤ C) :
    x ∈ S.topologicalClosure := by
  apply (mem_closure_map_iff S x).mp
  apply Pareto.mem_closure_of_bounded_coordinate_limits
    (S.map paretoEquiv.toLinearMap) (fun N => toPareto (f N)) (toPareto x)
    (fun N => ⟨f N, hmem N, rfl⟩)
    (C := Real.sqrt zetaTwo * C)
  · simpa only [toPareto_sequence] using hcoord
  · intro N
    exact (toPareto_norm_le (f N)).trans
      (mul_le_mul_of_nonneg_left (hbounded N) (Real.sqrt_nonneg _))

/-- Exact agreement on growing heads needs only a bound on the entire norm. -/
theorem mem_closure_of_bounded_matching_heads
    (S : Submodule ℝ QHilbert) (f : ℕ → QHilbert) (x : QHilbert)
    (hmem : ∀ N, f N ∈ S)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (f N) k = qSequence x k)
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ^ 2 ≤ C) :
    x ∈ S.topologicalClosure := by
  apply mem_closure_of_bounded_coordinate_limits S f x hmem (C := C + 1)
  · intro k hk
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with N hN
    exact (hhead N k hk hN).symm
  · intro N
    have := hbounded N
    nlinarith [sq_nonneg (‖f N‖ - 1)]

/-- For the actual full legal residue span, bounded physical convergence to
one suffices. The uniform norm bound is not supplied by this theorem. -/
theorem riemannHypothesis_of_bounded_legal_coordinate_limits
    (f : ℕ → QHilbert) (hmem : ∀ N, f N ∈ QFullResidueProjection.legalSpan)
    (hcoord : ∀ k, 0 < k → Tendsto (fun N => qSequence (f N) k) atTop (𝓝 1))
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ≤ C) : RiemannHypothesis := by
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  apply mem_closure_of_bounded_coordinate_limits
    QFullResidueProjection.legalSpan f qOne hmem _ hbounded
  intro k hk
  simpa only [qSequence_qOne, qOneSequence, if_neg (Nat.ne_of_gt hk)] using hcoord k hk

/-- Growing exact legal heads plus a full energy budget imply RH under Q. -/
theorem riemannHypothesis_of_bounded_legal_heads
    (f : ℕ → QHilbert) (hmem : ∀ N, f N ∈ QFullResidueProjection.legalSpan)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (f N) k = 1)
    {C : ℝ} (hbounded : ∀ N, ‖f N‖ ^ 2 ≤ C) : RiemannHypothesis := by
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  apply mem_closure_of_bounded_matching_heads
    QFullResidueProjection.legalSpan f qOne hmem _ hbounded
  intro N k hk hNk
  simpa only [qSequence_qOne, qOneSequence, if_neg (Nat.ne_of_gt hk)] using hhead N k hk hNk

/-- The complete Jordan-weighted coefficient sum is a concrete sufficient
budget for bounded legal approximants. Every divisor mode, including 1, is kept. -/
theorem riemannHypothesis_of_bounded_divisor_energy
    (f : ℕ → QHilbert) (hmem : ∀ N, f N ∈ QFullResidueProjection.legalSpan)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (f N) k = 1)
    {C : ℝ} (hbudget : ∀ N,
      (∑' r : ℕ+, (inner ℝ (f N) (divisorWavelet (r : ℕ))) ^ 2 /
        qJordanTwo (r : ℕ)) ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_legal_heads f hmem hhead
  simpa only [divisorWavelet_parseval_norm] using hbudget

end RiemannResearch.RH.QBoundedCoordinateClosure
