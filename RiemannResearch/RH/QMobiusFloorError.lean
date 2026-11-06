/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.CanonicalMobiusWindowCancellation
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring

/-!
# Complete signed floor and Mertens errors for the all-conductor Möbius head

Source: Full_Conductor_RH_Projection_Machinery, 6 November 2026, task A2.
The concrete exact head and its full legal membership are QMobiusExactHead.
The arithmetic inputs below are the existing unconditional finite floor
expansion and finite hyperbola identity, specialized to the actual Q defect.
Every signed summand and the conductor-N+1 correction are retained.
The two inner finite sums in the Mertens formula are the ordinary Mertens
partial sums. No RH hypothesis or analytic converse provider is used.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QMobiusFloorError
open ZetaTwoHilbert QAnnihilatorTailEscape

/-- Exact signed error, including the anchored physical coordinate zero. -/
theorem defect_sequence_floor_sum (N n : ℕ) :
    qSequence (defect N) n = qOneSequence n -
      (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) +
      (((N + 1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum N) *
        ((n / (N + 1) : ℕ) : ℝ) := by
  change qSequenceLinear (qOne - QMobiusExactHead.exactHead N) n = _
  rw [map_sub]
  change qSequence qOne n - qSequence (QMobiusExactHead.exactHead N) n = _
  rw [qSequence_qOne, QMobiusExactHead.exactHead_sequence,
    Pareto.canonicalMobiusHead_floor_expansion]
  ring

/-- Exact full Mertens hyperbola error on and beyond the head endpoint. -/
theorem defect_sequence_mertens_sum (N n : ℕ) (hn : 0 < n) (hNn : N ≤ n) :
    qSequence (defect N) n =
      (∑ k ∈ Finset.Icc 1 (n / (N + 1)),
        ((∑ d ∈ Finset.Icc 1 (n / k), (ArithmeticFunction.moebius d : ℝ)) -
          (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)))) +
      (((N + 1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum N) *
        ((n / (N + 1) : ℕ) : ℝ) := by
  rw [defect_sequence_floor_sum]
  simp only [qOneSequence, if_neg (Nat.ne_of_gt hn)]
  rw [Pareto.finite_mobius_floor_tail_identity N n hn hNn]

end RiemannResearch.RH.QMobiusFloorError
