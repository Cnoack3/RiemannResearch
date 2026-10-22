/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeValuationIndependence
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Probability.Independence.Basic

/-!
# Independence of actual prime-packet increments

Source: user-directed prime-factor argument, 21--22 October 2026.
The existing exact residue difference turns the prime packet increment
at a positive integer into an affine divisibility indicator. The existing
actual Q law therefore proves mutual independence of these increments.
This is a statement about increments under Q, not about integrated packets
or their Pareto Gram matrix.
-/

noncomputable section

namespace RiemannResearch.RH.ZetaTwoProbability
open MeasureTheory ProbabilityTheory
open RiemannResearch.RH.Pareto
def packetIncrement (q : ℕ) (k : ℕ+) : ℝ :=
  ramanujanPacket q (k : ℕ) - ramanujanPacket q ((k : ℕ) - 1)

theorem packetIncrement_prime (p : ℕ) (hp : p.Prime) (k : ℕ+) :
    packetIncrement p k =
      (fun b : Bool => 1 - if b then (p : ℝ) else 0) (divisibilityBool p k) := by
  rw [packetIncrement, ramanujanPacket_prime_eq_residue p hp,
    residue_difference p (k : ℕ) k.pos]
  simp [divisibilityBool]

theorem iIndepFun_primePacketIncrement {ι : Type*} (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    iIndepFun (fun i => packetIncrement (p i)) Q := by
  have h := (iIndepFun_divisibilityBool p hp hinj).comp
    (fun i (b : Bool) => (1 : ℝ) - if b then (p i : ℝ) else 0)
    (fun i => measurable_of_countable
      (fun b : Bool => (1 : ℝ) - if b then (p i : ℝ) else 0))
  have heq : (fun i => packetIncrement (p i)) =
      (fun i => (fun b : Bool => (1 : ℝ) - if b then (p i : ℝ) else 0) ∘
        divisibilityBool (p i)) := by
    funext i k
    exact packetIncrement_prime (p i) (hp i) k
  rw [heq]
  exact h
end RiemannResearch.RH.ZetaTwoProbability
