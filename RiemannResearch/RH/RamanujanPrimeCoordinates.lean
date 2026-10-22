/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeParetoGram
import RiemannResearch.RH.QRamanujanPackets
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QFinitePrimeBasis
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Actual Ramanujan packet coordinates against independent prime modes

Source: user-directed prime-factor/Gram argument, 21--22 October 2026.
The finite Q prime modes come from the proved prime-valuation law.
Every identity retains the full Q projection residual and the exact
Radon--Nikodym correction. No completeness of divisibility modes, statistical
packet independence, or squarefree capacity limit is asserted.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.RamanujanPrimeCoordinates
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer
open QFinitePrimeBasis QPrimeParetoGram QRamanujanPackets Pareto

@[simp] theorem toPareto_packet (q : ℕ) :
    toPareto (qRamanujanPacket q) = ramanujanPacketHilbert q := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, qSequence_qRamanujanPacket,
    hilbertSequence_ramanujanPacketHilbert]

def qPacketSynthesis (s : Finset ℕ) (a : ℕ → ℝ) : QHilbert :=
  ∑ q ∈ s, a q • qRamanujanPacket q

@[simp] theorem toPareto_qPacketSynthesis (s : Finset ℕ) (a : ℕ → ℝ) :
    toPareto (qPacketSynthesis s a) =
      ∑ q ∈ s, a q • ramanujanPacketHilbert q := by
  change toParetoLinear (∑ q ∈ s, a q • qRamanujanPacket q) = _
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro q _
  change a q • toPareto (qRamanujanPacket q) = _
  rw [toPareto_packet]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeCoefficient (s : Finset ℕ) (a : ℕ → ℝ)
    (p : ι → ℕ) (A : Finset ι) : ℝ :=
  inner ℝ (qPacketSynthesis s a) (primeUnitVector p A)

/-- Literal entries of the finite prime observation matrix, applied to a. -/
theorem primeCoefficient_eq_sum (s : Finset ℕ) (a : ℕ → ℝ)
    (p : ι → ℕ) (A : Finset ι) :
    primeCoefficient s a p A =
      ∑ q ∈ s, a q * inner ℝ (qRamanujanPacket q) (primeUnitVector p A) := by
  simp only [primeCoefficient, qPacketSynthesis, sum_inner, real_inner_smul_left]

/-- Exact complete packet energy, including both residual and RN correction. -/
theorem packet_prime_energy_exact (s : Finset ℕ) (a : ℕ → ℝ)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset ι)) :
    ‖∑ q ∈ s, a q • ramanujanPacketHilbert q‖ ^ 2 =
      zetaTwo * ((∑ A ∈ S, primeCoefficient s a p A ^ 2) +
        ‖qPacketSynthesis s a - ∑ A ∈ S,
          primeCoefficient s a p A • primeUnitVector p A‖ ^ 2) -
      zetaTwo * normCorrection (qPacketSynthesis s a) := by
  simpa only [primeCoefficient, toPareto_qPacketSynthesis] using
    prime_projection_full_energy_exact p hp hinj (qPacketSynthesis s a) S

/-- Two-sided full-packet certificate; the projection remainder is retained. -/
theorem packet_prime_energy_bounds (s : Finset ℕ) (a : ℕ → ℝ)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset ι)) :
    (zetaTwo / 2) * ((∑ A ∈ S, primeCoefficient s a p A ^ 2) +
      ‖qPacketSynthesis s a - ∑ A ∈ S,
        primeCoefficient s a p A • primeUnitVector p A‖ ^ 2) ≤
      ‖∑ q ∈ s, a q • ramanujanPacketHilbert q‖ ^ 2 ∧
    ‖∑ q ∈ s, a q • ramanujanPacketHilbert q‖ ^ 2 ≤
      zetaTwo * ((∑ A ∈ S, primeCoefficient s a p A ^ 2) +
      ‖qPacketSynthesis s a - ∑ A ∈ S,
        primeCoefficient s a p A • primeUnitVector p A‖ ^ 2) := by
  simpa only [primeCoefficient, toPareto_qPacketSynthesis] using
    prime_projection_full_energy_bounds p hp hinj (qPacketSynthesis s a) S

/-- Literal quadratic form certificate H >= zetaTwo/2 times C-transpose C. -/
theorem packet_prime_observation_lower (s : Finset ℕ) (a : ℕ → ℝ)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset ι)) :
    (zetaTwo / 2) * (∑ A ∈ S, primeCoefficient s a p A ^ 2) ≤
      ‖∑ q ∈ s, a q • ramanujanPacketHilbert q‖ ^ 2 := by
  have h := (packet_prime_energy_bounds s a p hp hinj S).1
  have hZ : 0 ≤ zetaTwo / 2 := by have hz := zetaTwo_pos; positivity
  have hr : 0 ≤ ‖qPacketSynthesis s a - ∑ A ∈ S,
      primeCoefficient s a p A • primeUnitVector p A‖ ^ 2 := sq_nonneg _
  nlinarith

/-- The actual unit-target residual is represented by the same Q sequence. -/
theorem toPareto_packet_residual (s : Finset ℕ) (a : ℕ → ℝ) :
    toPareto (qOne - qPacketSynthesis s a) =
      hilbertOne - ∑ q ∈ s, a q • ramanujanPacketHilbert q := by
  change toParetoLinear (qOne - qPacketSynthesis s a) = _
  rw [map_sub]
  change toPareto qOne - toPareto (qPacketSynthesis s a) = _
  rw [toPareto_qOne, toPareto_qPacketSynthesis]

/-- Exact target-error diagnostic; finite prime observations retain the tail. -/
theorem packet_target_prime_energy_exact (s : Finset ℕ) (a : ℕ → ℝ)
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (S : Finset (Finset ι)) :
    ‖hilbertOne - ∑ q ∈ s, a q • ramanujanPacketHilbert q‖ ^ 2 =
      zetaTwo * ((∑ A ∈ S,
        (inner ℝ (qOne - qPacketSynthesis s a) (primeUnitVector p A)) ^ 2) +
      ‖(qOne - qPacketSynthesis s a) - ∑ A ∈ S,
        (inner ℝ (qOne - qPacketSynthesis s a) (primeUnitVector p A)) •
          primeUnitVector p A‖ ^ 2) -
      zetaTwo * normCorrection (qOne - qPacketSynthesis s a) := by
  simpa only [toPareto_packet_residual] using
    prime_projection_full_energy_exact p hp hinj (qOne - qPacketSynthesis s a) S

end RiemannResearch.RH.RamanujanPrimeCoordinates
