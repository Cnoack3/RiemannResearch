/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoAmplitudeCertificates
import RiemannResearch.RH.QPrimeBalancedExactHead
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Refined complete-P certificates for the least-prime-balanced family

Source: user-provided capacity/energy agenda, 24 October 2026.
The Q-defined arithmetic trial is reencoded with the complete P weights.
The finite certificate retains the entire omitted tail and is within a
factor of two of the regularized actual P energy. No divergence or RH
converse provider is presumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeBalancedExactHead
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open Pareto.AmplitudeCertificates

def paretoNextPrimeHead (N : ℕ) : ThresholdHilbert :=
  toPareto (nextPrimeHead N)

def nextPrimeResidual (N n : ℕ) : ℝ :=
  qSequence (nextPrimeHead N) n - 1

def nextPrimeCertificate (N : ℕ) : ℝ :=
  unitCertificate (nextPrimeResidual N) (N + anchorPrime N)

def nextPrimeRawCertificate (N K : ℕ) : ℝ :=
  certificate (nextPrimeResidual N) (N + anchorPrime N : ℕ) K

theorem paretoNextPrimeHead_sequence (N : ℕ) :
    hilbertSequence (paretoNextPrimeHead N) = qSequence (nextPrimeHead N) :=
  toPareto_sequence _

theorem paretoNextPrimeHead_mem_squarefreeCRTSpan (N : ℕ) :
    paretoNextPrimeHead N ∈ squarefreeCRTSpan := by
  rw [← qSquarefreeCRTSpan_map]
  exact ⟨nextPrimeHead N, nextPrimeHead_mem_squarefreeSpan N, rfl⟩

theorem paretoNextPrimeHead_exact (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    hilbertSequence (paretoNextPrimeHead N) n = 1 := by
  rw [paretoNextPrimeHead_sequence]
  exact nextPrimeHead_exact N n hn hnN

/-- This equality is with the complete P norm, not the Q norm. -/
theorem nextPrimeResidual_energy_eq (N : ℕ) :
    energy (nextPrimeResidual N) = ‖hilbertOne - paretoNextPrimeHead N‖ ^ 2 := by
  rw [hilbert_norm_sq]
  unfold energy
  apply tsum_congr
  intro n
  rw [← hilbertSequence_weighted_square]
  have hseq : hilbertSequence (hilbertOne - paretoNextPrimeHead N) (n+1) =
      1 - qSequence (nextPrimeHead N) (n+1) := by
    change hilbertSequenceLinear (hilbertOne - paretoNextPrimeHead N) (n+1) = _
    rw [map_sub]
    change hilbertSequence hilbertOne (n+1) -
      hilbertSequence (paretoNextPrimeHead N) (n+1) = _
    rw [hilbertOne_sequence, paretoNextPrimeHead_sequence]
    simp [zeroAnchor]
  have hw : paretoWeight n = positiveWeight (n+1) := by
    unfold paretoWeight positiveWeight
    push_cast
    ring
  rw [hw, hseq]
  unfold nextPrimeResidual
  ring

theorem nextPrimeCertificate_bounds (N : ℕ) (hN : 0 < N) :
    max 1 (‖hilbertOne - paretoNextPrimeHead N‖ ^ 2) ≤ nextPrimeCertificate N ∧
      nextPrimeCertificate N ≤ 2 * max 1 (‖hilbertOne - paretoNextPrimeHead N‖ ^ 2) := by
  have hb := unitCertificate_bounds (nextPrimeResidual N) (N + anchorPrime N)
    (fun n => nextPrimeHead_amplitude N (n+1) hN)
  simpa only [nextPrimeCertificate, nextPrimeResidual_energy_eq] using hb

/-- An arbitrary numerical cutoff gives a complete, nonregularized error
certificate, suitable for a nontrivial finite capacity lower bound. -/
theorem nextPrimeRawCertificate_bounds (N : ℕ) (hN : 0 < N) (K : ℕ) :
    ‖hilbertOne - paretoNextPrimeHead N‖ ^ 2 ≤ nextPrimeRawCertificate N K ∧
      nextPrimeRawCertificate N K ≤ ‖hilbertOne - paretoNextPrimeHead N‖ ^ 2 +
        ((N + anchorPrime N : ℕ) : ℝ)^2 / ((K : ℝ)+1) := by
  have hb := certificate_bounds (nextPrimeResidual N) (N + anchorPrime N : ℕ)
    (Nat.cast_nonneg _) (fun n => nextPrimeHead_amplitude N (n+1) hN) K
  simpa only [nextPrimeRawCertificate, nextPrimeResidual_energy_eq] using hb

/-- Refinement preserves exactly the summability status of the regularized
actual energies along every selected positive-head sequence. -/
theorem nextPrimeCertificate_reciprocal_summable_iff
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j) :
    Summable (fun j => (nextPrimeCertificate (N j))⁻¹) ↔
      Summable (fun j => (max 1 (‖hilbertOne - paretoNextPrimeHead (N j)‖ ^ 2))⁻¹) := by
  have h := reciprocal_summable_iff (fun j => nextPrimeResidual (N j))
    (fun j => N j + anchorPrime (N j))
    (fun j n => nextPrimeHead_amplitude (N j) (n+1) (hN j))
  simpa only [nextPrimeCertificate, nextPrimeResidual_energy_eq] using h

end RiemannResearch.RH.QPrimeBalancedExactHead
