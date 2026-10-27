/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountablePairVariance
import RiemannResearch.RH.ZetaTwoHilbertSpace

/-!
# Pair variance for the actual Q law

The ENNReal definition applies to every real sequence without an integrability
premise. For actual Q-Hilbert vectors it equals the exact centered norm.
Source: direct countable variance expansion in the prime-resampling agenda.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.QPairVariance
open ZetaTwoHilbert
open RiemannResearch.Analysis.CountableJumpEnergy
open RiemannResearch.Analysis.CountablePairVariance

def pairFlow (n m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (positiveQWeight n) * ENNReal.ofReal (positiveQWeight m)

def pairVariance (g : ℕ → ℝ) : ℝ≥0∞ := countableJumpEnergy pairFlow g

/-- Complete pair differences equal the exact Q variance for every L2 vector. -/
theorem pairVariance_qSequence (f : QHilbert) :
    pairVariance (qSequence f) =
      ENNReal.ofReal (‖f‖ ^ 2 - (inner ℝ qOne f) ^ 2) := by
  have hw : HasSum positiveQWeight 1 := by
    simpa only [positiveQWeight_tsum] using positiveQWeight_summable.hasSum
  have hf1 : HasSum (fun n => positiveQWeight n * qSequence f n)
      (inner ℝ qOne f) := by
    have h : HasSum
        (fun n => positiveQWeight n * qSequence qOne n * qSequence f n)
        (inner ℝ qOne f) := by
      simpa only [qInner_weighted] using (qSequence_product_summable qOne f).hasSum
    apply h.congr_fun
    intro n
    rw [qSequence_qOne]
    by_cases hn : n = 0
    · subst n
      simp [positiveQWeight, qOneSequence]
    · simp [qOneSequence, hn]
  have hf2 : HasSum (fun n => positiveQWeight n * (qSequence f n) ^ 2) (‖f‖ ^ 2) := by
    simpa only [qNorm_weighted_sq] using (qSequence_square_summable f).hasSum
  exact weighted_pair_energy_eq positiveQWeight (qSequence f)
    (inner ℝ qOne f) (‖f‖ ^ 2) positiveQWeight_nonneg hw hf1 hf2

end RiemannResearch.RH.QPairVariance
