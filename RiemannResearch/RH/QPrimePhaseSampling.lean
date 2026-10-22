/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QZeroPhaseSampling
import RiemannResearch.Analysis.PrimePhaseCRTCells

/-!
# Prime-phase CRT samples of the complete Q inner product

Source: user-directed zero-ordinate/CRT discussion, 21 October 2026.
Analytic background: Ford--Zaharescu (2005), arXiv:math/0405459, and
Ford--Meng--Zaharescu (2017), arXiv:1511.06814. These support the external
equidistribution input, not a formal provider of it in this module.

The finite CRT construction is unconditional. The limit theorem exposes its
joint phase-cell frequency assumption; no zeta-zero equidistribution theorem
is supplied by this file. For zero ordinates with multiplicities, κ must index
the multiplicity labels and `times` records their ordinates.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.QZeroPhaseSampling

open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.FiniteCellSampling
open RiemannResearch.Analysis.PrimePhaseCRTCells

/-- The exact sampling identity retains the joint phase-cell discrepancy.
The inverse rotation in `positivePhaseCode` is essential: raw residue zero
is the positive representative L, whose zero-based Q block index is L - 1. -/
theorem weighted_primePhase_inner_exact {κ : Type*}
    (s : Finset κ) (times : κ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (F G : ℕ → ℝ) :
    sampleMean s (fun j => positivePhaseCode P hP (times j)) (fun a =>
      ((primeProduct P : ℝ) *
        residuePowerWeight 0 (primeProduct P) (a.val + 1)) *
          (F (a.val + 1) * G (a.val + 1))) =
      ∑ a : Fin (primeProduct P),
        residuePowerWeight 0 (primeProduct P) (a.val + 1) *
          ((primeProduct P : ℝ) *
            jointCellFrequency s times P (finRotate (primeProduct P) a)) *
          (F (a.val + 1) * G (a.val + 1)) := by
  rw [weighted_inner_sample_exact]
  simp only [positivePhaseCode, cellFrequency_equiv, Equiv.symm_symm,
    phaseCode_cellFrequency]

/-- Uniform joint frequencies of the actual prime-phase bins recover the
complete Q inner product of bounded periodic physical representatives. -/
theorem weighted_primePhase_inner_tendsto {κ : Type*}
    (s : ℕ → Finset κ) (times : κ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f g : QHilbert) (F G : ℕ → ℝ) {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D)
    (hpF : ∀ k, F (k + primeProduct P) = F k)
    (hpG : ∀ k, G (k + primeProduct P) = G k)
    (hf : ∀ k, qSequence f (k + 1) = F (k + 1))
    (hg : ∀ k, qSequence g (k + 1) = G (k + 1))
    (hcell : ∀ r, Tendsto (fun n => jointCellFrequency (s n) times P r)
      atTop (𝓝 (1 / (primeProduct P : ℝ)))) :
    Tendsto (fun n => sampleMean (s n)
      (fun j => positivePhaseCode P hP (times j)) (fun a =>
        ((primeProduct P : ℝ) *
          residuePowerWeight 0 (primeProduct P) (a.val + 1)) *
            (F (a.val + 1) * G (a.val + 1))))
      atTop (𝓝 (inner ℝ f g)) := by
  apply weighted_inner_sample_tendsto (primeProduct P) (primeProduct_pos P hP)
    s (fun j => positivePhaseCode P hP (times j))
    f g F G hF hG hpF hpG hf hg
  exact positivePhaseCode_frequency_tendsto s times P hP hcell

end RiemannResearch.RH.QZeroPhaseSampling
