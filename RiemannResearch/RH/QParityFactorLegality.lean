/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QPrimeValuationFactorLegality
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QSquarefreeCapacity
import Mathlib.Tactic.Module

/-!
# Exact exceptional parity-factor legality criterion.

Finite exact identities; no asymptotic arithmetic gain bound is assumed or proved.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace RiemannResearch.RH.QParityFactorLegality
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open QSquarefreeFiniteDualClosure QPrimeValuationFactorLegality
open QDivisorLegality PrimeValuationBasis

/-- Exact constant-plus-odd decomposition, preserving both coefficients. -/
theorem compatible_parity_factor_exact (φ : ℕ → ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization 2))
    (hx : x ∈ radicalCompatible) :
    x = φ 1 • qOne + (2 * (φ 0 - φ 1)) • qResidue 2 := by
  rw [valuation_factor_binary 2 Nat.prime_two φ x hseq hx, qDivisor_two_eq]
  module

/-- The value on the even integers is the only remaining target-closure obligation. -/
theorem compatible_parity_factor_legal_iff (φ : ℕ → ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization 2))
    (hx : x ∈ radicalCompatible) :
    x ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      φ 1 • qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  have hg : qResidue 2 ∈ qSquarefreeCRTSpan.topologicalClosure :=
    qSquarefreeCRTSpan.le_topologicalClosure
      (Submodule.subset_span ⟨⟨2, ⟨by decide, Nat.prime_two.squarefree⟩⟩, rfl⟩)
  have hc := qSquarefreeCRTSpan.topologicalClosure.smul_mem (2 * (φ 0 - φ 1)) hg
  have he := compatible_parity_factor_exact φ x hseq hx
  constructor
  · intro h
    have hs := qSquarefreeCRTSpan.topologicalClosure.sub_mem h hc
    simpa only [he, add_sub_cancel_right] using hs
  · intro h
    rw [he]
    exact qSquarefreeCRTSpan.topologicalClosure.add_mem h hc

/-- Actual valuation-space version: the coefficient is the physical value at two. -/
theorem compatible_valuation_two_legal_iff (x : QHilbert)
    (hv : x ∈ valuationSpace 2) (hx : x ∈ radicalCompatible) :
    x ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      qSequence x 2 • qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  simpa only [pow_one] using compatible_parity_factor_legal_iff
    (fun k => qSequence x (2 ^ k)) x (fun n hn => hv n (ne_of_gt hn)) hx

/-- Conditional RH reduction: a legal parity factor with nonzero even value
already supplies a nonzero constant direction. -/
theorem riemannHypothesis_of_legal_parity_factor_even_nonzero
    (φ : ℕ → ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization 2))
    (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) (hφ : φ 1 ≠ 0) :
    RiemannHypothesis := by
  have hconst := (compatible_parity_factor_legal_iff φ x hseq
    (legalClosure_le_radicalCompatible hx)).mp hx
  have hone := qSquarefreeCRTSpan.topologicalClosure.smul_mem (φ 1)⁻¹ hconst
  rw [smul_smul, inv_mul_cancel₀ hφ, one_smul] at hone
  apply ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact hone

end RiemannResearch.RH.QParityFactorLegality
