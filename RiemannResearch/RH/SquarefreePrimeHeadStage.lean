/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreePacketCapacity
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.PrimeHeadRefinedCertificates
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Finite squarefree packet legality of prime-balanced exact heads

Source: the user-provided squarefree-capacity agenda, 24 October 2026.
Divisors of a squarefree conductor remain squarefree, so the exact
residue-to-packet divisor identity places every prime-balanced trial in
the finite dictionary ending at its actual prime anchor.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.SquarefreePacketCapacity
open Pareto Pareto.CoefficientStabilization
open ZetaTwoHilbert ZetaTwoParetoTransfer QPrimeBalancedExactHead
open RiemannResearch.Analysis.FiniteHilbertGram

theorem residueAtom_mem_stage (n q : ℕ) (hq : 1 < q)
    (hs : Squarefree q) (hle : q ≤ n + 1) :
    residueAtom (q - 2) ∈ stage n := by
  have hraw : rawResidueAtom (q - 2) ∈ stage n := by
    rw [rawResidueAtom_eq_packet_divisor_sum q hq]
    apply Submodule.sum_mem
    intro d hd
    have hd2 : 1 < d := (Finset.mem_filter.mp hd).2
    have hdiv : d ∣ q := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdle : d ≤ q := Nat.le_of_dvd (by omega) hdiv
    have hds : Squarefree d := fun x hx => hs x (dvd_trans hx hdiv)
    let i : Index n := ⟨⟨d - 2, by omega⟩, by
      change Squarefree (d - 2 + 2)
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ d)] using hds⟩
    change ramanujanPacketHilbert d ∈ Submodule.span ℝ (Set.range (family n))
    exact Submodule.subset_span ⟨i, by
      change ramanujanPacketHilbert (d - 2 + 2) = ramanujanPacketHilbert d
      rw [Nat.sub_add_cancel (by omega : 2 ≤ d)]⟩
  have hh := (stage n).smul_mem ((q : ℝ)⁻¹) hraw
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  simpa only [rawResidueAtom, Nat.sub_add_cancel (by omega : 2 ≤ q),
    smul_smul, inv_mul_cancel₀ hq0, one_smul] using hh

theorem toPareto_qResidue_mem_stage (n q : ℕ) (hq : 1 < q)
    (hs : Squarefree q) (hle : q ≤ n + 1) :
    toPareto (qResidue q) ∈ stage n := by
  have he : toPareto (qResidue q) = residueAtom (q - 2) := by
    have h := toPareto_residueAtom (q - 2)
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ q)] using h
  rw [he]
  exact residueAtom_mem_stage n q hq hs hle

theorem primeHead_mem_stage (N q : ℕ) (hq : Nat.Prime q) (hNq : N < q) :
    toPareto (primeHead N q) ∈ stage (q - 1) := by
  have hq0 : 0 < q := hq.pos
  change toParetoLinear (primeHead N q) ∈ _
  unfold primeHead
  simp only [map_add, map_neg, map_sum, map_smul]
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    by_cases hds : Squarefree d
    · apply Submodule.smul_mem
      by_cases hd1 : d = 1
      · subst d
        rw [qResidue_one, map_zero]
        exact Submodule.zero_mem _
      · exact toPareto_qResidue_mem_stage (q - 1) d (by omega) hds (by omega)
    · simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hds,
        Int.cast_zero, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    exact toPareto_qResidue_mem_stage (q - 1) q hq.one_lt hq.squarefree (by omega)

theorem paretoNextPrimeHead_mem_stage (N : ℕ) :
    paretoNextPrimeHead N ∈ stage (anchorPrime N - 1) :=
  primeHead_mem_stage N (anchorPrime N) (anchorPrime_spec N).2 (anchorPrime_spec N).1

theorem kappa_lower_of_nextPrimeRawCertificate (N : ℕ) (hN : 0 < N) (K : ℕ) :
    1 - nextPrimeRawCertificate N K ≤ kappa (anchorPrime N - 1) := by
  apply kappa_lower_of_legal_error _ (paretoNextPrimeHead N)
    (paretoNextPrimeHead_mem_stage N)
  exact (nextPrimeRawCertificate_bounds N hN K).1

end RiemannResearch.RH.SquarefreePacketCapacity
