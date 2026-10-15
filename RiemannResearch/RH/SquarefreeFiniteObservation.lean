/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTSquarefreeConverse
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.CanonicalPrimeSubpolynomialWindow
import RiemannResearch.RH.MobiusDifferenceCLM
import Mathlib.Data.Nat.Prime.Infinite
import Lean.Elab.Tactic.Omega
/-!
# Finite observations cannot separate one from squarefree residue atoms

Source: user-directed squarefree closure investigation, 14 October 2026.
The proof uses the existing canonical Mobius trials at a prime boundary to
match any prescribed finite physical head exactly.

Every finite-coordinate linear functional that annihilates the squarefree
residue atoms also annihilates the constant-one sequence. This is an
unconditional finite-observation statement, not norm-closure membership.
Arbitrary continuous functionals involving infinitely many coordinates are
not covered, and no bound on the canonical trials' tail energies is asserted.
-/

open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative
noncomputable section

/-- Any finite physical-coordinate functional annihilating all squarefree
residue atoms necessarily annihilates the constant-one sequence. -/
theorem squarefree_finite_observation_annihilator
    (N : ℕ) (c : ℕ → ℝ)
    (hann : ∀ d : ℕ, 2 ≤ d → Squarefree d →
      (∑ n ∈ Finset.Icc 1 N, c n * residueFraction d n) = 0) :
    (∑ n ∈ Finset.Icc 1 N, c n) = 0 := by
  let L : ThresholdHilbert →L[ℝ] ℝ :=
    ∑ n ∈ Finset.Icc 1 N, c n • anchoredEvaluationCLM n
  have hS : squarefreeCRTSpan ≤ LinearMap.ker L.toLinearMap := by
    rw [squarefreeCRTSpan_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    change L (normalizedResidueHilbert d.val _) = 0
    simpa [L, normalizedResidueHilbert_sequence, smul_eq_mul] using
      hann d.val d.property.1 d.property.2
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
  have hpred : p - 1 + 1 = p := by have := hp.two_le; omega
  have hm : canonicalMobiusHilbert (p - 1) ∈ squarefreeCRTSpan :=
    canonicalMobiusHilbert_mem_squarefreeCRTSpan _ (by simpa [hpred] using hp.squarefree)
  have he := hS hm
  change L (canonicalMobiusHilbert (p - 1)) = 0 at he
  have hL : L (canonicalMobiusHilbert (p - 1)) =
      ∑ n ∈ Finset.Icc 1 N, c n := by
    simp only [L, sum_apply, smul_apply,
      anchoredEvaluationCLM_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n hn
    have hbounds := Finset.mem_Icc.mp hn
    rw [canonicalMobiusHilbert_exact _ _ (by omega) (by omega)]
    simp
  exact hL.symm.trans he

end
end RiemannResearch.RH.Pareto
