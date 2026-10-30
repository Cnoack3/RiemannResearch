/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTPrimeInnovation
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.Primorial
import Lean.Elab.Tactic.Omega

/-! Exhaustion of the entire squarefree dictionary by the actual dense schedule.
Source: the user's explicit full-squarefree requirement, 30 October 2026.
Composite squarefree conductors are included, as are arbitrary finite supports.
These span equalities do not prove that the constant belongs to the closure. -/
noncomputable section
namespace RiemannResearch.RH.QCRTSquarefreeExhaustion
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QSquarefreeEnergyTransitions QCRTPrimeInnovation QSquarefreeAffineHead

theorem squarefree_conductor_mem (d i : ℕ) (hd : 1 < d) (hsf : Squarefree d)
    (hdi : d ≤ i) : d ∈ conductors (oldPeriod i) := by
  have hdL : d ∣ oldPeriod i :=
    dvd_trans hsf.dvd_primorial (primorial_dvd_primorial
      (by dsimp [denseSchedule]; omega))
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hdL, primorial_ne_zero _⟩, hd⟩

/-- Every squarefree conductor, including composite ones, enters permanently. -/
theorem every_squarefree_conductor_eventually (d : ℕ) (hd : 1 < d)
    (hsf : Squarefree d) :
    ∃ I : ℕ, ∀ i, I ≤ i → d ∈ conductors (oldPeriod i) := by
  exact ⟨d, fun i hdi => squarefree_conductor_mem d i hd hsf hdi⟩

theorem every_finite_squarefree_support (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d ∧ Squarefree d) :
    ∃ I : ℕ, ∀ i, I ≤ i → s ⊆ conductors (oldPeriod i) := by
  refine ⟨s.sup id, ?_⟩
  intro i hIi d hd
  exact squarefree_conductor_mem d i (hs d hd).1 (hs d hd).2
    ((Finset.le_sup (f := id) hd).trans hIi)

/-- Equality of algebraic spans; no prime-only subdictionary is substituted. -/
theorem dense_iSup_eq_squarefreeSpan :
    (⨆ i : ℕ, divisorStage (oldPeriod i)) = qSquarefreeCRTSpan := by
  apply le_antisymm
  · exact iSup_le (fun i => divisorStage_le_squarefreeSpan
      (oldPeriod i) (primorial_pos _) (squarefree_primorial _))
  · unfold qSquarefreeCRTSpan
    apply Submodule.span_le.mpr
    rintro f ⟨d, rfl⟩
    apply (le_iSup (fun i : ℕ => divisorStage (oldPeriod i)) d.val)
    apply Submodule.subset_span
    exact ⟨d.val,
      (Nat.mem_divisors.mp (Finset.mem_filter.mp
        (squarefree_conductor_mem d.val d.val d.property.1 d.property.2 le_rfl)).1).1, rfl⟩

/-- The closure of the scheduled union is exactly the full squarefree closure. -/
theorem dense_closure_eq_squarefreeClosure :
    (⨆ i : ℕ, divisorStage (oldPeriod i)).topologicalClosure =
      qSquarefreeCRTSpan.topologicalClosure := by
  rw [dense_iSup_eq_squarefreeSpan]
end RiemannResearch.RH.QCRTSquarefreeExhaustion
