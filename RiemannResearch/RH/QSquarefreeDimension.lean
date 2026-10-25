/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.Analysis.ContinuousBiorthogonalDeletion
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Lean.Elab.Tactic.Omega

/-!
# Infinite dimension of the squarefree closed span

Source: the user's question about compactness of its boundary and balls.
An infinite independent prime-atom subfamily proves infinite dimension;
Riesz's theorem then excludes norm compactness of every positive-radius ball.
-/

noncomputable section

namespace RiemannResearch.RH.QSquarefreeDimension

open ZetaTwoHilbert ZetaTwoOptimizerStage SquarefreeMobiusProjection

theorem qResidue_mem_of_squarefree {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d) :
    qResidue d ∈ ZetaTwoOptimizerStage.closure := by
  apply (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure
  have hi : squarefreeAtom (d - 2) = qResidue d := by
    simp [squarefreeAtom, Nat.sub_add_cancel hd, hs]
  rw [← hi]
  exact Submodule.subset_span ⟨d - 2, rfl⟩

theorem full_atom_linearIndependent :
    LinearIndependent ℝ (fun i : ℕ => qResidue (i + 2)) := by
  exact RiemannResearch.Analysis.continuous_biorthogonal_linearIndependent
    (fun i => qResidue (i + 2)) (fun i => qCoefficientCLM (i + 2))
    q_coordinate_biorthogonal

theorem prime_atom_linearIndependent :
    LinearIndependent ℝ (fun p : {p : ℕ // p.Prime} => qResidue p.val) := by
  have hi : Function.Injective (fun p : {p : ℕ // p.Prime} => p.val - 2) := by
    intro p q hpq
    change p.val - 2 = q.val - 2 at hpq
    apply Subtype.ext
    have hp := p.property.two_le
    have hq := q.property.two_le
    omega
  have h := full_atom_linearIndependent.comp
    (fun p : {p : ℕ // p.Prime} => p.val - 2) hi
  change LinearIndependent ℝ
    (fun p : {p : ℕ // p.Prime} => qResidue (p.val - 2 + 2)) at h
  have heq : (fun p : {p : ℕ // p.Prime} => qResidue (p.val - 2 + 2)) =
      (fun p : {p : ℕ // p.Prime} => qResidue p.val) := by
    funext p
    rw [Nat.sub_add_cancel p.property.two_le]
  rwa [heq] at h

theorem closure_not_finiteDimensional :
    ¬ FiniteDimensional ℝ ZetaTwoOptimizerStage.closure := by
  intro hfin
  letI := hfin
  letI : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOfPred_prime.to_subtype
  let atoms : {p : ℕ // p.Prime} → ZetaTwoOptimizerStage.closure := fun p =>
    ⟨qResidue p.val,
      qResidue_mem_of_squarefree p.property.two_le p.property.squarefree⟩
  have hli : LinearIndependent ℝ atoms :=
    LinearIndependent.of_comp ZetaTwoOptimizerStage.closure.subtype
      prime_atom_linearIndependent
  exact Finite.false (LinearIndependent.finite hli)

theorem closedBall_not_isCompact (r : ℝ) (hr : 0 < r) :
    ¬ IsCompact (Metric.closedBall (0 : ZetaTwoOptimizerStage.closure) r) := by
  intro hc
  exact closure_not_finiteDimensional
    (FiniteDimensional.of_isCompact_closedBall ℝ hr hc)

end RiemannResearch.RH.QSquarefreeDimension
