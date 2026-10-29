/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.RamanujanHilbertTransfer
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# An explicit nonzero Pareto annihilator of the squarefree legal space

The physical vector is (2,-6,-12,20,0,...). Its norm squared is 40 and
its pairing with f is f(1)-f(2)-f(3)+f(4). It annihilates both squarefree
residue and squarefree Ramanujan closed spans. It also annihilates the
constant, so this properness result does not decide constant membership.

It does NOT annihilate the full-conductor legal space: its pairing with g4
is -1. This scope distinction is part of the theorem statements below.

Source: user-requested Ramanujan/Pareto legal-span audit, 28 October 2026.
The squarefree four-site identity is transferred from QSquarefreeBoundary;
this module establishes its explicit Pareto Riesz representative.
-/

noncomputable section
namespace RiemannResearch.RH.ParetoRamanujanSquarefreeAnnihilator
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QSquarefreeBoundary

def fourSiteWitness : ThresholdHilbert :=
  (2 : ℝ) • paretoPointHilbert 0 + (-6 : ℝ) • paretoPointHilbert 1 +
    (-12 : ℝ) • paretoPointHilbert 2 + (20 : ℝ) • paretoPointHilbert 3

theorem fourSiteWitness_pairing (f : ThresholdHilbert) :
    inner ℝ fourSiteWitness f =
      hilbertGibbsPhysical f 0 - hilbertGibbsPhysical f 1 -
        hilbertGibbsPhysical f 2 + hilbertGibbsPhysical f 3 := by
  rw [real_inner_comm, fourSiteWitness]
  simp only [inner_add_right, real_inner_smul_right, inner_paretoPoint]
  norm_num [paretoWeight]
  ring

theorem fourSiteWitness_norm_sq : ‖fourSiteWitness‖ ^ 2 = 40 := by
  rw [← real_inner_self_eq_norm_sq, fourSiteWitness_pairing]
  simp only [fourSiteWitness, hilbertGibbsPhysical_add,
    hilbertGibbsPhysical_smul, hilbertGibbsPhysical_paretoPoint]
  norm_num

theorem fourSiteWitness_ne_zero : fourSiteWitness ≠ 0 := by
  intro h
  have he := fourSiteWitness_norm_sq
  rw [h] at he
  norm_num at he

theorem fourSiteWitness_inner_one : inner ℝ fourSiteWitness hilbertOne = 0 := by
  rw [fourSiteWitness_pairing]
  norm_num [hilbertGibbs_one_physical]

theorem fourSiteWitness_toPareto (f : QHilbert) :
    inner ℝ fourSiteWitness (toPareto f) = fourSiteFunctional f := by
  rw [fourSiteWitness_pairing, fourSiteFunctional_apply]
  simp only [hilbertGibbsPhysical_eq, toPareto_sequence]
  norm_num
  ring

def paretoFourSite : ThresholdHilbert →L[ℝ] ℝ :=
  fourSiteFunctional.comp toQCLM

theorem fourSiteWitness_functional (f : ThresholdHilbert) :
    inner ℝ fourSiteWitness f = paretoFourSite f := by
  have h := fourSiteWitness_toPareto (toQ f)
  rw [toPareto_toQ] at h
  exact h

def squarefreeConductors : Set ℕ := {d | 1 < d ∧ Squarefree d}

def squarefreeResidueClosure : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ (BaezDuarte.residueVector '' squarefreeConductors)).topologicalClosure

def squarefreeRamanujanClosure : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ (ramanujanPacketHilbert '' squarefreeConductors)).topologicalClosure

theorem qResidue_mem_squarefreeClosure {d : ℕ}
    (hd : 1 < d) (hs : Squarefree d) :
    qResidue d ∈ ZetaTwoOptimizerStage.closure := by
  apply (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).le_topologicalClosure
  have he : d - 2 + 2 = d := by omega
  have ha : ZetaTwoOptimizerStage.squarefreeAtom (d - 2) = qResidue d := by
    simp only [ZetaTwoOptimizerStage.squarefreeAtom, he, if_pos hs]
  rw [← ha]
  exact Submodule.subset_span ⟨d - 2, rfl⟩

theorem paretoFourSite_zero_on_residue {d : ℕ} (hd : 1 < d)
    (hs : Squarefree d) : paretoFourSite (BaezDuarte.residueVector d) = 0 := by
  change fourSiteFunctional (toQ (BaezDuarte.residueVector d)) = 0
  rw [toQ_residueVector d (by omega)]
  exact fourSiteFunctional_zero_on_closure (qResidue_mem_squarefreeClosure hd hs)

theorem paretoFourSite_zero_on_closure {f : ThresholdHilbert}
    (hf : f ∈ squarefreeResidueClosure) : paretoFourSite f = 0 := by
  let K : Submodule ℝ ThresholdHilbert := paretoFourSite.ker
  have hspan : Submodule.span ℝ
      (BaezDuarte.residueVector '' squarefreeConductors) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    exact paretoFourSite_zero_on_residue hd.1 hd.2
  have hclosed : IsClosed (K : Set ThresholdHilbert) := by
    change IsClosed {f : ThresholdHilbert | paretoFourSite f = 0}
    exact isClosed_eq paretoFourSite.continuous continuous_const
  have hf' : f ∈ _root_.closure
      (Submodule.span ℝ (BaezDuarte.residueVector '' squarefreeConductors) :
        Set ThresholdHilbert) := hf
  exact (closure_minimal hspan hclosed) hf'

theorem fourSiteWitness_mem_residue_orthogonal :
    fourSiteWitness ∈ squarefreeResidueClosureᗮ := by
  intro f hf
  rw [real_inner_comm, fourSiteWitness_functional]
  exact paretoFourSite_zero_on_closure hf

theorem squarefreeRamanujanClosure_eq_residueClosure :
    squarefreeRamanujanClosure = squarefreeResidueClosure := by
  apply RamanujanTransfer.p_closure_eq squarefreeConductors
  · intro d hd
    exact lt_trans Nat.zero_lt_one hd.1
  · intro d hd q hqd hq
    refine ⟨hq, ?_⟩
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hpp
    exact (Nat.squarefree_iff_prime_squarefree.mp hd.2 p hp) (dvd_trans hpp hqd)

theorem fourSiteWitness_mem_ramanujan_orthogonal :
    fourSiteWitness ∈ squarefreeRamanujanClosureᗮ := by
  rw [squarefreeRamanujanClosure_eq_residueClosure]
  exact fourSiteWitness_mem_residue_orthogonal

theorem squarefreeRamanujan_orthogonal_ne_bot :
    squarefreeRamanujanClosureᗮ ≠ ⊥ := by
  intro he
  have hw := fourSiteWitness_mem_ramanujan_orthogonal
  rw [he] at hw
  apply fourSiteWitness_ne_zero
  simpa using hw

/-- This vector is a squarefree annihilator, not a full-conductor annihilator. -/
theorem fourSiteWitness_pairing_residue_four :
    inner ℝ fourSiteWitness (BaezDuarte.residueVector 4) = -1 := by
  rw [← toPareto_qResidue 4 (by norm_num), fourSiteWitness_toPareto]
  exact fourSiteFunctional_qResidue_four

end RiemannResearch.RH.ParetoRamanujanSquarefreeAnnihilator
