/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeJointIrreducibility
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Every nonzero vector is cyclic for words in B and the legal projection

Source: the user-provided paper, final section 3, November 4, 2026.
The orbit is constructed explicitly from finite operator words. Arithmetic
irreducibility makes its closed linear span the full real Q Hilbert space.
This makes no claim that the orbit of a legal vector remains legal.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeJointCommutant
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal

def wordAction : List Bool → QHilbert → QHilbert
  | [], f => f
  | false::w, f => B (wordAction w f)
  | true::w, f => closure.starProjection (wordAction w f)

def wordSpan (f : QHilbert) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun w : List Bool => wordAction w f))

theorem self_mem_wordSpan (f : QHilbert) : f ∈ wordSpan f :=
  Submodule.subset_span ⟨[], rfl⟩

theorem B_mem_wordSpan (f g : QHilbert) (hg : g ∈ wordSpan f) :
    B g ∈ wordSpan f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨w, rfl⟩ := hg
      exact Submodule.subset_span ⟨false::w, rfl⟩
  | zero => simpa only [map_zero] using (wordSpan f).zero_mem
  | add g h hg hh ihg ihh =>
      rw [map_add]
      exact (wordSpan f).add_mem ihg ihh
  | smul c g hg ihg =>
      rw [map_smul]
      exact (wordSpan f).smul_mem c ihg

theorem projection_mem_wordSpan (f g : QHilbert) (hg : g ∈ wordSpan f) :
    closure.starProjection g ∈ wordSpan f := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨w, rfl⟩ := hg
      exact Submodule.subset_span ⟨true::w, rfl⟩
  | zero => simpa only [map_zero] using (wordSpan f).zero_mem
  | add g h hg hh ihg ihh =>
      rw [map_add]
      exact (wordSpan f).add_mem ihg ihh
  | smul c g hg ihg =>
      rw [map_smul]
      exact (wordSpan f).smul_mem c ihg

theorem B_mem_closedWordSpan (f g : QHilbert)
    (hg : g ∈ (wordSpan f).topologicalClosure) :
    B g ∈ (wordSpan f).topologicalClosure := by
  have hbase : (wordSpan f : Set QHilbert) ⊆
      {g | B g ∈ (wordSpan f).topologicalClosure} := by
    intro g hg
    exact (wordSpan f).le_topologicalClosure (B_mem_wordSpan f g hg)
  have hclosed : IsClosed {g | B g ∈ (wordSpan f).topologicalClosure} :=
    (wordSpan f).isClosed_topologicalClosure.preimage B.continuous
  exact (closure_minimal hbase hclosed) hg

theorem projection_mem_closedWordSpan (f g : QHilbert)
    (hg : g ∈ (wordSpan f).topologicalClosure) :
    closure.starProjection g ∈ (wordSpan f).topologicalClosure := by
  have hbase : (wordSpan f : Set QHilbert) ⊆
      {g | closure.starProjection g ∈ (wordSpan f).topologicalClosure} := by
    intro g hg
    exact (wordSpan f).le_topologicalClosure (projection_mem_wordSpan f g hg)
  have hclosed : IsClosed
      {g | closure.starProjection g ∈ (wordSpan f).topologicalClosure} :=
    (wordSpan f).isClosed_topologicalClosure.preimage closure.starProjection.continuous
  exact (closure_minimal hbase hclosed) hg

/-- Cyclicity is unconditional for every nonzero vector, including any
hypothetical nonzero target residual. -/
theorem closedWordSpan_eq_top (f : QHilbert) (hf : f ≠ 0) :
    (wordSpan f).topologicalClosure = ⊤ := by
  rcases invariant_subspace_trivial (wordSpan f).topologicalClosure
    (B_mem_closedWordSpan f) (projection_mem_closedWordSpan f) with hzero | htop
  · have hmem := (wordSpan f).le_topologicalClosure (self_mem_wordSpan f)
    rw [hzero] at hmem
    exact False.elim (hf (by simpa only [Submodule.mem_bot] using hmem))
  · exact htop

end RiemannResearch.RH.QSquarefreeJointCommutant
