/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The screened basis for an enlargement of an exact-head residue dictionary

Source: the user-provided capacity-increment agenda, 29 October 2026,
Priority A. Independence and the entire innovation span are proved from
the existing full compensated basis. No Gram invertibility is assumed.
The actual-family arithmetic hypotheses are discharged in QCRTInnovationBlock.
-/

noncomputable section
namespace RiemannResearch.RH.QResidueHeadExtension
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

def addedFamily (s t : Finset ℕ) (r : ℕ) : ↥(t \ s) → QHilbert :=
  fun d => compensatedResidue d r

theorem combined_independent (s t : Finset ℕ) (H r : ℕ)
    (ht : ∀ d ∈ t, 1 < d) (hst : s ⊆ t) (hr : r ∈ s)
    (hnew : ∀ d ∈ t \ s, H < d) :
    LinearIndependent ℝ
      (Sum.elim (fun d : freeConductors s H r => compensatedResidue d r)
        (addedFamily s t r)) := by
  classical
  let e : ↥(freeConductors s H r) ⊕ ↥(t \ s) → ↥(freeConductors t H r) :=
    Sum.elim
      (fun d => ⟨d, Finset.mem_filter.mpr
        ⟨hst (Finset.mem_filter.mp d.property).1, (Finset.mem_filter.mp d.property).2⟩⟩)
      (fun d => ⟨d, Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp d.property).1, hnew d d.property,
          fun he => (Finset.mem_sdiff.mp d.property).2 (he ▸ hr)⟩⟩)
  have he : Function.Injective e := by
    intro a b hab
    have hv := congrArg Subtype.val hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hv)
      | inr b =>
        have ha := (Finset.mem_filter.mp a.property).1
        exact False.elim ((Finset.mem_sdiff.mp b.property).2 (hv ▸ ha))
    | inr a =>
      cases b with
      | inl b =>
        have hb := (Finset.mem_filter.mp b.property).1
        exact False.elim ((Finset.mem_sdiff.mp a.property).2 (hv.symm ▸ hb))
      | inr b => exact congrArg Sum.inr (Subtype.ext hv)
  have hi := (compensated_linearIndependent t ht H r (hst hr)).comp e he
  convert hi using 1
  funext j
  cases j <;> rfl

theorem tangent_extension (s t : Finset ℕ) (H r : ℕ)
    (hs : ∀ d ∈ s, 1 < d) (ht : ∀ d ∈ t, 1 < d)
    (hst : s ⊆ t) (hH : 0 < H) (hr : r ∈ s) (hHr : H < r)
    (hnew : ∀ d ∈ t \ s, H < d) :
    (dictionary s ⊓ headNull H) ⊔
      Submodule.span ℝ (Set.range (addedFamily s t r)) =
        dictionary t ⊓ headNull H := by
  classical
  rw [inf_headNull_eq_zeroHeadSpan s hs H r hH hr hHr,
    inf_headNull_eq_zeroHeadSpan t ht H r hH (hst hr) hHr]
  apply le_antisymm
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span
        ⟨⟨d, Finset.mem_filter.mpr
          ⟨hst (Finset.mem_filter.mp d.property).1,
            (Finset.mem_filter.mp d.property).2⟩⟩, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span
        ⟨⟨d, Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp d.property).1, hnew d d.property,
            fun he => (Finset.mem_sdiff.mp d.property).2 (he ▸ hr)⟩⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    by_cases hd : (d : ℕ) ∈ s
    · apply (show zeroHeadSpan s H r ≤ zeroHeadSpan s H r ⊔
        Submodule.span ℝ (Set.range (addedFamily s t r)) from le_sup_left)
      exact Submodule.subset_span
        ⟨⟨d, Finset.mem_filter.mpr ⟨hd, (Finset.mem_filter.mp d.property).2⟩⟩, rfl⟩
    · apply (show Submodule.span ℝ (Set.range (addedFamily s t r)) ≤
        zeroHeadSpan s H r ⊔ Submodule.span ℝ (Set.range (addedFamily s t r)) from le_sup_right)
      exact Submodule.subset_span
        ⟨⟨d, Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp d.property).1, hd⟩⟩, rfl⟩

theorem screened_added_independent (s t : Finset ℕ) (H r : ℕ)
    (hs : ∀ d ∈ s, 1 < d) (ht : ∀ d ∈ t, 1 < d)
    (hst : s ⊆ t) (hH : 0 < H) (hr : r ∈ s) (hHr : H < r)
    (hnew : ∀ d ∈ t \ s, H < d) :
    LinearIndependent ℝ
      (fun d => innovation (dictionary s ⊓ headNull H) (addedFamily s t r d)) := by
  let u := fun d : freeConductors s H r => compensatedResidue d r
  have hu := compensated_linearIndependent s hs H r hr
  have hspan : synthesisSpan u = dictionary s ⊓ headNull H :=
    (inf_headNull_eq_zeroHeadSpan s hs H r hH hr hHr).symm
  have hi := screened_linearIndependent hu (addedFamily s t r)
    (combined_independent s t H r ht hst hr hnew)
  convert hi using 1
  · funext d
    unfold screened
    rw [synthesis_inverseCoeff_eq_projection]
    simp only [← hspan, innovation]
    rfl
  · rfl

theorem screened_added_span (s t : Finset ℕ) (H r : ℕ)
    (hs : ∀ d ∈ s, 1 < d) (ht : ∀ d ∈ t, 1 < d)
    (hst : s ⊆ t) (hH : 0 < H) (hr : r ∈ s) (hHr : H < r)
    (hnew : ∀ d ∈ t \ s, H < d) :
    Submodule.span ℝ
      (Set.range (fun d => innovation (dictionary s ⊓ headNull H) (addedFamily s t r d))) =
      (dictionary t ⊓ headNull H) ⊓ (dictionary s ⊓ headNull H)ᗮ := by
  rw [innovation_span, tangent_extension s t H r hs ht hst hH hr hHr hnew]

end RiemannResearch.RH.QResidueHeadExtension
