/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Simultaneous transporters of labelled subgroup families

This module isolates the group-theoretic torsor statement needed by the
strong-E8 incidence program. A simultaneous transporter carries every
member of one labelled subgroup family to the corresponding member of a
second family. Once one transporter is chosen, every other transporter is
obtained uniquely by right multiplication by the intersection of the source
normalizers.

The labels matter: this is not the setwise stabilizer of an unordered family.
In the E8 application the unlike subsystem types D8, A2^4, and A4^2 must not
be treated as mutually conjugate. The intended labelled transporters are
between isomorphic descended tori or Borel frames.

Source: user-provided strong-E8 solvable-incidence argument (14 August 2026);
the source supports the statement and its application.
-/

namespace Subgroup

universe u v

variable {G : Type u} {ι : Type v} [Group G]

/-- Elements simultaneously conjugating each member of one labelled subgroup
family to the corresponding member of another family. -/
def simultaneousTransporter (S T : ι → Subgroup G) : Set G :=
  {g | ∀ i x, x ∈ S i ↔ g * x * g⁻¹ ∈ T i}

/-- The stabilizer of a labelled subgroup family under simultaneous
conjugation: the intersection of its normalizers. -/
def simultaneousNormalizer (S : ι → Subgroup G) : Subgroup G :=
  ⨅ i, Subgroup.normalizer (S i : Set G)

theorem mem_simultaneousTransporter_iff
    {S T : ι → Subgroup G} {g : G} :
    g ∈ simultaneousTransporter S T ↔
      ∀ i x, x ∈ S i ↔ g * x * g⁻¹ ∈ T i :=
  Iff.rfl

theorem mem_simultaneousNormalizer_iff
    {S : ι → Subgroup G} {g : G} :
    g ∈ simultaneousNormalizer S ↔
      ∀ i, g ∈ Subgroup.normalizer (S i : Set G) := by
  exact Subgroup.mem_iInf

/-- If every member of the family is self-normalizing, its simultaneous
normalizer is their intersection. This is the abstract Borel-frame case. -/
theorem simultaneousNormalizer_eq_iInf_of_selfNormalizing
    (S : ι → Subgroup G)
    (hself : ∀ i, Subgroup.normalizer (S i : Set G) = S i) :
    simultaneousNormalizer S = ⨅ i, S i := by
  simp only [simultaneousNormalizer, hself]

/-- Relative to one chosen simultaneous transporter, every other transporter
differs from it on the right by an element of the common source normalizer. -/
theorem mem_simultaneousTransporter_iff_inv_mul_mem
    {S T : ι → Subgroup G} {g₀ g : G}
    (hg₀ : g₀ ∈ simultaneousTransporter S T) :
    g ∈ simultaneousTransporter S T ↔
      g₀⁻¹ * g ∈ simultaneousNormalizer S := by
  constructor
  · intro hg
    rw [mem_simultaneousNormalizer_iff]
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    let n := g₀⁻¹ * g
    have hx₀ := hg₀ i (n * x * n⁻¹)
    have hx₀' :
        n * x * n⁻¹ ∈ S i ↔ g * x * g⁻¹ ∈ T i := by
      simpa [n, mul_assoc] using hx₀
    exact (hg i x).trans hx₀'.symm
  · intro hn i x
    have hni :
        g₀⁻¹ * g ∈ Subgroup.normalizer (S i : Set G) :=
      (mem_simultaneousNormalizer_iff.mp hn) i
    have hnx :
        x ∈ S i ↔ (g₀⁻¹ * g) * x * (g₀⁻¹ * g)⁻¹ ∈ S i :=
      (Subgroup.mem_normalizer_iff.mp hni) x
    have hx₀ :=
      hg₀ i ((g₀⁻¹ * g) * x * (g₀⁻¹ * g)⁻¹)
    have hx₀' :
        (g₀⁻¹ * g) * x * (g₀⁻¹ * g)⁻¹ ∈ S i ↔
          g * x * g⁻¹ ∈ T i := by
      simpa [mul_assoc] using hx₀
    exact hnx.trans hx₀'

theorem simultaneousTransporter_eq_rightCoset
    {S T : ι → Subgroup G} {g₀ : G}
    (hg₀ : g₀ ∈ simultaneousTransporter S T) :
    simultaneousTransporter S T =
      (fun n : G => g₀ * n) '' (simultaneousNormalizer S : Set G) := by
  ext g
  constructor
  · intro hg
    refine ⟨g₀⁻¹ * g, ?_, ?_⟩
    · exact (mem_simultaneousTransporter_iff_inv_mul_mem hg₀).mp hg
    · simp
  · rintro ⟨n, hn, rfl⟩
    apply (mem_simultaneousTransporter_iff_inv_mul_mem hg₀).mpr
    change g₀⁻¹ * (g₀ * n) ∈ (simultaneousNormalizer S : Set G)
    simpa only [inv_mul_cancel_left] using hn

/-- The explicit torsor equivalence supplied by a chosen base transporter. -/
def simultaneousTransporterEquiv
    {S T : ι → Subgroup G} {g₀ : G}
    (hg₀ : g₀ ∈ simultaneousTransporter S T) :
    simultaneousNormalizer S ≃
      {g : G // g ∈ simultaneousTransporter S T} where
  toFun n := ⟨g₀ * n, by
    apply (mem_simultaneousTransporter_iff_inv_mul_mem hg₀).mpr
    simpa only [inv_mul_cancel_left] using n.property⟩
  invFun g := ⟨g₀⁻¹ * g, by
    exact (mem_simultaneousTransporter_iff_inv_mul_mem hg₀).mp g.property⟩
  left_inv n := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

end Subgroup
