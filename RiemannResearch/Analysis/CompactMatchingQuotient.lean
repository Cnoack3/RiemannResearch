import RiemannResearch.Analysis.CompactConstraintEnergy
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Compact quotient and matching-space reconstruction

Source: the user's categorical CRT and energy note, 14 November 2026,
Theorem C. A continuous map from a compact space to a Hausdorff space identifies
its kernel-relation quotient homeomorphically with its target when surjective.
Applied to coordinate maps, finite CRT and compactness identify that target
with the space of all pairwise compatible tuples.

The quotient uses its quotient topology; the matching space uses the subspace
topology inherited from the full product. No countability assumption is needed.
The RH consumer is the topological realization of compatible arithmetic data.
This qualitative reconstruction supplies no analytic energy bound.
-/

noncomputable section

namespace CompactConstraintEnergy

/-- A compact-to-Hausdorff continuous surjection gives a homeomorphism from
the quotient by any equivalence relation equal to its kernel relation. -/
def quotientHomeomorph
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (s : Setoid X) (f : X → Y) (hf : Continuous f)
    (hsurj : Function.Surjective f)
    (hker : ∀ x y, s.r x y ↔ f x = f y) :
    Quotient s ≃ₜ Y := by
  let lift : Quotient s → Y := Quotient.lift f (fun x y h => (hker x y).mp h)
  have hinj : Function.Injective lift := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b hab
    exact Quotient.sound ((hker a b).mpr hab)
  have hsurj' : Function.Surjective lift := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Quotient.mk s x, rfl⟩
  let e : Quotient s ≃ Y := Equiv.ofBijective lift ⟨hinj, hsurj'⟩
  have hcont : Continuous e := continuous_quot_lift _ hf
  exact hcont.homeoOfEquivCompactToT2

@[simp] theorem quotientHomeomorph_mk
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (s : Setoid X) (f : X → Y) (hf : Continuous f)
    (hsurj : Function.Surjective f)
    (hker : ∀ x y, s.r x y ↔ f x = f y) (x : X) :
    quotientHomeomorph s f hf hsurj hker (Quotient.mk s x) = f x := rfl

variable {X I : Type*} {Y : I → Type*}

/-- Pairwise matching data, using actual binary images. -/
abbrev MatchingSpace (q : ∀ i, X → Y i) :=
  {b : ∀ i, Y i // ∀ i j, ∃ x, q i x = b i ∧ q j x = b j}

/-- The intersection of all coordinate kernel relations. -/
def commonKernel (q : ∀ i, X → Y i) : Setoid X :=
  Setoid.ker (fun x i => q i x)

theorem commonKernel_iff (q : ∀ i, X → Y i) (x y : X) :
    (commonKernel q).r x y ↔ ∀ i, q i x = q i y := by
  change (fun i => q i x) = (fun i => q i y) ↔ _
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- The canonical coordinate map, with its compatibility certificate. -/
def toMatching (q : ∀ i, X → Y i) (x : X) : MatchingSpace q :=
  ⟨fun i => q i x, fun _ _ => ⟨x, rfl, rfl⟩⟩

variable [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]

theorem continuous_toMatching (q : ∀ i, X → Y i)
    (hq : ∀ i, Continuous (q i)) : Continuous (toMatching q) :=
  (continuous_pi hq).subtype_mk _

variable [CompactSpace X] [∀ i, T2Space (Y i)]

/-- Finite CRT is enough for exact topological reconstruction from an
arbitrary compatible family on a compact space. -/
def matchingQuotientHomeomorph (q : ∀ i, X → Y i)
    (hq : ∀ i, Continuous (q i))
    (hcrt : ∀ b : (∀ i, Y i), ∀ F : Finset I,
      (∀ i ∈ F, ∀ j ∈ F, ∃ x, q i x = b i ∧ q j x = b j) →
      ∃ x, ∀ i ∈ F, q i x = b i) :
    Quotient (commonKernel q) ≃ₜ MatchingSpace q :=
  quotientHomeomorph (commonKernel q) (toMatching q) (continuous_toMatching q hq)
    (by
      intro b
      obtain ⟨x, hx⟩ := (exists_lift_iff_pairwise q hq b.val (hcrt b.val)).mpr b.property
      exact ⟨x, Subtype.ext (funext hx)⟩)
    (by
      intro x y
      change (fun i => q i x) = (fun i => q i y) ↔ toMatching q x = toMatching q y
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

@[simp] theorem matchingQuotientHomeomorph_mk (q : ∀ i, X → Y i)
    (hq : ∀ i, Continuous (q i))
    (hcrt : ∀ b : (∀ i, Y i), ∀ F : Finset I,
      (∀ i ∈ F, ∀ j ∈ F, ∃ x, q i x = b i ∧ q j x = b j) →
      ∃ x, ∀ i ∈ F, q i x = b i) (x : X) :
    matchingQuotientHomeomorph q hq hcrt (Quotient.mk (commonKernel q) x) =
      toMatching q x := rfl

end CompactConstraintEnergy
