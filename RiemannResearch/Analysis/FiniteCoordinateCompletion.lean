import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Choose

/-!
# Completion by finite coordinate images

Source: the user-provided categorical CRT note, 2026-11-14, Theorem C.
The completion consists of all data realized on every finite set of coordinates.
For discrete coordinates it is exactly the closure of the original image.
This construction supplies compact compatible data, not an analytic energy bound.
-/

namespace FiniteCoordinate

variable {X I : Type*} {Y : I → Type*} (q : (i : I) → X → Y i)

def Compatible (b : (i : I) → Y i) : Prop :=
  ∀ F : Finset I, ∃ x : X, ∀ i ∈ F, q i x = b i

abbrev Completion := {b : (i : I) → Y i // Compatible q b}

def toCompletion (x : X) : Completion q :=
  ⟨fun i => q i x, fun _ => ⟨x, fun _ _ => rfl⟩⟩

/-- The actual image of a finite coordinate map. -/
abbrev Image (F : Finset I) :=
  {a : (i : F) → Y i.val // ∃ x : X, ∀ i : F, q i.val x = a i}

/-- Coherence under all restrictions between finite coordinate images. -/
def Coherent (a : (F : Finset I) → Image q F) : Prop :=
  ∀ (F G : Finset I) (h : F ⊆ G) (i : F),
    (a G).val ⟨i.val, h i.property⟩ = (a F).val i

abbrev ImageLimit := {a : (F : Finset I) → Image q F // Coherent q a}

def toImageLimit (b : Completion q) : ImageLimit q :=
  ⟨fun F => ⟨fun i => b.val i.val, by
      obtain ⟨x, hx⟩ := b.property F
      exact ⟨x, fun i => hx i.val i.property⟩⟩,
    fun _ _ _ _ => rfl⟩

def fromImageLimit (a : ImageLimit q) : Completion q := by
  classical
  refine ⟨fun i => (a.val {i}).val ⟨i, Finset.mem_singleton_self i⟩, ?_⟩
  intro F
  obtain ⟨x, hx⟩ := (a.val F).property
  refine ⟨x, fun i hi => ?_⟩
  exact (hx ⟨i, hi⟩).trans
    (a.property {i} F (Finset.singleton_subset_iff.mpr hi) ⟨i, Finset.mem_singleton_self i⟩)

/-- The completion is the inverse limit of its actual finite images, with
restriction coherence made explicit. -/
def completionEquivImageLimit : Completion q ≃ ImageLimit q where
  toFun := toImageLimit q
  invFun := fromImageLimit q
  left_inv b := by
    apply Subtype.ext
    funext i
    rfl
  right_inv a := by
    classical
    apply Subtype.ext
    funext F
    apply Subtype.ext
    funext i
    exact (a.property {i.val} F (Finset.singleton_subset_iff.mpr i.property)
      ⟨i.val, Finset.mem_singleton_self i.val⟩).symm

def completionHomeomorphImageLimit [∀ i, TopologicalSpace (Y i)] :
    Completion q ≃ₜ ImageLimit q where
  toEquiv := completionEquivImageLimit q
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro F
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply i.val).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hF : Continuous (fun a : ImageLimit q => a.val {i}) :=
      (continuous_apply {i}).comp continuous_subtype_val
    exact (continuous_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset I))).comp
      (continuous_subtype_val.comp hF)

def PairwiseCompatible (b : (i : I) → Y i) : Prop :=
  ∀ i j, ∃ x : X, q i x = b i ∧ q j x = b j

/-- Hereditary finite CRT for the actual binary coordinate images. The empty
finite set clause supplies nonemptiness of the original space. -/
def HasFiniteCRT : Prop :=
  ∀ (F : Finset I) (b : (i : I) → Y i),
    (∀ i ∈ F, ∀ j ∈ F, ∃ x : X, q i x = b i ∧ q j x = b j) →
      ∃ x : X, ∀ i ∈ F, q i x = b i

theorem compatible_iff_pairwise (h : HasFiniteCRT q) (b : (i : I) → Y i) :
    Compatible q b ↔ PairwiseCompatible q b := by
  classical
  constructor
  · intro hb i j
    obtain ⟨x, hx⟩ := hb {i, j}
    exact ⟨x, hx i (by simp), hx j (by simp)⟩
  · intro hb F
    exact h F b (fun i _ j _ => hb i j)

def completionHomeomorphMatching [∀ i, TopologicalSpace (Y i)]
    (h : HasFiniteCRT q) : Completion q ≃ₜ {b // PairwiseCompatible q b} :=
  Homeomorph.setCongr (Set.ext (fun b => compatible_iff_pairwise q h b))

/-- Any coordinate-compatible algebraic operation preserves the completion.
This includes all finitary operations of an algebraic signature. -/
theorem compatible_operation {K : Type*}
    (opX : (K → X) → X) (opY : (i : I) → (K → Y i) → Y i)
    (hop : ∀ (i : I) (x : K → X), q i (opX x) = opY i (fun k => q i (x k)))
    (a : K → ((i : I) → Y i)) (ha : ∀ k, Compatible q (a k)) :
    Compatible q (fun i => opY i (fun k => a k i)) := by
  classical
  intro F
  choose x hx using fun k => ha k F
  refine ⟨opX x, ?_⟩
  intro i hi
  rw [hop]
  congr 1
  funext k
  exact hx k i hi

def completionOperation {K : Type*}
    (opX : (K → X) → X) (opY : (i : I) → (K → Y i) → Y i)
    (hop : ∀ (i : I) (x : K → X), q i (opX x) = opY i (fun k => q i (x k)))
    (a : K → Completion q) : Completion q :=
  ⟨fun i => opY i (fun k => (a k).val i),
    compatible_operation q opX opY hop (fun k => (a k).val) (fun k => (a k).property)⟩

theorem toCompletion_operation {K : Type*}
    (opX : (K → X) → X) (opY : (i : I) → (K → Y i) → Y i)
    (hop : ∀ (i : I) (x : K → X), q i (opX x) = opY i (fun k => q i (x k)))
    (x : K → X) :
    toCompletion q (opX x) =
      completionOperation q opX opY hop (fun k => toCompletion q (x k)) :=
  Subtype.ext (funext (fun i => hop i x))

theorem continuous_completionOperation [∀ i, TopologicalSpace (Y i)] {K : Type*}
    (opX : (K → X) → X) (opY : (i : I) → (K → Y i) → Y i)
    (hop : ∀ (i : I) (x : K → X), q i (opX x) = opY i (fun k => q i (x k)))
    (hcontinuous : ∀ i, Continuous (opY i)) :
    Continuous (completionOperation q opX opY hop) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply (hcontinuous i).comp
  apply continuous_pi
  intro k
  exact (continuous_apply i).comp (continuous_subtype_val.comp (continuous_apply k))

theorem compatible_iff_mem_closure [∀ i, TopologicalSpace (Y i)]
    [∀ i, DiscreteTopology (Y i)] (b : (i : I) → Y i) :
    Compatible q b ↔ b ∈ closure (Set.range (fun x : X => fun i => q i x)) := by
  classical
  constructor
  · intro hb
    rw [mem_closure_iff]
    intro O hO hbO
    obtain ⟨F, U, hU, hsub⟩ := isOpen_pi_iff.mp hO b hbO
    obtain ⟨x, hx⟩ := hb F
    refine ⟨fun i => q i x, hsub ?_, ⟨x, rfl⟩⟩
    intro i hi
    change q i x ∈ U i
    rw [hx i hi]
    exact (hU i hi).2
  · intro hb F
    let O : Set ((i : I) → Y i) := (F : Set I).pi (fun i => {b i})
    have hO : IsOpen O := by
      apply isOpen_pi_iff.mpr
      intro a ha
      exact ⟨F, (fun i => {b i}),
        (fun i hi => ⟨isOpen_discrete _, ha i hi⟩), Set.Subset.rfl⟩
    have hbO : b ∈ O := fun _ _ => rfl
    obtain ⟨a, ha, x, rfl⟩ := mem_closure_iff.mp hb O hO hbO
    exact ⟨x, fun i hi => ha i hi⟩

theorem isClosed_compatible [∀ i, TopologicalSpace (Y i)]
    [∀ i, DiscreteTopology (Y i)] : IsClosed {b | Compatible q b} := by
  have h : {b | Compatible q b} = closure (Set.range (fun x : X => fun i => q i x)) := by
    ext b
    exact compatible_iff_mem_closure q b
  rw [h]
  exact isClosed_closure

instance completionCompactSpace [∀ i, TopologicalSpace (Y i)]
    [∀ i, DiscreteTopology (Y i)] [∀ i, CompactSpace (Y i)] :
    CompactSpace (Completion q) :=
  isCompact_iff_compactSpace.mp (isClosed_compatible q).isCompact

theorem toCompletion_denseRange [∀ i, TopologicalSpace (Y i)]
    [∀ i, DiscreteTopology (Y i)] : DenseRange (toCompletion q) := by
  intro b
  rw [mem_closure_iff]
  intro O hO hbO
  obtain ⟨U, hU, hUO⟩ := isOpen_induced_iff.mp hO
  have hbU : b.val ∈ U := by
    change b ∈ Subtype.val ⁻¹' U
    rwa [hUO]
  obtain ⟨a, haU, x, rfl⟩ :=
    mem_closure_iff.mp ((compatible_iff_mem_closure q b.val).mp b.property) U hU hbU
  refine ⟨toCompletion q x, ?_, ⟨x, rfl⟩⟩
  rw [← hUO]
  exact haU

end FiniteCoordinate
