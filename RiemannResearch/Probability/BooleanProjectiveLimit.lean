import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order
import RiemannResearch.Probability.DeterminantalProcess

/-!
# Projective extension for Boolean coordinates

Finite Boolean cylinders are compact and closed. A decreasing sequence with
empty intersection is eventually empty, which gives countable additivity of
the projective content and its Caratheodory extension. This works for arbitrary
index sets. The measure construction follows Mathlib's
Probability/Kernel/IonescuTulcea/Traj.lean; the compact-cylinder argument is the
finite-discrete case of Kolmogorov extension. The final theorem transfers all
finite determinantal correlations to the resulting measure.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace RiemannResearch.Probability.BooleanProjective

variable {α : Type*}

theorem isClosed_bool_cylinder (I : Finset α) (S : Set (I → Bool)) :
    IsClosed (cylinder (α := fun _ : α => Bool) I S) := by
  change IsClosed ((fun x : α → Bool => fun i : I => x i.1) ⁻¹' S)
  exact (Set.toFinite S).isClosed.preimage (continuous_pi fun i => continuous_apply i.1)

theorem bool_projectiveContent_tendsto_zero
    {P : (I : Finset α) → Measure (I → Bool)} (hP : IsProjectiveMeasureFamily (α := fun _ : α => Bool) P)
    {A : ℕ → Set (α → Bool)}
    (hA : ∀ n, A n ∈ measurableCylinders (fun _ : α => Bool))
    (hanti : Antitone A) (hempty : ⋂ n, A n = ∅) :
    Tendsto (fun n => projectiveFamilyContent hP (A n)) atTop (𝓝 0) := by
  have hclosed (n : ℕ) : IsClosed (A n) := by
    obtain ⟨I, S, hS, hEq⟩ := (mem_measurableCylinders _).mp (hA n)
    rw [hEq]
    exact isClosed_bool_cylinder I S
  have hdir : Directed (fun s t : Set (α → Bool) => s ⊇ t) A := by
    intro i j
    exact ⟨max i j, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩
  obtain ⟨N, hN⟩ := isCompact_univ.elim_directed_family_closed A hclosed
    (by simpa using hempty) hdir
  have hN' : A N = ∅ := by simpa using hN
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : A n = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have : x ∈ A N := hanti hn hx
    simpa [hN'] using this
  simp [hn']

theorem bool_projectiveContent_sigmaSubadditive
    {P : (I : Finset α) → Measure (I → Bool)}
    [∀ I, IsFiniteMeasure (P I)] (hP : IsProjectiveMeasureFamily (α := fun _ : α => Bool) P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  refine addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent hP) (fun _ _ => projectiveFamilyContent_ne_top hP) ?_
    hf hf_Union hf'
  exact fun s hs hanti hempty => bool_projectiveContent_tendsto_zero hP hs hanti hempty

def boolProjectiveLimit
    {P : (I : Finset α) → Measure (I → Bool)}
    [∀ I, IsFiniteMeasure (P I)] (hP : IsProjectiveMeasureFamily (α := fun _ : α => Bool) P) :
    Measure (α → Bool) :=
  (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (bool_projectiveContent_sigmaSubadditive hP)

theorem isProjectiveLimit_boolProjectiveLimit
    {P : (I : Finset α) → Measure (I → Bool)}
    [∀ I, IsFiniteMeasure (P I)] (hP : IsProjectiveMeasureFamily (α := fun _ : α => Bool) P) :
    IsProjectiveLimit (α := fun _ : α => Bool) (boolProjectiveLimit hP) P := by
  intro I
  ext s hs
  rw [Measure.map_apply (measurable_pi_lambda _ fun i => measurable_pi_apply i.1) hs]
  change boolProjectiveLimit hP (cylinder (α := fun _ : α => Bool) I s) = _
  rw [boolProjectiveLimit, AddContent.measure_eq, projectiveFamilyContent_cylinder hP hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

instance isProbabilityMeasure_boolProjectiveLimit
    {P : (I : Finset α) → Measure (I → Bool)}
    [∀ I, IsProbabilityMeasure (P I)] (hP : IsProjectiveMeasureFamily (α := fun _ : α => Bool) P) :
    IsProbabilityMeasure (boolProjectiveLimit hP) :=
  (isProjectiveLimit_boolProjectiveLimit hP).isProbabilityMeasure

open RiemannResearch.Probability.DPP

/-- Every finite marginal is a DPP for the restricted kernel, so the projective
limit is an actual DPP for the full kernel. No countability is needed. -/
theorem boolProjectiveLimit_isDPP
    {P : (I : Finset α) → Measure (I → Bool)}
    [∀ I, IsProbabilityMeasure (P I)] (hP : IsProjectiveMeasureFamily (α := fun _ : α => Bool) P)
    (K : α → α → ℝ)
    (hDPP : ∀ I, IsDPP (P I) (fun x => {i | x i = true})
      (fun i j : I => K i.1 j.1)) :
    IsDPP (boolProjectiveLimit hP) (fun x => {i | x i = true}) K := by
  constructor
  · intro i
    exact (measurableSet_singleton true).preimage (measurable_pi_apply i)
  · intro n e
    let I : Finset α := Finset.univ.map e
    let eI : Fin n ↪ I :=
      ⟨fun i => ⟨e i, by simp [I]⟩,
        fun i j hij => e.injective (congrArg Subtype.val hij)⟩
    let E : Set (I → Bool) := {x | ∀ i, x (eI i) = true}
    have hE : MeasurableSet E := (Set.toFinite E).measurableSet
    change (boolProjectiveLimit hP (cylinder (α := fun _ : α => Bool) I E)).toReal = _
    rw [(isProjectiveLimit_boolProjectiveLimit hP).measure_cylinder I hE]
    exact (hDPP I).correlation n eI

end RiemannResearch.Probability.BooleanProjective
