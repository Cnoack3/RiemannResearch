import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.Tauto

/-!
# Finite deletion for continuous biorthogonal dictionaries

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Sections 4 and 5. These are general normed-space results for an explicitly
supplied continuous biorthogonal dictionary. No assertion about an infinite
coordinate projection is assumed or inferred.
-/

namespace RiemannResearch.Analysis

noncomputable section

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

def dictionarySpan (h : ι → E) (S : Set ι) : Submodule ℝ E :=
  Submodule.span ℝ (h '' S)

def dictionaryClosure (h : ι → E) (S : Set ι) : Submodule ℝ E :=
  (dictionarySpan h S).topologicalClosure

theorem dictionaryClosure_mono (h : ι → E) {S T : Set ι} (hST : S ⊆ T) :
    dictionaryClosure h S ≤ dictionaryClosure h T := by
  apply Submodule.topologicalClosure_mono
  exact Submodule.span_mono (Set.image_mono hST)

/-- Continuous biorthogonal coordinates also imply algebraic independence. -/
theorem continuous_biorthogonal_linearIndependent
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0) :
    LinearIndependent ℝ h := by
  classical
  apply linearIndependent_iff'.2
  intro s c hc i hi
  have he := congrArg (L i) hc
  simpa [map_sum, map_smul, hbi, hi] using he

/-- Norm convergence forces every individual continuous coefficient to its
target value; no convergence of the formal expansion is asserted. -/
theorem continuous_coordinate_tendsto
    (l : E →L[ℝ] ℝ) (F : ℕ → E) (x : E)
    (hF : Filter.Tendsto F Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => l (F n)) Filter.atTop (nhds (l x)) :=
  l.continuous.continuousAt.tendsto.comp hF

/-- A continuous coefficient vanishes throughout the closed span when its
dictionary index is omitted. -/
theorem biorthogonal_coordinate_zero_of_omitted
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (S : Set ι) (i : ι) (hi : i ∉ S)
    {x : E} (hx : x ∈ dictionaryClosure h S) : L i x = 0 := by
  classical
  have hspan : ∀ y ∈ dictionarySpan h S, L i y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        have hij : i ≠ j := by intro he; exact hi (he.symm ▸ hj)
        simp [hbi, hij]
    | zero => simp
    | add a b ha hb iha ihb => simp [map_add, iha, ihb]
    | smul c a ha iha => simp [map_smul, iha]
  exact (closure_minimal hspan
    (isClosed_eq (L i).continuous continuous_const)) hx

/-- Every approximating subfamily contains every nonzero target coordinate. -/
theorem biorthogonal_nonzero_target_mem
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (S : Set ι) {x : E} (hx : x ∈ dictionaryClosure h S)
    (i : ι) (hi : L i x ≠ 0) : i ∈ S := by
  by_contra hn
  exact hi (biorthogonal_coordinate_zero_of_omitted h L hbi S i hn hx)

/-- A zero target coordinate may be removed by a continuous rank-one map. -/
theorem dictionary_delete_one_of_coordinate
    (h : ι → E) (l : E →L[ℝ] ℝ) (i : ι)
    (hbi : ∀ j, l (h j) = if i = j then 1 else 0)
    (S : Set ι) {x : E}
    (hx : x ∈ dictionaryClosure h S) (hzero : l x = 0) :
    x ∈ dictionaryClosure h (S \ {i}) := by
  classical
  let P : E →ₗ[ℝ] E := LinearMap.id - (l).toLinearMap.smulRight (h i)
  have hP : ∀ y : E, P y = y - l y • h i := by intro y; rfl
  have hPc : Continuous P := by
    change Continuous (fun y : E => y - l y • h i)
    exact continuous_id.sub ((l).continuous.smul continuous_const)
  have hspan : ∀ y ∈ dictionarySpan h S,
      P y ∈ dictionarySpan h (S \ {i}) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        by_cases hij : i = j
        · subst j
          simp [hP, hbi]
        · have hpj : P (h j) = h j := by simp [hP, hbi, hij]
          rw [hpj]
          exact Submodule.subset_span ⟨j, ⟨hj, by simpa [eq_comm] using hij⟩, rfl⟩
    | zero => simpa using (dictionarySpan h (S \ {i})).zero_mem
    | add a b ha hb iha ihb =>
        simpa only [map_add] using (dictionarySpan h (S \ {i})).add_mem iha ihb
    | smul c a ha iha =>
        simpa only [map_smul] using (dictionarySpan h (S \ {i})).smul_mem c iha
  have hsub : (dictionarySpan h S : Set E) ⊆
      P ⁻¹' (dictionaryClosure h (S \ {i}) : Set E) := by
    intro y hy
    exact (dictionarySpan h (S \ {i})).le_topologicalClosure (hspan y hy)
  have hPx := (closure_minimal hsub
    ((dictionarySpan h (S \ {i})).isClosed_topologicalClosure.preimage hPc)) hx
  change P x ∈ dictionaryClosure h (S \ {i}) at hPx
  have hfix : P x = x := by rw [hP, hzero, zero_smul, sub_zero]
  rw [hfix] at hPx
  exact hPx


/-- The rank-one deletion theorem specialized to a biorthogonal family. -/
theorem biorthogonal_delete_one
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (S : Set ι) (i : ι) {x : E}
    (hx : x ∈ dictionaryClosure h S) (hzero : L i x = 0) :
    x ∈ dictionaryClosure h (S \ {i}) :=
  dictionary_delete_one_of_coordinate h (L i) i (hbi i) S hx hzero

theorem biorthogonal_delete_one_iff
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (S : Set ι) (i : ι) (x : E) :
    x ∈ dictionaryClosure h (S \ {i}) ↔
      x ∈ dictionaryClosure h S ∧ L i x = 0 := by
  constructor
  · intro hx
    refine ⟨dictionaryClosure_mono h Set.diff_subset hx, ?_⟩
    exact biorthogonal_coordinate_zero_of_omitted h L hbi (S \ {i}) i
      (by simp) hx
  · rintro ⟨hx, hz⟩
    exact biorthogonal_delete_one h L hbi S i hx hz

/-- Removing finitely many indices is possible precisely when all their target
coefficients vanish. -/
theorem biorthogonal_delete_finite_iff
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (S : Set ι) (J : Finset ι) (x : E) :
    x ∈ dictionaryClosure h (S \ (J : Set ι)) ↔
      x ∈ dictionaryClosure h S ∧ ∀ i ∈ J, L i x = 0 := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
      have hsets : S \ (↑(insert i J) : Set ι) = (S \ (J : Set ι)) \ {i} := by
        ext j
        simp only [Set.mem_diff, Finset.mem_coe, Finset.mem_insert,
          Set.mem_singleton_iff]
        tauto
      rw [hsets, biorthogonal_delete_one_iff h L hbi, ih]
      simp only [Finset.mem_insert, forall_eq_or_imp]
      tauto

/-- Inclusion minimality is stated for approximation of one specified target,
not density of the whole ambient space. -/
def IsMinimalTargetFamily (h : ι → E) (x : E) (S : Set ι) : Prop :=
  x ∈ dictionaryClosure h S ∧
    ∀ T : Set ι, T ⊆ S → x ∈ dictionaryClosure h T → S ⊆ T

/-- A minimal approximating subfamily, if it exists, is uniquely determined by
the support of the continuous target coefficients. -/
theorem biorthogonal_minimal_family_eq_support
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (x : E) (S : Set ι) (hmin : IsMinimalTargetFamily h x S) :
    S = {i | L i x ≠ 0} := by
  ext i
  constructor
  · intro hi hz
    have hdel := biorthogonal_delete_one h L hbi S i hmin.1 hz
    exact (hmin.2 (S \ {i}) Set.diff_subset hdel hi).2 (by simp)
  · intro hi
    exact biorthogonal_nonzero_target_mem h L hbi S hmin.1 i hi

/-- If the nonzero-coefficient support succeeds, it is minimal. This does not
assert that this support actually succeeds. -/
theorem biorthogonal_support_minimal_iff
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (x : E) :
    IsMinimalTargetFamily h x {i | L i x ≠ 0} ↔
      x ∈ dictionaryClosure h {i | L i x ≠ 0} := by
  constructor
  · exact And.left
  · intro hx
    refine ⟨hx, ?_⟩
    intro T hT hxT i hi
    exact biorthogonal_nonzero_target_mem h L hbi T hxT i hi

theorem biorthogonal_exists_minimal_iff_support_approximates
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (x : E) :
    (∃ S, IsMinimalTargetFamily h x S) ↔
      x ∈ dictionaryClosure h {i | L i x ≠ 0} := by
  constructor
  · rintro ⟨S, hS⟩
    rw [← biorthogonal_minimal_family_eq_support h L hbi x S hS]
    exact hS.1
  · intro hx
    exact ⟨_, (biorthogonal_support_minimal_iff h L hbi x).2 hx⟩

/-- Every dictionary element remains indispensable for density of the whole
space, including elements whose coefficient at a particular target vanishes. -/
theorem biorthogonal_deleted_generator_not_mem
    (h : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hbi : ∀ i j, L i (h j) = if i = j then 1 else 0)
    (S : Set ι) (i : ι) :
    h i ∉ dictionaryClosure h (S \ {i}) := by
  classical
  intro hx
  have hz := biorthogonal_coordinate_zero_of_omitted h L hbi (S \ {i}) i
    (by simp) hx
  simpa [hbi] using hz

end
end RiemannResearch.Analysis
