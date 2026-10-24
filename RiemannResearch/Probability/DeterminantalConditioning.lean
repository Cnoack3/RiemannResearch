import RiemannResearch.Probability.DeterminantalProcess
import RiemannResearch.LinearAlgebra.OptionSchurDeterminant

/-!
# Exact finite inclusion conditioning for determinantal laws

Source: sixth transfer program, 24 October 2026; the finite conditioning
identity is the Schur-complement formula discussed in Kulesza--Taskar,
https://arxiv.org/abs/1207.6083. Conditioning mass positivity is explicit.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace RiemannResearch.Probability.DPP

variable {ι α Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

theorem IsDPP.correlation_fintype (h : IsDPP μ X K) (e : ι ↪ α) :
    μ.real {ω | ∀ i, e i ∈ X ω} = (Matrix.of (fun i j => K (e i) (e j))).det := by
  let q : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hevent : {ω | ∀ j, e (q j) ∈ X ω} = {ω | ∀ i, e i ∈ X ω} := by
    ext ω
    constructor
    · intro hh i
      obtain ⟨j, rfl⟩ := q.surjective i
      exact hh j
    · exact fun hh j => hh (q j)
  have hh := h.correlation (Fintype.card ι) (q.toEmbedding.trans e)
  change μ.real {ω | ∀ j, e (q j) ∈ X ω} =
    ((Matrix.of (fun i j => K (e i) (e j))).submatrix q q).det at hh
  rw [hevent, Matrix.det_submatrix_equiv_self] at hh
  exact hh

variable {L : Option ι → Option ι → ℝ} {Y : Ω → Set (Option ι)}

theorem IsDPP.option_head_inclusion (h : IsDPP μ Y L) :
    μ.real {ω | ∀ i, some i ∈ Y ω} = (Matrix.of (fun i j => L (some i) (some j))).det :=
  h.correlation_fintype ⟨some, by intro i j hij; exact Option.some.inj hij⟩

theorem IsDPP.option_all_inclusion (h : IsDPP μ Y L) :
    μ.real {ω | ∀ i, i ∈ Y ω} = (Matrix.of L).det :=
  h.correlation_fintype (Function.Embedding.refl _)

theorem IsDPP.option_conditioned_vacancy (h : IsDPP μ Y L)
    (hp : 0 < μ.real {ω | ∀ i, some i ∈ Y ω}) :
    μ.real {ω | (∀ i, some i ∈ Y ω) ∧ none ∉ Y ω} /
      μ.real {ω | ∀ i, some i ∈ Y ω} =
      1 - (Matrix.of L).det / (Matrix.of (fun i j => L (some i) (some j))).det := by
  have hsub : {ω | ∀ i : Option ι, i ∈ Y ω} ⊆ {ω | ∀ i, some i ∈ Y ω} :=
    fun ω hω i => hω (some i)
  have hevent : {ω | (∀ i, some i ∈ Y ω) ∧ none ∉ Y ω} =
      {ω | ∀ i, some i ∈ Y ω} \ {ω | ∀ i : Option ι, i ∈ Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨hh, ht⟩
      exact ⟨hh, fun h => ht (h none)⟩
    · rintro ⟨hh, hall⟩
      refine ⟨hh, ?_⟩
      intro ht
      exact hall (fun i => by cases i with | none => exact ht | some i => exact hh i)
  have hm : MeasurableSet {ω | ∀ i : Option ι, i ∈ Y ω} := by
    convert MeasurableSet.iInter (fun i : Option ι => h.measurable_occupancy i) using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hevent, measureReal_sdiff hsub hm,
    sub_div, div_self (ne_of_gt hp), h.option_all_inclusion, h.option_head_inclusion]

theorem IsDPP.option_conditioned_vacancy_schur (h : IsDPP μ Y L)
    (hp : 0 < μ.real {ω | ∀ i, some i ∈ Y ω}) :
    μ.real {ω | (∀ i, some i ∈ Y ω) ∧ none ∉ Y ω} /
      μ.real {ω | ∀ i, some i ∈ Y ω} =
      1 - L none none + ∑ i, L none (some i) *
        (∑ j, ((Matrix.of (fun i j => L (some i) (some j)))⁻¹) i j * L (some j) none) := by
  have hd : (Matrix.of (fun i j => L (some i) (some j))).det ≠ 0 := by
    rw [← h.option_head_inclusion]
    exact ne_of_gt hp
  have hblock : (Matrix.of L).submatrix some some =
      Matrix.of (fun i j => L (some i) (some j)) := by
    ext i j
    rfl
  have hunit : IsUnit ((Matrix.of L).submatrix some some).det := by
    rw [hblock]
    exact isUnit_iff_ne_zero.mpr hd
  have hschur : (Matrix.of L).det =
      (Matrix.of (fun i j => L (some i) (some j))).det *
        (L none none - ∑ i, L none (some i) *
          (∑ j, ((Matrix.of (fun i j => L (some i) (some j)))⁻¹) i j * L (some j) none)) := by
    simpa only [hblock, Matrix.of_apply] using
      RiemannResearch.LinearAlgebra.det_option_schur (Matrix.of L) hunit
  rw [h.option_conditioned_vacancy hp, hschur, mul_div_cancel_left₀ _ hd]
  ring

end RiemannResearch.Probability.DPP
