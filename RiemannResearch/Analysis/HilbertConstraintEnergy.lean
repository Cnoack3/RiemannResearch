/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.HilbertConstraintReconstruction
import RiemannResearch.Analysis.FiniteSingularGramReconstruction
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Exact energy and duality for infinite Hilbert reconstruction

Source: user-provided `Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md`,
Theorem E. Finite energies are actual infima, with infinity for inconsistent
data, and are evaluated by the canonical finite Gram pseudoinverse. The
uniform bound remains a hypothesis for arithmetic applications.
-/

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

namespace RiemannResearch.Analysis.HilbertConstraintReconstruction

open FiniteHilbertGram

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
theorem norm_sq_le_iff_norm_le_sqrt (x : H) {C : ℝ} (hC : 0 ≤ C) :
    ‖x‖ ^ 2 ≤ C ↔ ‖x‖ ≤ Real.sqrt C := by
  constructor <;> intro h <;>
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg x]

/-- Finite subsystem optimum, including infinite cost for inconsistent data. -/
def finiteOptimum (u : ι → H) (b : ι → ℝ) (F : Finset ι) : ℝ≥0∞ :=
  finiteConstraintEnergy (fun i : F => u i) (fun i : F => b i)

theorem finiteOptimum_empty (u : ι → H) (b : ι → ℝ) :
    finiteOptimum u b ∅ = 0 := by
  apply le_antisymm _ bot_le
  apply iInf_le_of_le (0 : H)
  apply iInf_le_of_le (fun i => isEmptyElim i)
  simp

theorem finiteOptimum_mono (u : ι → H) (b : ι → ℝ) :
    Monotone (finiteOptimum u b) := by
  intro F G hFG
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  apply iInf_le_of_le x
  exact iInf_le _ (fun i : F => hx ⟨i, hFG i.property⟩)

/-- Exact finite optimum comparison is equivalent to bounded feasibility. -/
theorem finiteOptimum_le_ofReal_iff (u : ι → H) (b : ι → ℝ)
    (F : Finset ι) {C : ℝ} (hC : 0 ≤ C) :
    finiteOptimum u b F ≤ ENNReal.ofReal C ↔
      ∃ x : H, ‖x‖ ^ 2 ≤ C ∧ ∀ i ∈ F, inner ℝ (u i) x = b i := by
  classical
  let v : F → H := fun i => u i
  let d : F → ℝ := fun i => b i
  constructor
  · intro h
    have hb : ∃ c : F → ℝ, gram v c = d := by
      by_contra hb
      change finiteConstraintEnergy v d ≤ ENNReal.ofReal C at h
      rw [finiteConstraintEnergy_infeasible v d hb] at h
      exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
    refine ⟨gramMinimumVector v d, ?_, ?_⟩
    · have he : finiteOptimum u b F =
          ENNReal.ofReal (‖gramMinimumVector v d‖ ^ 2) := by
        rw [finiteOptimum, finiteConstraintEnergy_feasible _ _ hb,
          ← gramMinimumVector_energy v d hb]
      rw [he] at h
      have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hC] using hr
    · intro i hi
      exact gramMinimumVector_observation v d hb ⟨i, hi⟩
  · rintro ⟨x, hx, hb⟩
    apply iInf_le_of_le x
    apply iInf_le_of_le (fun i : F => hb i i.property)
    exact ENNReal.ofReal_le_ofReal hx

/-- Squared finite-coefficient dual bound. Subtype indexing makes every sum
finite and permits an arbitrary, including uncountable, dictionary. -/
def DualBound (u : ι → H) (b : ι → ℝ) (C : ℝ) : Prop :=
  ∀ F : Finset ι, ∀ c : F → ℝ,
    |∑ i : F, c i * b i| ^ 2 ≤
      C * ‖Fintype.linearCombination ℝ (fun i : F => u i) c‖ ^ 2

variable [CompleteSpace H]

theorem bounded_solution_sq_iff_finite (u : ι → H) (b : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) :
    (∃ x : H, ‖x‖ ^ 2 ≤ C ∧ IsSolution u b x) ↔
      ∀ F : Finset ι, ∃ x : H, ‖x‖ ^ 2 ≤ C ∧
        ∀ i ∈ F, inner ℝ (u i) x = b i := by
  simpa only [← norm_sq_le_iff_norm_le_sqrt _ hC] using
    bounded_solution_iff_finite u b (Real.sqrt C)

/-- The prescribed functional is bounded exactly when it is represented by
a vector with the same squared norm bound. -/
theorem bounded_solution_iff_dualBound (u : ι → H) (b : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) :
    (∃ x : H, ‖x‖ ^ 2 ≤ C ∧ IsSolution u b x) ↔ DualBound u b C := by
  rw [bounded_solution_sq_iff_finite u b hC]
  constructor
  · intro h F
    obtain ⟨x, hx, hb⟩ := h F
    exact (finite_dual_bound_iff (fun i : F => u i) (fun i : F => b i) C hC).mp
      ⟨x, fun i => hb i i.property, hx⟩
  · intro h F
    obtain ⟨x, hb, hx⟩ :=
      (finite_dual_bound_iff (fun i : F => u i) (fun i : F => b i) C hC).mpr (h F)
    exact ⟨x, hx, fun i hi => hb ⟨i, hi⟩⟩

theorem exists_solution_iff_dualBound (u : ι → H) (b : ι → ℝ) :
    (∃ x : H, IsSolution u b x) ↔ ∃ C : ℝ, 0 ≤ C ∧ DualBound u b C := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨‖x‖ ^ 2, sq_nonneg _,
      (bounded_solution_iff_dualBound u b (sq_nonneg _)).mp ⟨x, le_rfl, hx⟩⟩
  · rintro ⟨C, hC, h⟩
    obtain ⟨x, _, hx⟩ := (bounded_solution_iff_dualBound u b hC).mpr h
    exact ⟨x, hx⟩

omit [CompleteSpace H] in
theorem finiteOptimum_le_of_solution (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) (F : Finset ι) :
    finiteOptimum u b F ≤ ENNReal.ofReal (‖x‖ ^ 2) :=
  (finiteOptimum_le_ofReal_iff u b F (sq_nonneg _)).mpr ⟨x, le_rfl, fun i _ => hx i⟩

/-- The exact uniform finite-energy criterion for an infinite solution. -/
theorem exists_solution_iff_iSup_finiteOptimum_lt_top (u : ι → H) (b : ι → ℝ) :
    (∃ x : H, IsSolution u b x) ↔ (⨆ F : Finset ι, finiteOptimum u b F) < ⊤ := by
  constructor
  · rintro ⟨x, hx⟩
    exact lt_of_le_of_lt (iSup_le (finiteOptimum_le_of_solution u b hx))
      ENNReal.ofReal_lt_top
  · intro h
    let M : ℝ≥0∞ := ⨆ F : Finset ι, finiteOptimum u b F
    have hM : M ≠ ⊤ := ne_of_lt h
    obtain ⟨x, _, hx⟩ := (bounded_solution_sq_iff_finite u b
      (ENNReal.toReal_nonneg : 0 ≤ M.toReal)).mpr (fun F =>
        (finiteOptimum_le_ofReal_iff u b F ENNReal.toReal_nonneg).mp (by
          rw [ENNReal.ofReal_toReal hM]
          exact le_iSup (finiteOptimum u b) F))
    exact ⟨x, hx⟩

/-- Infinite optimum, with infinity when there is no solution. -/
def globalOptimum (u : ι → H) (b : ι → ℝ) : ℝ≥0∞ :=
  ⨅ x : H, ⨅ (_ : IsSolution u b x), ENNReal.ofReal (‖x‖ ^ 2)

/-- Supremum of finite optima equals the infinite optimum, including infinity. -/
theorem globalOptimum_eq_iSup_finiteOptimum (u : ι → H) (b : ι → ℝ) :
    globalOptimum u b = ⨆ F : Finset ι, finiteOptimum u b F := by
  have hlo : (⨆ F : Finset ι, finiteOptimum u b F) ≤ globalOptimum u b := by
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    exact iSup_le (finiteOptimum_le_of_solution u b hx)
  apply le_antisymm _ hlo
  by_cases hM : (⨆ F : Finset ι, finiteOptimum u b F) = ⊤
  · rw [hM]
    exact le_top
  · let M : ℝ≥0∞ := ⨆ F : Finset ι, finiteOptimum u b F
    obtain ⟨x, hx, hb⟩ := (bounded_solution_sq_iff_finite u b
      (ENNReal.toReal_nonneg : 0 ≤ M.toReal)).mpr (fun F =>
        (finiteOptimum_le_ofReal_iff u b F ENNReal.toReal_nonneg).mp (by
          rw [ENNReal.ofReal_toReal hM]
          exact le_iSup (finiteOptimum u b) F))
    apply iInf_le_of_le x
    apply iInf_le_of_le hb
    calc
      ENNReal.ofReal (‖x‖ ^ 2) ≤ ENNReal.ofReal M.toReal := ENNReal.ofReal_le_ofReal hx
      _ = M := ENNReal.ofReal_toReal hM

/-- The canonical solution attains the infinite optimum. -/
theorem globalOptimum_eq_canonical_energy (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) :
    globalOptimum u b = ENNReal.ofReal (‖(closedSpan u).starProjection x‖ ^ 2) := by
  apply le_antisymm
  · apply iInf_le_of_le ((closedSpan u).starProjection x)
    exact iInf_le _ (projection_isSolution u b hx)
  · apply le_iInf
    intro v
    apply le_iInf
    intro hv
    exact ENNReal.ofReal_le_ofReal (canonical_minimizes u b hx hv)

theorem canonical_energy_eq_iSup (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) :
    ENNReal.ofReal (‖(closedSpan u).starProjection x‖ ^ 2) =
      ⨆ F : Finset ι, finiteOptimum u b F := by
  rw [← globalOptimum_eq_canonical_energy u b hx, globalOptimum_eq_iSup_finiteOptimum]

omit [CompleteSpace H] in
theorem finiteSpan_eq_synthesisSpan (u : ι → H) (F : Finset ι) :
    finiteSpan u F = synthesisSpan (fun i : F => u i) := by
  unfold finiteSpan synthesisSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.property, rfl⟩

/-- Canonical finite reconstruction, defined from the data alone. -/
def finiteMinimum (u : ι → H) (b : ι → ℝ) (F : Finset ι) : H :=
  gramMinimumVector (fun i : F => u i) (fun i : F => b i)

omit [CompleteSpace H] in
/-- For consistent data, the finite Gram reconstruction is the actual
orthogonal projection of every global solution. -/
theorem finiteMinimum_eq_projection (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) (F : Finset ι) :
    finiteMinimum u b F = (finiteSpan u F).starProjection x := by
  let v : F → H := fun i => u i
  let d : F → ℝ := fun i => b i
  have hb : ∃ c : F → ℝ, gram v c = d :=
    (finite_feasible_iff_gram_range v d).mp ⟨x, fun i => hx i⟩
  have hm : gramMinimumVector v d ∈ finiteSpan u F := by
    rw [finiteSpan_eq_synthesisSpan]
    exact synthesis_mem v _
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hm
  intro w hw
  rw [finiteSpan_eq_synthesisSpan, synthesisSpan, ← Fintype.range_linearCombination] at hw
  obtain ⟨c, rfl⟩ := hw
  change inner ℝ (x - gramMinimumVector v d) (Fintype.linearCombination ℝ v c) = 0
  rw [real_inner_comm, inner_sub_right, inner_synthesis_left, inner_synthesis_left]
  simp only [show ∀ i : F, inner ℝ (v i) x = d i from fun i => hx i,
    gramMinimumVector_observation v d hb, sub_self]

omit [CompleteSpace H] in
theorem finiteOptimum_eq_finiteMinimum_energy (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) (F : Finset ι) :
    finiteOptimum u b F = ENNReal.ofReal (‖finiteMinimum u b F‖ ^ 2) := by
  have hb : ∃ c : F → ℝ, gram (fun i : F => u i) c = (fun i : F => b i) :=
    (finite_feasible_iff_gram_range _ _).mp ⟨x, fun i => hx i⟩
  rw [finiteOptimum, finiteConstraintEnergy_feasible _ _ hb,
    ← gramMinimumVector_energy _ _ hb]
  rfl

/-- The canonical least-energy finite solutions converge in norm as a net. -/
theorem finiteMinimum_tendsto (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) :
    Tendsto (finiteMinimum u b) atTop (𝓝 ((closedSpan u).starProjection x)) := by
  change Tendsto (fun F => finiteMinimum u b F) atTop (𝓝 ((closedSpan u).starProjection x))
  simpa only [finiteMinimum_eq_projection u b hx] using finiteProjection_tendsto u x

/-- Every cofinal finite exhaustion gives the same strong limit. -/
theorem finiteMinimum_tendsto_of_cofinal (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) {α : Type*} {l : Filter α}
    (F : α → Finset ι) (hF : Tendsto F l atTop) :
    Tendsto (fun a => finiteMinimum u b (F a)) l
      (𝓝 ((closedSpan u).starProjection x)) :=
  (finiteMinimum_tendsto u b hx).comp hF

omit [CompleteSpace H] in
theorem finiteMinimum_energy_increment (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) {F G : Finset ι} (hFG : F ⊆ G) :
    ‖finiteMinimum u b G - finiteMinimum u b F‖ ^ 2 =
      ‖finiteMinimum u b G‖ ^ 2 - ‖finiteMinimum u b F‖ ^ 2 := by
  simpa only [finiteMinimum_eq_projection u b hx] using
    finiteProjection_energy_increment u x hFG

/-- Exact strong-error formula with the supremum of actual finite energies. -/
theorem finiteMinimum_exact_error (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) (F : Finset ι) :
    ‖(closedSpan u).starProjection x - finiteMinimum u b F‖ ^ 2 =
      (⨆ G : Finset ι, finiteOptimum u b G).toReal - (finiteOptimum u b F).toReal := by
  rw [← canonical_energy_eq_iSup u b hx,
    finiteOptimum_eq_finiteMinimum_energy u b hx,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
    finiteMinimum_eq_projection u b hx]
  exact finiteProjection_error u x F

theorem finiteOptimum_toReal_tendsto (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) :
    Tendsto (fun F : Finset ι => (finiteOptimum u b F).toReal) atTop
      (𝓝 (⨆ F : Finset ι, finiteOptimum u b F).toReal) := by
  rw [← canonical_energy_eq_iSup u b hx]
  simpa only [finiteOptimum_eq_finiteMinimum_energy u b hx,
    ENNReal.toReal_ofReal (sq_nonneg _)] using (finiteMinimum_tendsto u b hx).norm.pow 2

/-- The least possible dual constant is attained and equals the canonical
squared norm. In particular, this identifies the infimum of all constants. -/
theorem canonical_energy_isLeast_dualBound (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) :
    IsLeast {C : ℝ | 0 ≤ C ∧ DualBound u b C}
      (‖(closedSpan u).starProjection x‖ ^ 2) := by
  refine ⟨⟨sq_nonneg _, ?_⟩, ?_⟩
  · exact (bounded_solution_iff_dualBound u b (sq_nonneg _)).mp
      ⟨(closedSpan u).starProjection x, le_rfl, projection_isSolution u b hx⟩
  · intro C hC
    obtain ⟨v, hv, hs⟩ := (bounded_solution_iff_dualBound u b hC.1).mpr hC.2
    exact (canonical_minimizes u b hx hs).trans hv

theorem existsUnique_solution_in_closedSpan (u : ι → H) (b : ι → ℝ)
    (h : ∃ x : H, IsSolution u b x) :
    ∃! v : H, IsSolution u b v ∧ v ∈ closedSpan u := by
  obtain ⟨x, hx⟩ := h
  refine ⟨(closedSpan u).starProjection x,
    ⟨projection_isSolution u b hx, (closedSpan u).starProjection_apply_mem x⟩, ?_⟩
  intro v hv
  have hp := solution_projection_eq u b hx hv.1
  rw [Submodule.starProjection_eq_self_iff.mpr hv.2] at hp
  exact hp

end RiemannResearch.Analysis.HilbertConstraintReconstruction
