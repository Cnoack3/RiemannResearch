/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.HilbertWeakCompactness
import RiemannResearch.Analysis.NestedProjectionEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Infinite Hilbert constraint reconstruction

Source: user-provided `Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md`,
Theorem E. The compactness argument extends the countable interpolation result
to arbitrary families; the projection argument specializes Mathlib's strong
convergence of increasing projections. These results supply the analytic
reconstruction layer for the Pareto/CRT program, without asserting any
arithmetic uniform-energy bound or the Riemann Hypothesis.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Bounded approximate interpolation along any nontrivial filter has an exact
interpolant. No countability or separability hypothesis is needed. -/
theorem exists_mem_of_bounded_test_net (S : Submodule ℝ H) [CompleteSpace S]
    {ι α : Type*} {l : Filter α} [l.NeBot] (C : ℝ) (F : α → H)
    (hmem : ∀ a, F a ∈ S) (hbound : ∀ a, ‖F a‖ ≤ C)
    (L : ι → H →L[ℝ] ℝ) (b : ι → ℝ)
    (hlim : ∀ i, Tendsto (fun a => L i (F a)) l (𝓝 (b i))) :
    ∃ f ∈ S, ‖f‖ ≤ C ∧ ∀ i, L i f = b i := by
  let test : WeakSpace ℝ S → (ι → ℝ) := fun w i =>
    ((L i).comp S.subtypeL) ((toWeakSpace ℝ S).symm w)
  have ht : Continuous test := by
    apply continuous_pi
    intro i
    exact WeakBilin.eval_continuous (topDualPairing ℝ S).flip
      ((L i).comp S.subtypeL)
  have hc := (RiemannResearch.Analysis.HilbertWeakCompactness.isCompact_closedBall_weak
    (H := S) C).image ht
  have hb : b ∈ test '' (toWeakSpace ℝ S '' Metric.closedBall (0 : S) C) := by
    apply hc.isClosed.mem_of_tendsto (tendsto_pi_nhds.mpr hlim)
    apply Eventually.of_forall
    intro a
    refine ⟨toWeakSpace ℝ S ⟨F a, hmem a⟩, ?_, ?_⟩
    · exact ⟨⟨F a, hmem a⟩, by simpa using hbound a, rfl⟩
    · rfl
  obtain ⟨w, ⟨f, hf, rfl⟩, hfb⟩ := hb
  refine ⟨f, f.property, ?_, ?_⟩
  · simpa using hf
  · intro i
    exact congrFun hfb i

/-- Uniform bounded feasibility of every finite subsystem is equivalent to
bounded feasibility of an arbitrary simultaneous family of continuous tests. -/
theorem bounded_finset_test_feasibility_iff (S : Submodule ℝ H) [CompleteSpace S]
    {ι : Type*} (C : ℝ) (L : ι → H →L[ℝ] ℝ) (b : ι → ℝ) :
    (∀ F : Finset ι, ∃ f ∈ S, ‖f‖ ≤ C ∧ ∀ i ∈ F, L i f = b i) ↔
      ∃ f ∈ S, ‖f‖ ≤ C ∧ ∀ i, L i f = b i := by
  classical
  constructor
  · intro h
    choose f hmem hbound hfinite using h
    apply S.exists_mem_of_bounded_test_net (l := atTop) C f hmem hbound L b
    intro i
    apply (tendsto_const_nhds :
      Tendsto (fun _ : Finset ι => b i) atTop (𝓝 (b i))).congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with F hF
    exact (hfinite F i (hF (by simp))).symm
  · rintro ⟨f, hf, hn, ht⟩ F
    exact ⟨f, hf, hn, fun i _ => ht i⟩

end Submodule

namespace RiemannResearch.Analysis.HilbertConstraintReconstruction

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual finite constraint span, allowing linear dependencies. -/
def finiteSpan (u : ι → H) (F : Finset ι) : Submodule ℝ H :=
  Submodule.span ℝ (u '' (F : Set ι))

instance finiteSpan_finiteDimensional (u : ι → H) (F : Finset ι) :
    FiniteDimensional ℝ (finiteSpan u F) :=
  FiniteDimensional.span_of_finite ℝ (F.finite_toSet.image u)

theorem finiteSpan_mono (u : ι → H) : Monotone (finiteSpan u) := by
  intro F G hFG
  exact Submodule.span_mono (Set.image_mono hFG)

theorem finiteSpan_le (u : ι → H) (F : Finset ι) :
    finiteSpan u F ≤ Submodule.span ℝ (Set.range u) := by
  apply Submodule.span_mono
  rintro _ ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

theorem iSup_finiteSpan (u : ι → H) :
    (⨆ F : Finset ι, finiteSpan u F) = Submodule.span ℝ (Set.range u) := by
  classical
  apply le_antisymm
  · exact iSup_le (finiteSpan_le u)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (le_iSup (finiteSpan u) {i})
    exact Submodule.subset_span ⟨i, by simp, rfl⟩

/-- Closed space in which the unique least-norm solution lies. -/
def closedSpan (u : ι → H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range u)).topologicalClosure

def IsSolution (u : ι → H) (b : ι → ℝ) (v : H) : Prop :=
  ∀ i, inner ℝ (u i) v = b i

variable [CompleteSpace H]

instance closedSpan_hasOrthogonalProjection (u : ι → H) :
    (closedSpan u).HasOrthogonalProjection := by
  unfold closedSpan
  infer_instance

/-- Strong convergence holds for the full finite-subset net, including an
uncountable dictionary. -/
theorem finiteProjection_tendsto (u : ι → H) (x : H) :
    Tendsto (fun F : Finset ι => (finiteSpan u F).starProjection x) atTop
      (𝓝 ((closedSpan u).starProjection x)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    (finiteSpan u) (finiteSpan_mono u) x
  simpa only [iSup_finiteSpan, closedSpan] using h

omit [CompleteSpace H] in
/-- Exact finite-stage energy increment. -/
theorem finiteProjection_energy_increment (u : ι → H) (x : H)
    {F G : Finset ι} (hFG : F ⊆ G) :
    ‖(finiteSpan u G).starProjection x - (finiteSpan u F).starProjection x‖ ^ 2 =
      ‖(finiteSpan u G).starProjection x‖ ^ 2 -
        ‖(finiteSpan u F).starProjection x‖ ^ 2 := by
  have h := NestedProjectionEnergy.captured_energy_eq_add_gap
    (finiteSpan_mono u hFG) x
  linarith

/-- Exact error relative to the canonical limiting solution. -/
theorem finiteProjection_error (u : ι → H) (x : H) (F : Finset ι) :
    ‖(closedSpan u).starProjection x - (finiteSpan u F).starProjection x‖ ^ 2 =
      ‖(closedSpan u).starProjection x‖ ^ 2 -
        ‖(finiteSpan u F).starProjection x‖ ^ 2 := by
  have hle : finiteSpan u F ≤ closedSpan u :=
    (finiteSpan_le u F).trans (Submodule.span ℝ (Set.range u)).le_topologicalClosure
  have h := NestedProjectionEnergy.captured_energy_eq_add_gap hle x
  linarith

omit [CompleteSpace H] in
/-- Every prescribed representer belongs to the closed constraint span. -/
theorem mem_closedSpan (u : ι → H) (i : ι) : u i ∈ closedSpan u :=
  (Submodule.span ℝ (Set.range u)).le_topologicalClosure
    (Submodule.subset_span ⟨i, rfl⟩)

omit [CompleteSpace H] in
/-- Orthogonality to the closed span is exactly vanishing on the constraints. -/
theorem mem_closedSpan_orthogonal_iff (u : ι → H) (z : H) :
    z ∈ (closedSpan u)ᗮ ↔ ∀ i, inner ℝ (u i) z = 0 := by
  constructor
  · intro h i
    exact ((closedSpan u).mem_orthogonal z).mp h _ (mem_closedSpan u i)
  · intro h
    apply ((closedSpan u).mem_orthogonal z).mpr
    have hspan : ∀ y ∈ Submodule.span ℝ (Set.range u), inner ℝ y z = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        exact h i
      | zero => simp
      | add x y hx hy hix hiy => simp [inner_add_left, hix, hiy]
      | smul a x hx hix => simp [inner_smul_left, hix]
    have hc : IsClosed {y : H | inner ℝ y z = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    intro y hy
    exact closure_minimal hspan hc hy

/-- All solutions form an affine translate of the orthogonal complement. -/
theorem isSolution_iff_sub_mem_orthogonal (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) (v : H) :
    IsSolution u b v ↔ v - x ∈ (closedSpan u)ᗮ := by
  rw [mem_closedSpan_orthogonal_iff]
  constructor
  · intro hv i
    rw [inner_sub_right, hv i, hx i, sub_self]
  · intro h i
    have hi := h i
    rw [inner_sub_right, hx i] at hi
    exact sub_eq_zero.mp hi

/-- Projecting any solution onto the closed constraint span preserves every
constraint and removes exactly the unconstrained orthogonal component. -/
theorem projection_isSolution (u : ι → H) (b : ι → ℝ)
    {x : H} (hx : IsSolution u b x) :
    IsSolution u b ((closedSpan u).starProjection x) := by
  intro i
  have hi := Submodule.starProjection_inner_eq_zero x (u i) (mem_closedSpan u i)
  rw [inner_sub_left] at hi
  calc
    inner ℝ (u i) ((closedSpan u).starProjection x) =
        inner ℝ ((closedSpan u).starProjection x) (u i) := real_inner_comm _ _
    _ = inner ℝ x (u i) := (sub_eq_zero.mp hi).symm
    _ = inner ℝ (u i) x := real_inner_comm _ _
    _ = b i := hx i

/-- Any two solutions have the same canonical projection. -/
theorem solution_projection_eq (u : ι → H) (b : ι → ℝ)
    {x v : H} (hx : IsSolution u b x) (hv : IsSolution u b v) :
    (closedSpan u).starProjection v = (closedSpan u).starProjection x := by
  have hz := (isSolution_iff_sub_mem_orthogonal u b hx v).mp hv
  have hp := ((closedSpan u).starProjection_apply_eq_zero_iff).mpr hz
  rw [map_sub] at hp
  exact sub_eq_zero.mp hp

/-- Exact least-energy decomposition, including the full norm-square remainder. -/
theorem solution_energy_decomposition (u : ι → H) (b : ι → ℝ)
    {x v : H} (hx : IsSolution u b x) (hv : IsSolution u b v) :
    ‖v‖ ^ 2 = ‖(closedSpan u).starProjection x‖ ^ 2 +
      ‖v - (closedSpan u).starProjection x‖ ^ 2 := by
  simpa only [solution_projection_eq u b hx hv] using
    NestedProjectionEnergy.norm_sq_eq_projection_add_residual (closedSpan u) v

theorem canonical_minimizes (u : ι → H) (b : ι → ℝ)
    {x v : H} (hx : IsSolution u b x) (hv : IsSolution u b v) :
    ‖(closedSpan u).starProjection x‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have h := solution_energy_decomposition u b hx hv
  nlinarith [sq_nonneg ‖v - (closedSpan u).starProjection x‖]

/-- The norm minimizer is unique. -/
theorem canonical_unique_minimizer (u : ι → H) (b : ι → ℝ)
    {x v : H} (hx : IsSolution u b x) (hv : IsSolution u b v)
    (hmin : ‖v‖ ^ 2 ≤ ‖(closedSpan u).starProjection x‖ ^ 2) :
    v = (closedSpan u).starProjection x := by
  have h := solution_energy_decomposition u b hx hv
  have hz : ‖v - (closedSpan u).starProjection x‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Fixed target data are globally realizable with a prescribed norm bound
exactly when all finite subsystems are realizable with that same bound. -/
theorem bounded_solution_iff_finite (u : ι → H) (b : ι → ℝ) (R : ℝ) :
    (∃ v : H, ‖v‖ ≤ R ∧ IsSolution u b v) ↔
      ∀ F : Finset ι, ∃ v : H, ‖v‖ ≤ R ∧ ∀ i ∈ F, inner ℝ (u i) v = b i := by
  let : CompleteSpace (⊤ : Submodule ℝ H) :=
    (isClosed_univ : IsClosed (Set.univ : Set H)).isComplete.completeSpace_coe
  simpa [IsSolution] using
    ((⊤ : Submodule ℝ H).bounded_finset_test_feasibility_iff R
      (fun i => innerSL ℝ (u i)) b).symm

end RiemannResearch.Analysis.HilbertConstraintReconstruction
