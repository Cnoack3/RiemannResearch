import RiemannResearch.Analysis.ExhaustiveProjectionWalk

/-!
# Target-specific adaptive completeness from residual correlations

Source: sixth Ramanujan transfer program, 24 October 2026.
Every atom need only become asymptotically orthogonal to the current residual.
The draw need not enumerate the dictionary, and its visited closed span need
not equal the whole dictionary span. The criterion is necessary and sufficient.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ProjectionCorrelationCompleteness
open ExhaustiveWalk
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def CorrelationsVanish (v : ι → H) (draw : ℕ → ι) (x : H) : Prop :=
  ∀ i, Tendsto (fun n => inner ℝ (v i) (x - (walkSpan v draw n).starProjection x))
    atTop (𝓝 0)

theorem inner_zero_on_dictionaryClosure (v : ι → H) (r : H)
    (h : ∀ i, inner ℝ (v i) r = 0) :
    ∀ w ∈ ExhaustiveWalk.dictionaryClosure v, inner ℝ w r = 0 := by
  have hs : Submodule.span ℝ (Set.range v) ≤ (innerSL ℝ r).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨i, rfl⟩
    change inner ℝ r (v i) = 0
    rw [real_inner_comm, h i]
  apply (Submodule.orthogonal_closure' (Submodule.span ℝ (Set.range v)) r).mp
  intro w hw
  have hz := hs hw
  change inner ℝ r w = 0 at hz
  exact (real_inner_comm r w).trans hz

theorem atom_mem_dictionaryClosure (v : ι → H) (i : ι) :
    v i ∈ ExhaustiveWalk.dictionaryClosure v :=
  (Submodule.span ℝ (Set.range v)).le_topologicalClosure
    (Submodule.subset_span (Set.mem_range_self i))

theorem correlation_tendsto (v : ι → H) (draw : ℕ → ι) (x : H) (i : ι) :
    Tendsto (fun n => inner ℝ (v i) (x - (walkSpan v draw n).starProjection x))
      atTop (𝓝 (inner ℝ (v i) (x - visitedProjection v draw x))) := by
  have hv : Tendsto (fun _ : ℕ => v i) atTop (𝓝 (v i)) := tendsto_const_nhds
  have hx : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
  exact hv.inner (hx.sub (walkProjection_tendsto_visited v draw x))

/-- Exact target-dependent completeness: no exhaustive enumeration assumption. -/
theorem visited_eq_full_iff_correlations (v : ι → H) (draw : ℕ → ι) (x : H) :
    visitedProjection v draw x = (ExhaustiveWalk.dictionaryClosure v).starProjection x ↔
      CorrelationsVanish v draw x := by
  constructor
  · intro he i
    have hz : inner ℝ (v i) (x - visitedProjection v draw x) = 0 := by
      rw [he, real_inner_comm]
      exact Submodule.starProjection_inner_eq_zero x (v i) (atom_mem_dictionaryClosure v i)
    simpa only [hz] using correlation_tendsto v draw x i
  · intro h
    have ha : ∀ i, inner ℝ (v i) (x - visitedProjection v draw x) = 0 :=
      fun i => tendsto_nhds_unique (correlation_tendsto v draw x i) (h i)
    apply Eq.symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact visitedClosure_le_dictionaryClosure v draw
        ((visitedClosure v draw).starProjection_apply_mem x)
    · intro w hw
      rw [real_inner_comm]
      exact inner_zero_on_dictionaryClosure v _ ha w hw

theorem error_eq_full_iff_correlations (v : ι → H) (draw : ℕ → ι) (x : H) :
    visitedError v draw x = limitingError v x ↔ CorrelationsVanish v draw x :=
  (visitedError_eq_full_iff v draw x).trans (visited_eq_full_iff_correlations v draw x)

theorem projection_tendsto_full_of_correlations (v : ι → H) (draw : ℕ → ι) (x : H)
    (h : CorrelationsVanish v draw x) :
    Tendsto (fun n => (walkSpan v draw n).starProjection x) atTop
      (𝓝 ((ExhaustiveWalk.dictionaryClosure v).starProjection x)) := by
  rw [← (visited_eq_full_iff_correlations v draw x).mpr h]
  exact walkProjection_tendsto_visited v draw x

end RiemannResearch.Analysis.ProjectionCorrelationCompleteness
