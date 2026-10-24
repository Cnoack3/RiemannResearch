import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact comparison of two partially explored dictionaries

Source: sixth Ramanujan transfer program, 24 October 2026.
The two subspaces need not be nested. A common covered subspace gives an
exact signed cross term; independent cofinal walks agree exactly when their
target projections agree, which is weaker than equality of visited spans.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.ProjectionWalkComparison
open ExhaustiveWalk
variable {H ι α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

theorem common_core_comparison_exact (A K L : Submodule ℝ H)
    [A.HasOrthogonalProjection] [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hAK : A ≤ K) (hAL : A ≤ L) (x : H) :
    ‖K.starProjection x - L.starProjection x‖ ^ 2 =
      2 * ‖x - A.starProjection x‖ ^ 2 - ‖x - K.starProjection x‖ ^ 2 -
        ‖x - L.starProjection x‖ ^ 2 -
      2 * inner ℝ (K.starProjection x - A.starProjection x)
        (L.starProjection x - A.starProjection x) := by
  have hK := nested_projection_energy A K hAK x
  have hL := nested_projection_energy A L hAL x
  have he : K.starProjection x - L.starProjection x =
      (K.starProjection x - A.starProjection x) - (L.starProjection x - A.starProjection x) := by abel
  rw [he, norm_sub_sq_real]
  linarith

/-- The sharp sum of radii follows from the full common-core identity. -/
theorem common_core_distance_bound (A K L : Submodule ℝ H)
    [A.HasOrthogonalProjection] [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hAK : A ≤ K) (hAL : A ≤ L) (x : H) :
    ‖K.starProjection x - L.starProjection x‖ ≤
      Real.sqrt (‖x - A.starProjection x‖ ^ 2 - ‖x - K.starProjection x‖ ^ 2) +
      Real.sqrt (‖x - A.starProjection x‖ ^ 2 - ‖x - L.starProjection x‖ ^ 2) := by
  have hK := nested_projection_energy A K hAK x
  have hL := nested_projection_energy A L hAL x
  have heK : ‖x - A.starProjection x‖ ^ 2 - ‖x - K.starProjection x‖ ^ 2 =
      ‖K.starProjection x - A.starProjection x‖ ^ 2 := by linarith
  have heL : ‖x - A.starProjection x‖ ^ 2 - ‖x - L.starProjection x‖ ^ 2 =
      ‖L.starProjection x - A.starProjection x‖ ^ 2 := by linarith
  rw [heK, heL, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have he : K.starProjection x - L.starProjection x =
      (K.starProjection x - A.starProjection x) - (L.starProjection x - A.starProjection x) := by abel
  rw [he]
  exact norm_sub_le _ _

theorem visitedClosure_eq_of_range_eq (v : ι → H) (d e : ℕ → ι)
    (h : Set.range d = Set.range e) : visitedClosure v d = visitedClosure v e := by
  have hr : Set.range (fun n => v (d n)) = Set.range (fun n => v (e n)) := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      have hn : d n ∈ Set.range e := h ▸ Set.mem_range_self n
      obtain ⟨m, hm⟩ := hn
      exact ⟨m, congrArg v hm⟩
    · rintro ⟨n, rfl⟩
      have hn : e n ∈ Set.range d := h.symm ▸ Set.mem_range_self n
      obtain ⟨m, hm⟩ := hn
      exact ⟨m, congrArg v hm⟩
  unfold visitedClosure ExhaustiveWalk.dictionaryClosure
  rw [hr]

theorem cofinal_difference_tendsto {l : Filter α}
    (v : ι → H) (d e : ℕ → ι) (x : H) (N M : α → ℕ)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop) :
    Tendsto (fun i => (walkSpan v d (N i)).starProjection x -
      (walkSpan v e (M i)).starProjection x) l
      (𝓝 (visitedProjection v d x - visitedProjection v e x)) :=
  ((walkProjection_tendsto_visited v d x).comp hN).sub
    ((walkProjection_tendsto_visited v e x).comp hM)

/-- Target-dependent agreement is exactly sufficient; the visited subspaces may differ. -/
theorem cofinal_difference_zero_iff {l : Filter α} [NeBot l]
    (v : ι → H) (d e : ℕ → ι) (x : H) (N M : α → ℕ)
    (hN : Tendsto N l atTop) (hM : Tendsto M l atTop) :
    Tendsto (fun i => (walkSpan v d (N i)).starProjection x -
      (walkSpan v e (M i)).starProjection x) l (𝓝 0) ↔
      visitedProjection v d x = visitedProjection v e x := by
  have ht := cofinal_difference_tendsto v d e x N M hN hM
  constructor
  · intro h
    exact sub_eq_zero.mp (tendsto_nhds_unique ht h)
  · intro h
    simpa only [h, sub_self] using ht

theorem cofinal_difference_zero_of_same_range {l : Filter α}
    (v : ι → H) (d e : ℕ → ι) (h : Set.range d = Set.range e)
    (x : H) (N M : α → ℕ) (hN : Tendsto N l atTop) (hM : Tendsto M l atTop) :
    Tendsto (fun i => (walkSpan v d (N i)).starProjection x -
      (walkSpan v e (M i)).starProjection x) l (𝓝 0) := by
  have he : visitedProjection v d x = visitedProjection v e x := by
    simp only [visitedProjection, visitedClosure_eq_of_range_eq v d e h]
  simpa only [he, sub_self] using cofinal_difference_tendsto v d e x N M hN hM

end RiemannResearch.Analysis.ProjectionWalkComparison
