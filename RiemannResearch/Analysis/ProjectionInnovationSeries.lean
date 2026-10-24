import RiemannResearch.Analysis.ProjectionVariation
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Complete orthogonal innovation series of arbitrary projection walks

Source: sixth Ramanujan transfer program, 24 October 2026. The standard
orthogonal-series theorem is applied to the actual increment subspaces.
No exhaustive ordering or nonzero-pivot assumption is required.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ProjectionInnovationSeries
open ExhaustiveWalk ProjectionVariation
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def innovationSpace (v : ι → H) (draw : ℕ → ι) (n : ℕ) : Submodule ℝ H :=
  walkSpan v draw (n + 1) ⊓ (walkSpan v draw n)ᗮ

theorem increment_mem (v : ι → H) (draw : ℕ → ι) (x : H) (n : ℕ) :
    increment v draw x n ∈ innovationSpace v draw n := by
  constructor
  · exact (walkSpan v draw (n + 1)).sub_mem
      ((walkSpan v draw (n + 1)).starProjection_apply_mem x)
      (walkSpan_mono v draw (Nat.le_succ n) ((walkSpan v draw n).starProjection_apply_mem x))
  · have hc : (walkSpan v draw n).starProjection
        ((walkSpan v draw (n + 1)).starProjection x) = (walkSpan v draw n).starProjection x :=
      congrArg (fun T : H →L[ℝ] H => T x)
        (Submodule.starProjection_comp_starProjection_of_le (walkSpan_mono v draw (Nat.le_succ n)))
    have hz : (walkSpan v draw n).starProjection (increment v draw x n) = 0 := by
      rw [increment, map_sub, hc, Submodule.starProjection_eq_self_iff.mpr
        ((walkSpan v draw n).starProjection_apply_mem x), sub_self]
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    rw [← Submodule.starProjection_eq_self_iff.mpr hy,
      (walkSpan v draw n).inner_starProjection_left_eq_right, hz, inner_zero_right]

theorem innovationSpace_orthogonal (v : ι → H) (draw : ℕ → ι) :
    OrthogonalFamily ℝ (fun n => innovationSpace v draw n)
      (fun n => (innovationSpace v draw n).subtypeₗᵢ) := by
  intro i j hij x y
  rcases lt_or_gt_of_ne hij with h | h
  · exact (Submodule.mem_orthogonal _ _).mp y.property.2 x
      (walkSpan_mono v draw (Nat.succ_le_of_lt h) x.property.1)
  · rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).mp x.property.2 y
      (walkSpan_mono v draw (Nat.succ_le_of_lt h) y.property.1)

theorem increment_energy_summable (v : ι → H) (draw : ℕ → ι) (x : H) (N : ℕ) :
    Summable (fun j => ‖increment v draw x (j + N)‖ ^ 2) := by
  apply summable_of_sum_range_le (fun j => sq_nonneg _)
    (c := walkError v draw x N)
  intro M
  rw [increment_energy_sum]
  exact sub_le_self _ (sq_nonneg _)

theorem sum_increment (v : ι → H) (draw : ℕ → ι) (x : H) (N M : ℕ) :
    (∑ j ∈ Finset.range M, increment v draw x (j + N)) =
      (walkSpan v draw (M + N)).starProjection x - (walkSpan v draw N).starProjection x := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [increment, Nat.add_right_comm M 1 N]
    abel

theorem sum_increment_tendsto (v : ι → H) (draw : ℕ → ι) (x : H) (N : ℕ) :
    Tendsto (fun M => ∑ j ∈ Finset.range M, increment v draw x (j + N)) atTop
      (𝓝 (visitedProjection v draw x - (walkSpan v draw N).starProjection x)) := by
  simp_rw [sum_increment]
  exact ((walkProjection_tendsto_visited v draw x).comp (tendsto_add_atTop_nat N)).sub
    tendsto_const_nhds

/-- The vector series is unconditionally summable, not merely convergent in its given order. -/
theorem increment_summable (v : ι → H) (draw : ℕ → ι) (x : H) :
    Summable (increment v draw x) := by
  let f : ∀ n, innovationSpace v draw n := fun n => ⟨increment v draw x n, increment_mem v draw x n⟩
  have hf (n : ℕ) : ‖f n‖ = ‖increment v draw x n‖ :=
    Submodule.coe_norm (f n)
  have hs : Summable (fun n => ‖f n‖ ^ 2) := by
    simpa only [hf, Nat.add_zero] using increment_energy_summable v draw x 0
  exact ((innovationSpace_orthogonal v draw).summable_iff_norm_sq_summable f).mpr hs

theorem increment_tail_hasSum (v : ι → H) (draw : ℕ → ι) (x : H) (N : ℕ) :
    HasSum (fun j => increment v draw x (j + N))
      (visitedProjection v draw x - (walkSpan v draw N).starProjection x) := by
  have hs := (increment_summable v draw x).comp_injective
    (i := fun j : ℕ => j + N) (fun i j h => Nat.add_right_cancel h)
  have hs' : Summable (fun j => increment v draw x (j + N)) := hs
  have he := tendsto_nhds_unique hs'.hasSum.tendsto_sum_nat
    (sum_increment_tendsto v draw x N)
  exact he ▸ hs'.hasSum

/-- Parseval's full tail is the exact still-uncaptured visited-space norm. -/
theorem increment_tail_energy (v : ι → H) (draw : ℕ → ι) (x : H) (N : ℕ) :
    (∑' j, ‖increment v draw x (j + N)‖ ^ 2) =
      ‖visitedProjection v draw x - (walkSpan v draw N).starProjection x‖ ^ 2 := by
  have hs := (increment_energy_summable v draw x N).hasSum.tendsto_sum_nat
  have ht : Tendsto (fun M => ∑ j ∈ Finset.range M, ‖increment v draw x (j + N)‖ ^ 2)
      atTop (𝓝 (walkError v draw x N - visitedError v draw x)) := by
    simp_rw [increment_energy_sum]
    exact tendsto_const_nhds.sub
      ((walkError_tendsto_visited v draw x).comp (tendsto_add_atTop_nat N))
  have he := tendsto_nhds_unique hs ht
  have hsplit := walkError_eq_visited_add v draw x N
  linarith

theorem increment_energy_tendsto_zero (v : ι → H) (draw : ℕ → ι) (x : H) :
    Tendsto (fun n => ‖increment v draw x n‖ ^ 2) atTop (𝓝 0) := by
  simpa only [Nat.add_zero] using (increment_energy_summable v draw x 0).tendsto_atTop_zero

/-- Exact finite multiplier energy, preserving every signed scalar multiplier. -/
theorem weighted_increment_energy (v : ι → H) (draw : ℕ → ι) (x : H)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ j ∈ s, a j • increment v draw x j‖ ^ 2 =
      ∑ j ∈ s, (a j) ^ 2 * ‖increment v draw x j‖ ^ 2 := by
  let f : ∀ n, innovationSpace v draw n :=
    fun n => a n • ⟨increment v draw x n, increment_mem v draw x n⟩
  have hf (n : ℕ) : (innovationSpace v draw n).subtypeₗᵢ (f n) =
      a n • increment v draw x n := rfl
  have hn (n : ℕ) : ‖f n‖ ^ 2 = (a n) ^ 2 * ‖increment v draw x n‖ ^ 2 := by
    rw [Submodule.coe_norm]
    change ‖a n • increment v draw x n‖ ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simpa only [hf, hn] using (innovationSpace_orthogonal v draw).norm_sum f s

end RiemannResearch.Analysis.ProjectionInnovationSeries
