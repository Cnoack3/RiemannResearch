import RiemannResearch.RH.ParetoClosedRepairTails
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite reverse pivots converge to the actual infinite pivot

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 4.1. The finite projections stay in the finite arithmetic span.
The limiting pivot is an element of its Hilbert closure and need not be finite.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

def finiteRepairTail (f : ℕ → ThresholdHilbert) (i N : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (f '' Set.Ico (i+1) (i+1+N))

instance finiteRepairTail_finiteDimensional (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    FiniteDimensional ℝ (finiteRepairTail f i N) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Ico (i+1) (i+1+N)).image f)

instance finiteRepairTail_complete (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    CompleteSpace (finiteRepairTail f i N) :=
  FiniteDimensional.complete ℝ _

instance finiteRepairTail_hasOrthogonalProjection (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    (finiteRepairTail f i N).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

theorem finiteRepairTail_mono (f : ℕ → ThresholdHilbert) (i : ℕ) :
    Monotone (finiteRepairTail f i) := by
  intro M N hMN
  apply Submodule.span_mono
  apply Set.image_mono
  intro j hj
  exact ⟨hj.1, lt_of_lt_of_le hj.2 (by omega)⟩

theorem finiteRepairTail_le_span (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    finiteRepairTail f i N ≤ repairTailSpan f (i+1) := by
  apply Submodule.span_mono
  apply Set.image_mono
  exact fun j hj => hj.1

theorem finiteRepairTail_le_closed (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    finiteRepairTail f i N ≤ closedRepairTail f (i+1) := by
  intro x hx y hy
  rw [real_inner_comm]
  exact hy x (finiteRepairTail_le_span f i N hx)

theorem finiteRepairTail_iSup (f : ℕ → ThresholdHilbert) (i : ℕ) :
    (⨆ N, finiteRepairTail f i N) = repairTailSpan f (i+1) := by
  apply le_antisymm
  · exact iSup_le (finiteRepairTail_le_span f i)
  · apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    apply (le_iSup (fun N => finiteRepairTail f i N) (j+1))
    apply Submodule.subset_span
    exact ⟨j, ⟨hj, by omega⟩, rfl⟩

def finiteRepairProjection (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (finiteRepairTail f i N).starProjection

theorem finiteRepairProjection_mem (f : ℕ → ThresholdHilbert) (i N : ℕ)
    (x : ThresholdHilbert) : finiteRepairProjection f i N x ∈ finiteRepairTail f i N :=
  Submodule.starProjection_apply_mem _ _

/-- The approximants are actual finite reverse projections. -/
def finiteRepairPivot (f : ℕ → ThresholdHilbert) (i N : ℕ) : ThresholdHilbert :=
  f i - finiteRepairProjection f i N (f i)

theorem finiteRepairProjection_tendsto (f : ℕ → ThresholdHilbert) (i : ℕ)
    (x : ThresholdHilbert) :
    Filter.Tendsto (fun N => finiteRepairProjection f i N x)
      Filter.atTop (nhds (closedRepairProjection f (i+1) x)) := by
  letI : (⨆ N, finiteRepairTail f i N).topologicalClosure.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have h := Submodule.starProjection_tendsto_closure_iSup
    (finiteRepairTail f i) (finiteRepairTail_mono f i) x
  simpa only [finiteRepairProjection, closedRepairProjection,
    finiteRepairTail_iSup, ← closedRepairTail_eq_closure] using h

theorem finiteRepairPivot_tendsto (f : ℕ → ThresholdHilbert) (i : ℕ) :
    Filter.Tendsto (fun N => finiteRepairPivot f i N)
      Filter.atTop (nhds (infiniteRepairPivot f i)) :=
  tendsto_const_nhds.sub (finiteRepairProjection_tendsto f i (f i))

/-- The finite pivot has exactly the infinite-pivot energy plus the squared
distance to that pivot. This includes the complete infinite Pareto tail. -/
theorem finiteRepairPivot_energy_gap (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    ‖finiteRepairPivot f i N‖^2 = ‖infiniteRepairPivot f i‖^2 +
      ‖finiteRepairPivot f i N - infiniteRepairPivot f i‖^2 := by
  have hdiff : finiteRepairPivot f i N - infiniteRepairPivot f i =
      closedRepairProjection f (i+1) (f i) - finiteRepairProjection f i N (f i) := by
    unfold finiteRepairPivot infiniteRepairPivot
    abel
  have hmem : finiteRepairPivot f i N - infiniteRepairPivot f i ∈
      closedRepairTail f (i+1) := by
    rw [hdiff]
    exact (closedRepairTail f (i+1)).sub_mem
      (closedRepairProjection_mem f (i+1) (f i))
      (finiteRepairTail_le_closed f i N (finiteRepairProjection_mem f i N (f i)))
  have ho := infiniteRepairPivot_orthogonal_tail f i _ hmem
  have ho' : inner ℝ (finiteRepairPivot f i N - infiniteRepairPivot f i)
      (infiniteRepairPivot f i) = 0 := by rw [real_inner_comm]; exact ho
  have he : finiteRepairPivot f i N = infiniteRepairPivot f i +
      (finiteRepairPivot f i N - infiniteRepairPivot f i) := by abel
  conv_lhs => rw [he]
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, ho, ho', real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

theorem infiniteRepairPivot_norm_sq_le_finite (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    ‖infiniteRepairPivot f i‖^2 ≤ ‖finiteRepairPivot f i N‖^2 := by
  rw [finiteRepairPivot_energy_gap]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- All finite pivots preserve the anchor and the complete earlier head. -/
theorem finiteRepairPivot_head (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i N k : ℕ) (hk : k ≤ i) :
    hilbertGibbsPhysical (finiteRepairPivot f i N) k = hilbertGibbsPhysical (f i) k :=
  closedRepairTail_sub_preserves_head f htri (i+1) k (by omega) _ _
    (finiteRepairTail_le_closed f i N (finiteRepairProjection_mem f i N (f i)))

theorem finiteRepairPivot_anchor (f : ℕ → ThresholdHilbert) (i N k : ℕ)
    (hz : ∀ j, i < j → hilbertGibbsPhysical (f j) k = 0) :
    hilbertGibbsPhysical (finiteRepairPivot f i N) k = hilbertGibbsPhysical (f i) k := by
  have hp := closedRepairTail_coordinate_zero f (i+1) k hz _
    (finiteRepairTail_le_closed f i N (finiteRepairProjection_mem f i N (f i)))
  change ((f i) k - (finiteRepairProjection f i N (f i)) k) /
    Real.sqrt (paretoWeight k) = _
  rw [sub_div]
  change hilbertGibbsPhysical (f i) k -
    hilbertGibbsPhysical (finiteRepairProjection f i N (f i)) k = _
  rw [hp, sub_zero]

/-- The approximating pivot is a finite linear combination of the original
arithmetic generators, including its own anchor generator. -/
theorem finiteRepairPivot_mem_finite_span (f : ℕ → ThresholdHilbert) (i N : ℕ) :
    finiteRepairPivot f i N ∈ Submodule.span ℝ (f '' Set.Ico i (i+1+N)) := by
  apply Submodule.sub_mem
  · exact Submodule.subset_span ⟨i, ⟨le_rfl, by omega⟩, rfl⟩
  · have hle : finiteRepairTail f i N ≤ Submodule.span ℝ (f '' Set.Ico i (i+1+N)) := by
      apply Submodule.span_mono
      apply Set.image_mono
      intro j hj
      have hlow : i+1 ≤ j := hj.1
      exact ⟨by omega, hj.2⟩
    exact hle (finiteRepairProjection_mem f i N (f i))

end
end RiemannResearch.RH.Pareto
