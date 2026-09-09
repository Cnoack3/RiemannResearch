import RiemannResearch.RH.ParetoClosedRepairTails
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exact reverse-pivot expansion with its moving boundary

Source: user-provided `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 4.2. Coordinates here run from zero. Every projection is the actual
complete-tail projection; the finite decomposition retains its boundary vector.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

def reversePivotCoefficient (f : ℕ → ThresholdHilbert) (x : ThresholdHilbert) (i : ℕ) : ℝ :=
  inner ℝ x (infiniteRepairPivot f i) / ‖infiniteRepairPivot f i‖^2

/-- The one-dimensional quotient coefficient is determined by the true inner product. -/
theorem closedRepairTail_one_step (f : ℕ → ThresholdHilbert) (i : ℕ)
    (hi : infiniteRepairPivot f i ≠ 0) (x : ThresholdHilbert)
    (hx : x ∈ closedRepairTail f i) :
    x - closedRepairProjection f (i+1) x =
      reversePivotCoefficient f x i • infiniteRepairPivot f i := by
  let c := reversePivotCoefficient f x i
  have hn : ‖infiniteRepairPivot f i‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hi)
  have hmem : x - c • infiniteRepairPivot f i ∈ closedRepairTail f i :=
    (closedRepairTail f i).sub_mem hx
      ((closedRepairTail f i).smul_mem c (infiniteRepairPivot_mem f i))
  have ho : inner ℝ (x - c • infiniteRepairPivot f i) (infiniteRepairPivot f i) = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [c, reversePivotCoefficient]
    rw [div_mul_cancel₀ _ hn, sub_self]
  have hnext := closedRepairTail_mem_next_of_pivot_orthogonal f i _ hmem ho
  have he : closedRepairProjection f (i+1) x = x - c • infiniteRepairPivot f i := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hnext
    intro y hy
    have he' : x - (x - c • infiniteRepairPivot f i) = c • infiniteRepairPivot f i := by abel
    rw [he', real_inner_smul_left, infiniteRepairPivot_orthogonal_tail f i y hy, mul_zero]
  rw [he]
  dsimp [c]
  abel

theorem closedRepairProjection_nested (f : ℕ → ThresholdHilbert) (i j : ℕ)
    (hij : i ≤ j) (x : ThresholdHilbert) :
    closedRepairProjection f j (closedRepairProjection f i x) = closedRepairProjection f j x := by
  have h := Submodule.starProjection_comp_starProjection_of_le (closedRepairTail_antitone f hij)
  exact congrArg (fun T : ThresholdHilbert →L[ℝ] ThresholdHilbert => T x) h

theorem reversePivotCoefficient_projection (f : ℕ → ThresholdHilbert)
    (i : ℕ) (x : ThresholdHilbert) :
    reversePivotCoefficient f (closedRepairProjection f i x) i = reversePivotCoefficient f x i := by
  unfold reversePivotCoefficient
  have h := (closedRepairTail f i).starProjection_isSymmetric x (infiniteRepairPivot f i)
  have hv : closedRepairProjection f i (infiniteRepairPivot f i) = infiniteRepairPivot f i :=
    Submodule.starProjection_eq_self_iff.mpr (infiniteRepairPivot_mem f i)
  change inner ℝ (closedRepairProjection f i x) (infiniteRepairPivot f i) =
    inner ℝ x (closedRepairProjection f i (infiniteRepairPivot f i)) at h
  rw [h, hv]

theorem closedRepairProjection_step (f : ℕ → ThresholdHilbert)
    (i : ℕ) (hi : infiniteRepairPivot f i ≠ 0) (x : ThresholdHilbert) :
    closedRepairProjection f i x - closedRepairProjection f (i+1) x =
      reversePivotCoefficient f x i • infiniteRepairPivot f i := by
  have h := closedRepairTail_one_step f i hi (closedRepairProjection f i x)
    (closedRepairProjection_mem f i x)
  rwa [closedRepairProjection_nested f i (i+1) (Nat.le_succ i),
    reversePivotCoefficient_projection] at h

/-- Exact finite expansion of a vector in the original closed arithmetic span. -/
theorem reversePivot_expansion (f : ℕ → ThresholdHilbert)
    (hn : ∀ i, infiniteRepairPivot f i ≠ 0) (x : ThresholdHilbert)
    (hx : x ∈ closedRepairTail f 0) (N : ℕ) :
    x - closedRepairProjection f N x =
      ∑ i ∈ Finset.range N, reversePivotCoefficient f x i • infiniteRepairPivot f i := by
  induction N with
  | zero =>
      have hfix : closedRepairProjection f 0 x = x := Submodule.starProjection_eq_self_iff.mpr hx
      simp [hfix]
  | succ N ih =>
      rw [Finset.sum_range_succ, ← ih, ← closedRepairProjection_step f N (hn N) x]
      abel

theorem reversePivot_energy_split (f : ℕ → ThresholdHilbert)
    (hn : ∀ i, infiniteRepairPivot f i ≠ 0) (x : ThresholdHilbert)
    (hx : x ∈ closedRepairTail f 0) (N : ℕ) :
    ‖x‖^2 =
      (∑ i ∈ Finset.range N, ‖infiniteRepairPivot f i‖^2 * reversePivotCoefficient f x i^2) +
      ‖closedRepairProjection f N x‖^2 := by
  rw [closedRepairProjection_energy f N x, reversePivot_expansion f hn x hx N,
    infiniteRepairPivot_finite_energy]

/-- The orthogonal coefficient expansion converges in the full norm. -/
theorem reversePivot_expansion_tendsto (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (hn : ∀ i, infiniteRepairPivot f i ≠ 0) (x : ThresholdHilbert)
    (hx : x ∈ closedRepairTail f 0) :
    Filter.Tendsto
      (fun N => ∑ i ∈ Finset.range N, reversePivotCoefficient f x i • infiniteRepairPivot f i)
      Filter.atTop (nhds x) := by
  have h : Filter.Tendsto (fun N => x - closedRepairProjection f N x)
      Filter.atTop (nhds x) := by
    have hc : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) := tendsto_const_nhds
    simpa only [sub_zero] using
      hc.sub (closedRepairProjection_tendsto_zero f htri x)
  simpa only [reversePivot_expansion f hn x hx] using h

def originalRepairPartialSum (f : ℕ → ThresholdHilbert) (a : ℕ → ℝ) (N : ℕ) : ThresholdHilbert :=
  ∑ j ∈ Finset.range N, a j • f j

def originalRepairBoundary (f : ℕ → ThresholdHilbert) (a : ℕ → ℝ) (N : ℕ) : ThresholdHilbert :=
  closedRepairProjection f N (originalRepairPartialSum f a N)

theorem originalRepairPartialSum_mem (f : ℕ → ThresholdHilbert) (a : ℕ → ℝ) (N : ℕ) :
    originalRepairPartialSum f a N ∈ closedRepairTail f 0 := by
  apply Submodule.sum_mem
  intro j hj
  exact (closedRepairTail f 0).smul_mem _ (repairGenerator_mem_closedRepairTail f 0 j (Nat.zero_le j))

/-- The triangular coefficient transform, with every original signed coefficient. -/
def transformedRepairCoefficient (f : ℕ → ThresholdHilbert) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i+1), a j * inner ℝ (f j) (infiniteRepairPivot f i) /
    ‖infiniteRepairPivot f i‖^2

theorem originalRepairPartialSum_coefficient (f : ℕ → ThresholdHilbert)
    (a : ℕ → ℝ) (i N : ℕ) (hiN : i < N) :
    reversePivotCoefficient f (originalRepairPartialSum f a N) i =
      transformedRepairCoefficient f a i := by
  unfold reversePivotCoefficient originalRepairPartialSum transformedRepairCoefficient
  rw [sum_inner]
  simp only [real_inner_smul_left]
  rw [Finset.sum_div]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : i+1 ≤ N))
  intro j hjN hji
  have hij : i < j := by
    have h : ¬ j < i+1 := by simpa using hji
    omega
  rw [real_inner_comm (infiniteRepairPivot f i) (f j),
    infiniteRepairPivot_orthogonal_tail f i (f j)
      (repairGenerator_mem_closedRepairTail f (i+1) j hij), mul_zero, zero_div]

/-- The transformed coefficients and the true boundary give the exact raw sum. -/
theorem originalRepairPartialSum_expansion (f : ℕ → ThresholdHilbert)
    (hn : ∀ i, infiniteRepairPivot f i ≠ 0) (a : ℕ → ℝ) (N : ℕ) :
    originalRepairPartialSum f a N =
      (∑ i ∈ Finset.range N, transformedRepairCoefficient f a i • infiniteRepairPivot f i) +
      originalRepairBoundary f a N := by
  have he := reversePivot_expansion f hn _ (originalRepairPartialSum_mem f a N) N
  have hs : (∑ i ∈ Finset.range N,
      reversePivotCoefficient f (originalRepairPartialSum f a N) i • infiniteRepairPivot f i) =
      ∑ i ∈ Finset.range N, transformedRepairCoefficient f a i • infiniteRepairPivot f i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [originalRepairPartialSum_coefficient f a i N (Finset.mem_range.mp hi)]
  rw [hs] at he
  exact sub_eq_iff_eq_add.mp he

/-- Every raw finite repair sum retains its actual projected boundary. -/
theorem originalRepairPartialSum_energy (f : ℕ → ThresholdHilbert)
    (hn : ∀ i, infiniteRepairPivot f i ≠ 0) (a : ℕ → ℝ) (N : ℕ) :
    ‖originalRepairPartialSum f a N‖^2 =
      (∑ i ∈ Finset.range N, ‖infiniteRepairPivot f i‖^2 *
        reversePivotCoefficient f (originalRepairPartialSum f a N) i^2) +
      ‖originalRepairBoundary f a N‖^2 :=
  reversePivot_energy_split f hn _ (originalRepairPartialSum_mem f a N) N

/-- The complete raw energy retains the moving boundary in addition to the
triangularly transformed diagonal energy. -/
theorem originalRepairPartialSum_transformed_energy (f : ℕ → ThresholdHilbert)
    (hn : ∀ i, infiniteRepairPivot f i ≠ 0) (a : ℕ → ℝ) (N : ℕ) :
    ‖originalRepairPartialSum f a N‖^2 =
      (∑ i ∈ Finset.range N, ‖infiniteRepairPivot f i‖^2 * transformedRepairCoefficient f a i^2) +
      ‖originalRepairBoundary f a N‖^2 := by
  rw [originalRepairPartialSum_energy f hn a N]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [originalRepairPartialSum_coefficient f a i N (Finset.mem_range.mp hi)]

private theorem norm_sq_uniform_bound_of_tendsto (F : ℕ → ThresholdHilbert)
    (x : ThresholdHilbert) (hF : Filter.Tendsto F Filter.atTop (nhds x)) :
    ∃ C : ℝ, ∀ N, ‖F N‖^2 ≤ C := by
  have hlim : Filter.Tendsto (fun N => ‖F N‖^2) Filter.atTop (nhds (‖x‖^2)) := hF.norm.pow 2
  have hev : ∀ᶠ N in Filter.atTop, ‖F N‖^2 < ‖x‖^2 + 1 :=
    hlim.eventually_lt_const (by linarith)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  let C := (∑ N ∈ Finset.range N₀, ‖F N‖^2) + ‖x‖^2 + 1
  refine ⟨C, fun N => ?_⟩
  have hsum : 0 ≤ ∑ j ∈ Finset.range N₀, ‖F j‖^2 := Finset.sum_nonneg (fun j hj => sq_nonneg _)
  by_cases hN : N < N₀
  · have hterm : ‖F N‖^2 ≤ ∑ j ∈ Finset.range N₀, ‖F j‖^2 :=
      Finset.single_le_sum (f := fun j => ‖F j‖^2)
        (fun j hj => sq_nonneg ‖F j‖) (Finset.mem_range.mpr hN)
    dsimp [C]
    nlinarith [sq_nonneg ‖x‖]
  · have hterm := hN₀ N (le_of_not_gt hN)
    dsimp [C]
    linarith

/-- Natural-order convergence of the original arithmetic series is equivalent
to BOTH finite transformed energy and disappearance of its moving boundary.
All coefficients and all boundary terms are constructed from the original data. -/
theorem originalRepairSeries_converges_iff (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (hn : ∀ i, infiniteRepairPivot f i ≠ 0) (a : ℕ → ℝ) :
    (∃ x : ThresholdHilbert,
      Filter.Tendsto (originalRepairPartialSum f a) Filter.atTop (nhds x)) ↔
      Summable (fun i => ‖infiniteRepairPivot f i‖^2 * transformedRepairCoefficient f a i^2) ∧
      Filter.Tendsto (originalRepairBoundary f a) Filter.atTop (nhds 0) := by
  constructor
  · rintro ⟨x, hF⟩
    refine ⟨?_, closedRepairProjection_moving_tendsto_zero f htri _ x hF⟩
    obtain ⟨C, hC⟩ := norm_sq_uniform_bound_of_tendsto _ x hF
    apply summable_of_sum_range_le (c := C) (fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    intro N
    have he := originalRepairPartialSum_transformed_energy f hn a N
    have hN := hC N
    nlinarith [sq_nonneg ‖originalRepairBoundary f a N‖]
  · rintro ⟨hE, hB⟩
    have hS : Summable (fun i => transformedRepairCoefficient f a i • infiniteRepairPivot f i) :=
      (infiniteRepairPivot_summable_iff f _).mpr hE
    refine ⟨∑' i, transformedRepairCoefficient f a i • infiniteRepairPivot f i, ?_⟩
    have h := hS.hasSum.tendsto_sum_nat.add hB
    simpa only [← originalRepairPartialSum_expansion f hn a, add_zero] using h

end
end RiemannResearch.RH.Pareto
