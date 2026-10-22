import RiemannResearch.RH.ParetoGibbsTailBasis

/-!
# Actual closed arithmetic tail spaces have zero intersection

Source: `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, Section 4.
The sequence is indexed from zero: its i-th generator vanishes at all earlier
physical Gibbs coordinates k<i. All closed spans and norms are genuine Hilbert
space constructions. Zero intersection alone does not remove a moving boundary.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The algebraic span of all generators at or beyond i. -/
def repairTailSpan (f : ℕ → ThresholdHilbert) (i : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (f '' Set.Ici i)

/-- The double orthogonal is the actual closed tail span. -/
def closedRepairTail (f : ℕ → ThresholdHilbert) (i : ℕ) : Submodule ℝ ThresholdHilbert :=
  (repairTailSpan f i)ᗮᗮ

 theorem closedRepairTail_eq_closure (f : ℕ → ThresholdHilbert) (i : ℕ) :
    closedRepairTail f i = (repairTailSpan f i).topologicalClosure := by
  exact Submodule.orthogonal_orthogonal_eq_closure _

 theorem repairTailSpan_antitone (f : ℕ → ThresholdHilbert) : Antitone (repairTailSpan f) := by
  intro i j hij
  apply Submodule.span_mono
  rintro y ⟨k, hk, rfl⟩
  exact ⟨k, le_trans hij hk, rfl⟩

 theorem closedRepairTail_antitone (f : ℕ → ThresholdHilbert) : Antitone (closedRepairTail f) := by
  intro i j hij x hx y hy
  apply hx
  intro z hz
  exact hy z (repairTailSpan_antitone f hij hz)

 theorem repairGenerator_mem_closedRepairTail (f : ℕ → ThresholdHilbert)
    (i j : ℕ) (hij : i ≤ j) : f j ∈ closedRepairTail f i := by
  intro y hy
  rw [real_inner_comm]
  exact hy _ (Submodule.subset_span ⟨j, hij, rfl⟩)

 theorem repairTailSpan_head_zero (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i k : ℕ) (hki : k < i) : paretoPointHilbert k ∈ (repairTailSpan f i)ᗮ := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨j, hj, rfl⟩ := hz
      rw [inner_paretoPoint, htri j k (lt_of_lt_of_le hki hj), mul_zero]
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
  | smul c x hx ih => simp [real_inner_smul_left, ih]

/-- Continuity of physical evaluations is implemented by the actual point duals. -/
 theorem closedRepairTail_head_zero (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i k : ℕ) (hki : k < i) (x : ThresholdHilbert) (hx : x ∈ closedRepairTail f i) :
    hilbertGibbsPhysical x k = 0 := by
  have h := hx _ (repairTailSpan_head_zero f htri i k hki)
  rw [real_inner_comm, inner_paretoPoint] at h
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (paretoWeight_pos k))

/-- Any coordinate annihilating every generating future repair also annihilates
the complete future span. The physical anchor need not equal the enumeration index. -/
theorem closedRepairTail_coordinate_zero (f : ℕ → ThresholdHilbert) (i k : ℕ)
    (hzero : ∀ j, i ≤ j → hilbertGibbsPhysical (f j) k = 0)
    (x : ThresholdHilbert) (hx : x ∈ closedRepairTail f i) :
    hilbertGibbsPhysical x k = 0 := by
  have hp : paretoPointHilbert k ∈ (repairTailSpan f i)ᗮ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        rw [inner_paretoPoint, hzero j hj, mul_zero]
    | zero => simp
    | add a b ha hb iha ihb => simp [inner_add_left, iha, ihb]
    | smul c a ha ih => simp [real_inner_smul_left, ih]
  have h := hx _ hp
  rw [real_inner_comm, inner_paretoPoint] at h
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (paretoWeight_pos k))

/-- Strictly increasing physical anchors imply the weak triangular condition
used by the closed-tail exhaustion theorem. This covers sparse prime indexing. -/
theorem repair_triangular_of_strict_anchors (f : ℕ → ThresholdHilbert) (anchor : ℕ → ℕ)
    (ha : StrictMono anchor)
    (hh : ∀ i k, k < anchor i → hilbertGibbsPhysical (f i) k = 0) :
    ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0 := by
  have hle : ∀ i, i ≤ anchor i := by
    intro i
    induction i with
    | zero => omega
    | succ i ih =>
        change i+1 ≤ anchor (i+1)
        have h : anchor i < anchor (i+1) := ha (by omega)
        omega
  intro i k hk
  exact hh i k (lt_of_lt_of_le hk (hle i))

/-- No nonzero vector survives every closed arithmetic tail. -/
 theorem closedRepairTail_intersection_zero (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (x : ThresholdHilbert) (hx : ∀ i, x ∈ closedRepairTail f i) : x = 0 := by
  apply Subtype.ext
  funext k
  have hz := closedRepairTail_head_zero f htri (k+1) k (by omega) x (hx (k+1))
  unfold hilbertGibbsPhysical at hz
  have hs : Real.sqrt (paretoWeight k) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos k))
  change x k = 0
  exact (div_eq_zero_iff.mp hz).resolve_right hs

 theorem closedRepairTail_iInf_eq_bot (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0) :
    (⨅ i, closedRepairTail f i) = ⊥ := by
  apply le_antisymm
  · intro x hx
    exact closedRepairTail_intersection_zero f htri x (by simpa using hx)
  · exact bot_le

/-- A physical coordinate is bounded by its exact weighted contribution to the
complete norm, for every Hilbert vector, including unbounded physical sequences. -/
 theorem hilbert_coordinate_energy_le (x : ThresholdHilbert) (k : ℕ) :
    paretoWeight k * hilbertGibbsPhysical x k ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [hilbertGibbsPhysical_square, hilbert_norm_sq]
  have hs := (hilbert_coordinate_square_summable x).sum_le_tsum ({k} : Finset ℕ)
    (fun j _ => sq_nonneg (x j))
  simpa using hs

/-- Subtracting any actual closed future-tail vector preserves every earlier
coordinate; this includes both finite and infinite orthogonal projections. -/
 theorem closedRepairTail_sub_preserves_head (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i k : ℕ) (hki : k < i) (x y : ThresholdHilbert) (hy : y ∈ closedRepairTail f i) :
    hilbertGibbsPhysical (x-y) k = hilbertGibbsPhysical x k := by
  have hz := closedRepairTail_head_zero f htri i k hki y hy
  change (x k - y k) / Real.sqrt (paretoWeight k) = _
  rw [sub_div]
  change hilbertGibbsPhysical x k - hilbertGibbsPhysical y k = _
  rw [hz, sub_zero]

 theorem closedRepairTail_pivot_lower (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i : ℕ) (y : ThresholdHilbert) (hy : y ∈ closedRepairTail f (i+1)) :
    paretoWeight i * hilbertGibbsPhysical (f i) i ^ 2 ≤ ‖f i-y‖^2 := by
  have h := hilbert_coordinate_energy_le (f i-y) i
  rw [closedRepairTail_sub_preserves_head f htri (i+1) i (by omega) (f i) y hy] at h
  exact h

 theorem closedRepairTail_pivot_ne_zero (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i : ℕ) (hi : hilbertGibbsPhysical (f i) i ≠ 0)
    (y : ThresholdHilbert) (hy : y ∈ closedRepairTail f (i+1)) : f i-y ≠ 0 := by
  have h := closedRepairTail_pivot_lower f htri i y hy
  have hp : 0 < paretoWeight i * hilbertGibbsPhysical (f i) i ^ 2 :=
    mul_pos (paretoWeight_pos i) (sq_pos_of_ne_zero hi)
  intro hz
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  linarith

instance closedRepairTail_hasOrthogonalProjection (f : ℕ → ThresholdHilbert) (i : ℕ) :
    (closedRepairTail f i).HasOrthogonalProjection := by
  unfold closedRepairTail
  infer_instance

/-- The genuine bounded orthogonal projection onto the complete future tail. -/
def closedRepairProjection (f : ℕ → ThresholdHilbert) (i : ℕ) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (closedRepairTail f i).starProjection

theorem closedRepairProjection_mem (f : ℕ → ThresholdHilbert) (i : ℕ)
    (x : ThresholdHilbert) : closedRepairProjection f i x ∈ closedRepairTail f i :=
  Submodule.starProjection_apply_mem _ _

theorem closedRepairProjection_orthogonal (f : ℕ → ThresholdHilbert) (i : ℕ)
    (x y : ThresholdHilbert) (hy : y ∈ closedRepairTail f i) :
    inner ℝ (x - closedRepairProjection f i x) y = 0 :=
  Submodule.starProjection_inner_eq_zero x y hy

theorem closedRepairProjection_norm_le (f : ℕ → ThresholdHilbert) (i : ℕ)
    (x : ThresholdHilbert) : ‖closedRepairProjection f i x‖ ≤ ‖x‖ :=
  Submodule.norm_starProjection_apply_le _ _

/-- The infinite reverse pivot is constructed, rather than postulated. -/
def infiniteRepairPivot (f : ℕ → ThresholdHilbert) (i : ℕ) : ThresholdHilbert :=
  f i - closedRepairProjection f (i+1) (f i)

theorem infiniteRepairPivot_mem (f : ℕ → ThresholdHilbert) (i : ℕ) :
    infiniteRepairPivot f i ∈ closedRepairTail f i :=
  (closedRepairTail f i).sub_mem
    (repairGenerator_mem_closedRepairTail f i i le_rfl)
    (closedRepairTail_antitone f (Nat.le_succ i) (closedRepairProjection_mem f (i+1) (f i)))

theorem infiniteRepairPivot_orthogonal_tail (f : ℕ → ThresholdHilbert) (i : ℕ)
    (y : ThresholdHilbert) (hy : y ∈ closedRepairTail f (i+1)) :
    inner ℝ (infiniteRepairPivot f i) y = 0 :=
  closedRepairProjection_orthogonal f (i+1) (f i) y hy

theorem infiniteRepairPivot_head (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i k : ℕ) (hk : k ≤ i) :
    hilbertGibbsPhysical (infiniteRepairPivot f i) k = hilbertGibbsPhysical (f i) k :=
  closedRepairTail_sub_preserves_head f htri (i+1) k (by omega) _ _
    (closedRepairProjection_mem f (i+1) (f i))

theorem infiniteRepairPivot_ne_zero (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (i : ℕ) (hi : hilbertGibbsPhysical (f i) i ≠ 0) : infiniteRepairPivot f i ≠ 0 :=
  closedRepairTail_pivot_ne_zero f htri i hi _
    (closedRepairProjection_mem f (i+1) (f i))

/-- Preserve any physical anchor that is zero on every later generator. -/
theorem infiniteRepairPivot_anchor (f : ℕ → ThresholdHilbert) (i k : ℕ)
    (hz : ∀ j, i < j → hilbertGibbsPhysical (f j) k = 0) :
    hilbertGibbsPhysical (infiniteRepairPivot f i) k = hilbertGibbsPhysical (f i) k := by
  have hp := closedRepairTail_coordinate_zero f (i+1) k hz _
    (closedRepairProjection_mem f (i+1) (f i))
  change ((f i) k - (closedRepairProjection f (i+1) (f i)) k) /
    Real.sqrt (paretoWeight k) = _
  rw [sub_div]
  change hilbertGibbsPhysical (f i) k -
    hilbertGibbsPhysical (closedRepairProjection f (i+1) (f i)) k = _
  rw [hp, sub_zero]

theorem infiniteRepairPivot_ne_zero_at_anchor (f : ℕ → ThresholdHilbert) (i k : ℕ)
    (hz : ∀ j, i < j → hilbertGibbsPhysical (f j) k = 0)
    (ha : hilbertGibbsPhysical (f i) k ≠ 0) : infiniteRepairPivot f i ≠ 0 := by
  intro h
  have he := infiniteRepairPivot_anchor f i k hz
  rw [h] at he
  have hzero : hilbertGibbsPhysical (0 : ThresholdHilbert) k = 0 := by simp [hilbertGibbsPhysical]
  rw [hzero] at he
  exact ha he.symm

theorem infiniteRepairPivot_inner_of_lt (f : ℕ → ThresholdHilbert)
    (i j : ℕ) (hij : i < j) :
    inner ℝ (infiniteRepairPivot f i) (infiniteRepairPivot f j) = 0 :=
  infiniteRepairPivot_orthogonal_tail f i _
    (closedRepairTail_antitone f hij (infiniteRepairPivot_mem f j))

theorem infiniteRepairPivot_pairwise_orthogonal (f : ℕ → ThresholdHilbert) :
    Pairwise (fun i j => inner ℝ (infiniteRepairPivot f i) (infiniteRepairPivot f j) = 0) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact infiniteRepairPivot_inner_of_lt f i j h
  · rw [real_inner_comm]
    exact infiniteRepairPivot_inner_of_lt f j i h

theorem closedRepairProjection_energy (f : ℕ → ThresholdHilbert) (i : ℕ)
    (x : ThresholdHilbert) :
    ‖x‖^2 = ‖x - closedRepairProjection f i x‖^2 + ‖closedRepairProjection f i x‖^2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x (closedRepairTail f i)
  rw [Submodule.starProjection_orthogonal_val] at h
  simpa only [closedRepairProjection, add_comm] using h

theorem infiniteRepairPivot_energy (f : ℕ → ThresholdHilbert) (i : ℕ) :
    ‖f i‖^2 = ‖infiniteRepairPivot f i‖^2 + ‖closedRepairProjection f (i+1) (f i)‖^2 :=
  closedRepairProjection_energy f (i+1) (f i)

/-- Increasing complements of the closed triangular tails exhaust the whole Hilbert space. -/
theorem closedRepairTail_complements_dense (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0) :
    (⨆ i, (closedRepairTail f i)ᗮ).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm
  · intro x hx
    apply closedRepairTail_intersection_zero f htri
    intro i
    have hx' : x ∈ (closedRepairTail f i)ᗮᗮ := by
      intro y hy
      exact hx y ((le_iSup (fun j => (closedRepairTail f j)ᗮ) i) hy)
    simpa using hx'
  · exact bot_le

/-- The actual projections of every fixed vector onto the closed tails tend to zero. -/
theorem closedRepairProjection_tendsto_zero (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (x : ThresholdHilbert) :
    Filter.Tendsto (fun i => closedRepairProjection f i x) Filter.atTop (nhds 0) := by
  have hmono : Monotone (fun i => (closedRepairTail f i)ᗮ) := by
    intro i j hij y hy z hz
    exact hy z (closedRepairTail_antitone f hij hz)
  have h := Submodule.starProjection_tendsto_self
    (fun i => (closedRepairTail f i)ᗮ) hmono x
    (le_of_eq (closedRepairTail_complements_dense f htri).symm)
  have he : (fun i => x - (closedRepairTail f i)ᗮ.starProjection x) =
      (fun i => closedRepairProjection f i x) := by
    funext i
    rw [Submodule.starProjection_orthogonal_val]
    dsimp [closedRepairProjection]
    abel
  have ht : Filter.Tendsto (fun i => x - (closedRepairTail f i)ᗮ.starProjection x)
      Filter.atTop (nhds (x-x)) := tendsto_const_nhds.sub h
  simpa only [he, sub_self] using ht

/-- A moving projection tends to zero whenever the vectors themselves converge.
The fixed-vector theorem and the contraction bound are both essential. -/
theorem closedRepairProjection_moving_tendsto_zero (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (F : ℕ → ThresholdHilbert) (x : ThresholdHilbert)
    (hF : Filter.Tendsto F Filter.atTop (nhds x)) :
    Filter.Tendsto (fun i => closedRepairProjection f i (F i)) Filter.atTop (nhds 0) := by
  have hd : Filter.Tendsto (fun i => ‖F i - x‖) Filter.atTop (nhds 0) := by
    simpa using (hF.sub_const x).norm
  have hz : Filter.Tendsto (fun i => closedRepairProjection f i (F i-x))
      Filter.atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun i => norm_nonneg _)
      (fun i => closedRepairProjection_norm_le f i (F i-x)) hd
  have hs := hz.add (closedRepairProjection_tendsto_zero f htri x)
  simpa only [map_sub, sub_add_cancel, add_zero] using hs

/-- Exact convergence criterion with the actual moving boundary. This theorem
does not assert that coordinatewise matching makes the boundary vanish. -/
theorem closedRepairProjection_convergence_iff (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (F : ℕ → ThresholdHilbert) (x : ThresholdHilbert) :
    Filter.Tendsto F Filter.atTop (nhds x) ↔
      Filter.Tendsto (fun i => F i - closedRepairProjection f i (F i))
        Filter.atTop (nhds x) ∧
      Filter.Tendsto (fun i => closedRepairProjection f i (F i))
        Filter.atTop (nhds 0) := by
  constructor
  · intro hF
    have hB := closedRepairProjection_moving_tendsto_zero f htri F x hF
    exact ⟨by simpa only [sub_zero] using hF.sub hB, hB⟩
  · rintro ⟨hA, hB⟩
    simpa only [sub_add_cancel, add_zero] using hA.add hB

/-- Inside one tail, being orthogonal to its reverse pivot is exactly membership
in the next tail. This supplies the one-dimensional quotient without assuming it. -/
theorem closedRepairTail_mem_next_of_pivot_orthogonal (f : ℕ → ThresholdHilbert)
    (i : ℕ) (x : ThresholdHilbert) (hx : x ∈ closedRepairTail f i)
    (hv : inner ℝ x (infiniteRepairPivot f i) = 0) :
    x ∈ closedRepairTail f (i+1) := by
  let z := x - closedRepairProjection f (i+1) x
  have hzmem : z ∈ closedRepairTail f i :=
    (closedRepairTail f i).sub_mem hx
      (closedRepairTail_antitone f (Nat.le_succ i) (closedRepairProjection_mem f (i+1) x))
  have hztail : ∀ y ∈ closedRepairTail f (i+1), inner ℝ z y = 0 :=
    fun y hy => closedRepairProjection_orthogonal f (i+1) x y hy
  have hvi : inner ℝ (infiniteRepairPivot f i) z = 0 := by
    dsimp [z]
    rw [inner_sub_right, real_inner_comm x (infiniteRepairPivot f i), hv,
      infiniteRepairPivot_orthogonal_tail f i _ (closedRepairProjection_mem f (i+1) x),
      sub_self]
  have hfi : inner ℝ (f i) z = 0 := by
    have he : f i = infiniteRepairPivot f i + closedRepairProjection f (i+1) (f i) := by
      unfold infiniteRepairPivot
      abel
    rw [he, inner_add_left, hvi, zero_add, real_inner_comm]
    exact hztail _ (closedRepairProjection_mem f (i+1) (f i))
  have hzorth : z ∈ (repairTailSpan f i)ᗮ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        change i ≤ j at hj
        rcases eq_or_lt_of_le hj with he | he
        · subst j
          exact hfi
        · rw [real_inner_comm]
          exact hztail _ (repairGenerator_mem_closedRepairTail f (i+1) j he)
    | zero => simp
    | add a b ha hb iha ihb => simp [inner_add_left, iha, ihb]
    | smul c a ha ih => simp [real_inner_smul_left, ih]
  have hz : z = 0 := by
    have hself := hzmem z hzorth
    exact inner_self_eq_zero.mp hself
  have he : x = closedRepairProjection f (i+1) x := sub_eq_zero.mp hz
  rw [he]
  exact closedRepairProjection_mem f (i+1) x

/-- The constructed pivots are total in the original closed triangular span. -/
theorem infiniteRepairPivot_total (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0)
    (x : ThresholdHilbert) (hx : x ∈ closedRepairTail f 0)
    (ho : ∀ i, inner ℝ x (infiniteRepairPivot f i) = 0) : x = 0 := by
  apply closedRepairTail_intersection_zero f htri
  intro i
  induction i with
  | zero => exact hx
  | succ i ih => exact closedRepairTail_mem_next_of_pivot_orthogonal f i x ih (ho i)

def infiniteRepairPivotSpan (f : ℕ → ThresholdHilbert) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (infiniteRepairPivot f))

theorem infiniteRepairPivotSpan_orthogonal (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0) :
    (infiniteRepairPivotSpan f)ᗮ = (closedRepairTail f 0)ᗮ := by
  apply le_antisymm
  · intro x hx y hy
    have hpzero : closedRepairProjection f 0 x = 0 := by
      apply infiniteRepairPivot_total f htri _ (closedRepairProjection_mem f 0 x)
      intro i
      have hvi : infiniteRepairPivot f i ∈ closedRepairTail f 0 :=
        closedRepairTail_antitone f (Nat.zero_le i) (infiniteRepairPivot_mem f i)
      have hfixed : closedRepairProjection f 0 (infiniteRepairPivot f i) =
          infiniteRepairPivot f i := Submodule.starProjection_eq_self_iff.mpr hvi
      have hsym := (closedRepairTail f 0).starProjection_isSymmetric x (infiniteRepairPivot f i)
      change inner ℝ (closedRepairProjection f 0 x) (infiniteRepairPivot f i) =
        inner ℝ x (closedRepairProjection f 0 (infiniteRepairPivot f i)) at hsym
      rw [hsym, hfixed, real_inner_comm]
      exact hx _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := closedRepairProjection_orthogonal f 0 x y hy
    rw [hpzero, sub_zero, real_inner_comm] at h
    exact h
  · intro x hx y hy
    have hspan : infiniteRepairPivotSpan f ≤ closedRepairTail f 0 := by
      apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      exact closedRepairTail_antitone f (Nat.zero_le i) (infiniteRepairPivot_mem f i)
    exact hx y (hspan hy)

/-- No completeness hypothesis on the pivot family is assumed: its closed span
is proved equal to the actual closed span of the original generators. -/
theorem infiniteRepairPivotSpan_closure (f : ℕ → ThresholdHilbert)
    (htri : ∀ i k, k < i → hilbertGibbsPhysical (f i) k = 0) :
    (infiniteRepairPivotSpan f).topologicalClosure = closedRepairTail f 0 := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    infiniteRepairPivotSpan_orthogonal f htri, Submodule.orthogonal_orthogonal]

private theorem infiniteRepairPivot_orthogonalFamily (f : ℕ → ThresholdHilbert) :
    OrthogonalFamily ℝ
      (fun i => Submodule.span ℝ ({infiniteRepairPivot f i} : Set ThresholdHilbert))
      (fun i => (Submodule.span ℝ ({infiniteRepairPivot f i} : Set ThresholdHilbert)).subtypeₗᵢ) := by
  intro i j hij x y
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
  change inner ℝ (x : ThresholdHilbert) (y : ThresholdHilbert) = 0
  rw [← ha, ← hb, real_inner_smul_left, real_inner_smul_right,
    infiniteRepairPivot_pairwise_orthogonal f hij, mul_zero, mul_zero]

/-- Orthogonal pivot coefficients have exactly their weighted diagonal energy. -/
theorem infiniteRepairPivot_finite_energy (f : ℕ → ThresholdHilbert)
    (a : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ i ∈ s, a i • infiniteRepairPivot f i‖^2 =
      ∑ i ∈ s, ‖infiniteRepairPivot f i‖^2 * a i^2 := by
  let u (i : ℕ) : Submodule.span ℝ ({infiniteRepairPivot f i} : Set ThresholdHilbert) :=
    ⟨a i • infiniteRepairPivot f i,
      (Submodule.span ℝ ({infiniteRepairPivot f i} : Set ThresholdHilbert)).smul_mem (a i)
        (Submodule.subset_span (by simp))⟩
  have h := (infiniteRepairPivot_orthogonalFamily f).norm_sum u s
  change ‖∑ i ∈ s, a i • infiniteRepairPivot f i‖^2 =
    ∑ i ∈ s, ‖a i • infiniteRepairPivot f i‖^2 at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- The exact diagonal summability criterion for the constructed infinite
pivots. The original generators require an additional moving boundary. -/
theorem infiniteRepairPivot_summable_iff (f : ℕ → ThresholdHilbert)
    (a : ℕ → ℝ) :
    Summable (fun i => a i • infiniteRepairPivot f i) ↔
      Summable (fun i => ‖infiniteRepairPivot f i‖^2 * a i^2) := by
  let u (i : ℕ) : Submodule.span ℝ ({infiniteRepairPivot f i} : Set ThresholdHilbert) :=
    ⟨a i • infiniteRepairPivot f i,
      (Submodule.span ℝ ({infiniteRepairPivot f i} : Set ThresholdHilbert)).smul_mem (a i)
        (Submodule.subset_span (by simp))⟩
  have h := (infiniteRepairPivot_orthogonalFamily f).summable_iff_norm_sq_summable u
  change Summable (fun i => a i • infiniteRepairPivot f i) ↔
    Summable (fun i => ‖a i • infiniteRepairPivot f i‖^2) at h
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm] using h

end
end RiemannResearch.RH.Pareto
