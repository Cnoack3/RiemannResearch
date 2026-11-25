import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import RiemannResearch.Analysis.ActualSmallGapProportion
import RiemannResearch.Analysis.ActualZeroWindowVariance
import RiemannResearch.Analysis.LamzouriGap285OriginalReplay
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Consecutive-occurrence contributions to the microscopic window variance

The exact finite square separates self-pairs, the two orientations of every
consecutive pair, and the two orientations of every remaining pair. Equal heights
of distinct occurrences contribute their full triangle weight. A lower bound
for the proportion of small internal gaps therefore supplies an explicit
variance floor at every larger fixed width. The positive-proportion statistic
is the one used by Lamzouri, arXiv:2611.14486, Theorem 1.1.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroWindowVariance

private theorem symmetric_range_square (w : ℕ → ℕ → ℝ)
    (hs : ∀ i j, w i j = w j i) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, w i j) =
      (∑ j ∈ Finset.range n, w j j) +
      2 * ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, w i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (∑ j ∈ Finset.range n, w n j) = ∑ j ∈ Finset.range n, w j n :=
      Finset.sum_congr rfl (fun j _ => hs n j)
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib, ih, hc]
    ring

private theorem split_ascending_rows (w : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, w i j) =
      (∑ i ∈ Finset.range (n - 1), w i (i + 1)) +
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range (j - 1), w i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ k =>
      rw [Finset.sum_range_succ (fun j => ∑ i ∈ Finset.range j, w i j) (k + 1), ih,
        Finset.sum_range_succ (fun j => ∑ i ∈ Finset.range (j - 1), w i j) (k + 1)]
      simp only [Nat.succ_sub_one]
      rw [Finset.sum_range_succ (fun i => w i (k + 1)),
        Finset.sum_range_succ (fun i => w i (i + 1))]
      ring

/-- Off-diagonal triangle mass from unordered pairs of nonconsecutive occurrences. -/
def nonadjacentTriangle (T h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (Ncount 0 T), ∑ i ∈ Finset.range (j - 1),
    max (h - |cutoffOrdinate T i - cutoffOrdinate T j|) 0

/-- The complete chronological triangle split retains zero gaps and the nonadjacent remainder. -/
theorem actualPhysicalTriangleEnergy_adjacent_split {T h : ℝ} (hh : 0 ≤ h) :
    actualPhysicalTriangleEnergy T h =
      ((Ncount 0 T : ℝ) * h +
        2 * (∑ i ∈ Finset.range (Ncount 0 T - 1), max (h - cutoffGap T i) 0) +
        2 * nonadjacentTriangle T h) / T := by
  classical
  let w := fun i j : ℕ => max (h - |cutoffOrdinate T i - cutoffOrdinate T j|) 0
  have hs : ∀ i j, w i j = w j i := by
    intro i j
    simp only [w, abs_sub_comm (cutoffOrdinate T i) (cutoffOrdinate T j)]
  have hadj : ∀ i, w i (i + 1) = max (h - cutoffGap T i) 0 := by
    intro i
    have hm := cutoffOrdinate_monotone T (Nat.le_succ i)
    simp only [w, abs_of_nonpos (sub_nonpos.mpr hm), cutoffGap]
    congr 2
    ring
  have hrow : (∑ i ∈ Finset.range (Ncount 0 T), ∑ j ∈ Finset.range (Ncount 0 T), w i j) =
      ∑ c : Copies T, ∑ d : Copies T, max (h - |c.1.1.im - d.1.1.im|) 0 := by
    calc
      _ = ∑ i ∈ Finset.range (Ncount 0 T), ∑ d : Copies T,
          max (h - |cutoffOrdinate T i - d.1.1.im|) 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact cutoffOrdinate_sum T (fun x => max (h - |cutoffOrdinate T i - x|) 0)
      _ = _ := cutoffOrdinate_sum T (fun x => ∑ d : Copies T, max (h - |x - d.1.1.im|) 0)
  unfold actualPhysicalTriangleEnergy
  rw [← hrow, symmetric_range_square w hs, split_ascending_rows]
  have hd : ∀ i, w i i = h := by simp [w, max_eq_left hh]
  simp_rw [hd, hadj]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold nonadjacentTriangle
  dsimp only [w]
  ring

/-- The consecutive small-gap contribution in the normalization of the actual count square. -/
theorem unfoldedWindowEnergy_smallGap_lower {T q k : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    unfoldedWindowMean T q + 2 * (q - k) * unfoldedWindowMean T 1 * smallGapFraction k T ≤
      unfoldedWindowEnergy T q := by
  let L := Real.log T / (2 * Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hTp : 0 < T := by linarith
  set h := q / L with heq
  have hh : 0 ≤ h := div_nonneg hq hL.le
  have hcut (i : ℕ) (hi : i ∈ smallGapIndices k T) : cutoffGap T i ≤ k / L := by
    apply (le_div_iff₀ hL).2
    change cutoffGap T i * (Real.log T / (2 * Real.pi)) ≤ k
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)).2
      (by simpa [mul_comm] using (Finset.mem_filter.mp hi).2)
  have hsum : ((smallGapIndices k T).card : ℝ) * (h - k / L) ≤
      ∑ i ∈ Finset.range (Ncount 0 T - 1), max (h - cutoffGap T i) 0 := by
    calc
      _ = ∑ i ∈ smallGapIndices k T, (h - k / L) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ smallGapIndices k T, max (h - cutoffGap T i) 0 :=
        Finset.sum_le_sum (fun i hi => (sub_le_sub_left (hcut i hi) h).trans (le_max_left _ _))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => le_max_right _ _)
  have hn : 0 ≤ nonadjacentTriangle T h :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => le_max_right _ _))
  have hmean : unfoldedWindowMean T q + 2 * (q - k) * unfoldedWindowMean T 1 *
      smallGapFraction k T =
      ((Ncount 0 T : ℝ) * h + 2 * ((smallGapIndices k T).card : ℝ) * (h - k / L)) / T := by
    by_cases hzero : Ncount 0 T = 0
    · have hi : smallGapIndices k T = ∅ := by simp [smallGapIndices, hzero]
      simp [unfoldedWindowMean, smallGapFraction, hzero, hi]
    · have hcount : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hzero
      change (Ncount 0 T : ℝ) * (q / L) / T + 2 * (q - k) *
        ((Ncount 0 T : ℝ) * (1 / L) / T) *
        (((smallGapIndices k T).card : ℝ) / (Ncount 0 T : ℝ)) = _
      rw [heq]
      field_simp [hcount, hL.ne', hTp.ne']
      <;> ring
  change _ ≤ actualPhysicalTriangleEnergy T h
  rw [hmean, actualPhysicalTriangleEnergy_adjacent_split hh]
  apply div_le_div_of_nonneg_right _ hTp.le
  linarith

/-- Every level below the consecutive-gap variance floor holds eventually.
The small-gap proportion is the actual multiplicity-preserving liminf. -/
theorem eventually_unfoldedWindowVariance_smallGap_lower {q k a : ℝ} (hq : 0 ≤ q)
    (hk : k < q) (ha : a < q - q ^ 2 + 2 * (q - k) * smallGapProportion k) :
    ∀ᶠ T : ℝ in atTop, a < unfoldedWindowVariance T q := by
  have hcoef : 0 < 2 * (q - k) := mul_pos (by norm_num) (sub_pos.mpr hk)
  have hsep : (a - (q - q ^ 2)) / (2 * (q - k)) < smallGapProportion k :=
    (div_lt_iff₀ hcoef).2 (by linarith)
  obtain ⟨d, hlow, hhigh⟩ := exists_between hsep
  have hd : a < (q - q ^ 2) + (2 * (q - k) * 1) * d := by
    linarith [(div_lt_iff₀ hcoef).1 hlow]
  have hf : ∀ᶠ T : ℝ in atTop, d < smallGapFraction k T :=
    eventually_lt_of_lt_liminf hhigh
      ⟨0, eventually_map.mpr (Eventually.of_forall (smallGapFraction_nonneg k))⟩
  have hm := ((unfoldedWindowMean_tendsto q).sub ((unfoldedWindowMean_tendsto q).pow 2)).add
    (((unfoldedWindowMean_tendsto 1).const_mul (2 * (q - k))).mul_const d)
  have hev := hm.eventually (lt_mem_nhds hd)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hf, hev,
    eventually_unfoldedWindowEnergy_eq_mean_sq_add_variance hq] with T hT hdT hlim hvar
  change a < unfoldedWindowMean T q - unfoldedWindowMean T q ^ 2 +
    (2 * (q - k) * unfoldedWindowMean T 1) * d at hlim
  have hunit : 0 ≤ unfoldedWindowMean T 1 := by
    unfold unfoldedWindowMean
    have hL := Real.log_pos hT
    have hTp : 0 < T := by linarith
    positivity
  have hfrac := mul_le_mul_of_nonneg_left hdT.le (mul_nonneg hcoef.le hunit)
  have hbound := unfoldedWindowEnergy_smallGap_lower (k := k) hT hq
  linarith

/-- Strictly positive actual count variance at one mean spacing, conditional on
the repository's scoped compact-deletion input. The finite polynomial replay
is supplied by the verified original coefficient arrays. -/
theorem eventually_unfoldedWindowVariance_one_pos_of_compactDeletion
    [LamzouriCompactDeletion2026] :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, c < unfoldedWindowVariance T 1 := by
  have hgap := LamzouriGapKernel285.smallGapProportion_certified285
  let k : ℝ := 392391339 / 500000000
  have hk : k < 1 := by norm_num [k]
  have hp : 0 < (1 - k) * smallGapProportion k := mul_pos (sub_pos.mpr hk) hgap
  refine ⟨_, hp, eventually_unfoldedWindowVariance_smallGap_lower zero_le_one hk ?_⟩
  linarith

end RiemannResearch.Analysis.MontgomeryPositiveGap
