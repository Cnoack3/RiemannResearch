import RiemannResearch.Analysis.MicroscopicRankCover
import RiemannResearch.Analysis.ZeroDPPRankVacancy
import RiemannResearch.Analysis.MicroscopicRankTail

/-!
# Rank splitting for deleted zero occurrences

The argument in the 2026-11-25 microscopic Selberg research note applies
separately to each subset of deleted chronological labels. Pairs of distinct
labels at a common ordinate are counted, with one orientation per pair.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.MicroscopicRankDeletion
open ActualZeroOrdinate MicroscopicRankCover ZeroDPPCollisionLoss ZeroDPPRankVacancy

/-- Count all admissible pairs of labels with at least one endpoint in the deletion set. -/
def deletedPairCount (n : ℕ) (S : Finset ℕ) (x : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    if i < j ∧ x j - x i ≤ h ∧ (i ∈ S ∨ j ∈ S) then 1 else 0

/-- At short ranks each deleted label is charged at most twice the cutoff.
At long ranks the collision-inclusive tail bounds all affected pairs. -/
theorem deletedPairCount_le (n J : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n)
    (x : ℕ → ℝ) (h : ℝ) :
    deletedPairCount n S x h ≤ 2 * (J : ℝ) * S.card + rankTailCount n J x h := by
  classical
  let r := Finset.range n
  let a := fun i j : ℕ => i < j ∧ j ≤ i + J
  let u := fun i j : ℕ => if i ∈ S ∧ a i j then (1 : ℝ) else 0
  let v := fun i j : ℕ => if j ∈ S ∧ a i j then (1 : ℝ) else 0
  let f := fun i j : ℕ => if i + J < j ∧ x j - x i ≤ h then (1 : ℝ) else 0
  have hpoint (i j : ℕ) :
      (if i < j ∧ x j - x i ≤ h ∧ (i ∈ S ∨ j ∈ S) then (1:ℝ) else 0)
        ≤ u i j + v i j + f i j := by
    dsimp [u,v,f,a]
    split_ifs <;> norm_num <;> grind
  have hrow (i : ℕ) : (∑ j ∈ r, (u i j + v j i)) ≤ if i ∈ S then 2 * (J : ℝ) else 0 := by
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      let p := fun j : ℕ => (j < i ∧ i ≤ j+J) ∨ (i < j ∧ j ≤ i+J)
      have he (j : ℕ) : u i j + v j i = if p j then (1:ℝ) else 0 := by
        dsimp [u,v,p,a]
        simp only [hi, true_and]
        split_ifs <;> norm_num <;> grind
      simp_rw [he]
      have hn : (r.filter p).card ≤ 2*J := smallRankDegree_le n i J
      rw [← Finset.sum_filter]
      simpa using (show ((r.filter p).card : ℝ) ≤ (2:ℝ) * J from by exact_mod_cast hn)
    · simp [u,v,hi]
  have htotal : (∑ i ∈ r, if i ∈ S then 2 * (J:ℝ) else 0) = 2 * (J : ℝ) * S.card := by
    have hs : r.filter (fun i => i ∈ S) = S := by
      ext i
      exact Finset.mem_filter.trans ⟨And.right, fun hi => ⟨hS hi, hi⟩⟩
    rw [← Finset.sum_filter, hs]
    simp [mul_comm]
  calc
    deletedPairCount n S x h ≤ ∑ i ∈ r, ∑ j ∈ r, (u i j + v i j + f i j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
    _ = (∑ i ∈ r, ∑ j ∈ r, (u i j + v j i)) + rankTailCount n J x h := by
      have hswap : (∑ i ∈ r, ∑ j ∈ r, v i j) = ∑ i ∈ r, ∑ j ∈ r, v j i := Finset.sum_comm
      dsimp only [rankTailCount]
      simp_rw [Finset.sum_add_distrib]
      rw [hswap]
    _ ≤ _ := add_le_add ((Finset.sum_le_sum fun i _ => hrow i).trans_eq htotal) le_rfl

/-- Uniform at a given height over all deletion sets, using the same normalizer as PCC. -/
theorem normalized_deletedPairCount_le {T : ℝ} (hT : 1 < T) (q : ℝ) (J : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Finset.range (Ncount 0 T)) :
    deletedPairCount (Ncount 0 T) S (cutoffOrdinate T) (q / (Real.log T / (2 * Real.pi))) /
      normalizer T ≤ 2 * (J:ℝ) * ((S.card : ℝ) / normalizer T) + actualRankTail T q J := by
  have hD : 0 ≤ normalizer T :=
    (div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)).le
  exact (div_le_div_of_nonneg_right (deletedPairCount_le _ J S hS _ _) hD).trans_eq
    (by unfold actualRankTail; ring)



theorem eventually_deletedPairCount_log {q : ℝ} (hq : 0 < q)
    (he : ExpTranslatedSquareTail (2*q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ S : Finset ℕ,
      S ⊆ Finset.range (Ncount 0 T) →
      let d := (S.card : ℝ) / normalizer T
      d ≤ 1 → deletedPairCount (Ncount 0 T) S (cutoffOrdinate T)
        (q / (Real.log T / (2 * Real.pi))) / normalizer T ≤ C*d*(1-Real.log d) := by
  obtain ⟨A,c,hA,hc,hE⟩ := eventually_rankTail_le_exp hq he
  let C := 2+2/c+A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ), hE] with T ht htail
  intro S hS
  let d := (S.card : ℝ) / normalizer T
  change d ≤ 1 → _ ≤ C*d*(1-Real.log d)
  intro hu
  by_cases hS0 : S = ∅
  · subst S
    simp [deletedPairCount,d]
  have hD : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans ht) (Real.log_pos ht)) (by positivity)
  have hd : 0 < d :=
    div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0))) hD
  have hlog : 0 ≤ -Real.log d := neg_nonneg.mpr (Real.log_nonpos hd.le hu)
  let u := -Real.log d / c
  let J := ⌊u⌋₊ + 1
  have hjlo : u ≤ (J : ℝ) := by simpa [J] using (Nat.lt_floor_add_one u).le
  have hjhi : (J : ℝ) ≤ u+1 := by
    simp only [J,Nat.cast_add,Nat.cast_one]
    exact add_le_add (Nat.floor_le (div_nonneg hlog hc.le)) le_rfl
  have hexp : Real.exp (-(c*(J:ℝ))) ≤ d := by
    rw [← Real.exp_log hd]
    apply Real.exp_le_exp.mpr
    have h := (div_le_iff₀ hc).mp hjlo
    linarith only [h]
  calc
    _ ≤ 2*(J:ℝ)*d + actualRankTail T q J := normalized_deletedPairCount_le ht q J S hS
    _ ≤ 2*(u+1)*d + A*d :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjhi (by norm_num)) hd.le)
        ((htail J).trans (mul_le_mul_of_nonneg_left hexp hA))
    _ ≤ C*d*(1-Real.log d) := by
      have hr : C*d*(1-Real.log d) - (2*(u+1)*d + A*d) =
          d*(2/c+(2+A)*(-Real.log d)) := by dsimp [C,u]; ring
      apply sub_nonneg.mp
      rw [hr]
      exact mul_nonneg hd.le (add_nonneg (div_nonneg (by norm_num) hc.le)
        (mul_nonneg (add_nonneg (by norm_num) hA) hlog))

end RiemannResearch.Analysis.MicroscopicRankDeletion
