import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Packing strict positive gaps among a selected set of distinct real heights -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.MicroscopicPacking

/-- Distinct selected ordinates in [0,T] force genuine one-sided pairs. Each
selected ordinate with no successor in its window occupies a different bin. -/
theorem strict_pair_packing {ι : Type*} [Fintype ι] (s : Finset ι) (x : ι → ℝ)
    (hinj : Set.InjOn x s) {T w : ℝ} (hT : 0 ≤ T) (hw : 0 < w)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ T) :
    (s.card : ℝ) ≤ T / w + 1 +
      ∑ i : ι, ∑ j : ι, if 0 < x j - x i ∧ x j - x i ≤ w then (1 : ℝ) else 0 := by
  classical
  let R := fun i j => 0 < x j - x i ∧ x j - x i ≤ w
  let a := s.filter fun i => ∀ j, ¬ R i j
  let b := fun i => ⌊x i / w⌋₊
  have ha {i} (hi : i ∈ a) : i ∈ s ∧ ∀ j, ¬ R i j := Finset.mem_filter.mp hi
  have hr (i) : 0 ≤ ∑ j : ι, if R i j then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have same {i j} (hi : i ∈ a) (hj : j ∈ a) (h : b i = b j) : x j - x i < w := by
    have h0 := Nat.floor_le (div_nonneg (hx i (ha hi).1).1 hw.le)
    change (b i : ℝ) ≤ x i / w at h0
    have h1 : x j / w < (b j : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [← h] at h1
    have h2 := (le_div_iff₀ hw).mp h0
    have h3 := (div_lt_iff₀ hw).mp h1
    linarith only [h2,h3]
  have hb : Set.InjOn b a := by
    intro i hi j hj h
    apply hinj (ha hi).1 (ha hj).1
    rcases lt_trichotomy (x i) (x j) with hlt | heq | hgt
    · exact False.elim ((ha hi).2 j ⟨sub_pos.mpr hlt, (same hi hj h).le⟩)
    · exact heq
    · exact False.elim ((ha hj).2 i ⟨sub_pos.mpr hgt, (same hj hi h.symm).le⟩)
  have hsub : a.image b ⊆ Finset.range (⌊T / w⌋₊ + 1) := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (hx i (ha hi).1).2 hw.le))
  have hn : a.card ≤ ⌊T / w⌋₊ + 1 := by
    simpa only [Finset.card_image_of_injOn hb, Finset.card_range] using Finset.card_le_card hsub
  have hm : ((s \ a).card : ℝ) ≤ ∑ i : ι, ∑ j : ι, if R i j then (1 : ℝ) else 0 := by
    calc
      _ = ∑ _i ∈ s \ a, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ s \ a, ∑ j : ι, if R i j then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨his,hia⟩ := Finset.mem_sdiff.mp hi
        have hex : ∃ j, R i j := by
          by_contra! hh
          exact hia (Finset.mem_filter.mpr ⟨his,hh⟩)
        obtain ⟨j,hj⟩ := hex
        have h := Finset.single_le_sum (f := fun k => if R i k then (1 : ℝ) else 0)
          (s := Finset.univ) (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
        simpa only [if_pos hj] using h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hr i)
  have hf := Nat.floor_le (div_nonneg hT hw.le)
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ s : a ⊆ s)
  have hn' : (a.card : ℝ) ≤ (⌊T / w⌋₊ : ℝ) + 1 := by exact_mod_cast hn
  have hc' : ((s \ a).card : ℝ) + a.card = s.card := by exact_mod_cast hc
  change (s.card : ℝ) ≤ T/w + 1 + ∑ i : ι, ∑ j : ι, if R i j then (1:ℝ) else 0
  linarith
/-- The denominator is the length of the selected physical height interval.
Both labels in the lower bound belong to the selected finite sample. -/
theorem strict_pair_packing_in_band {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hinj : Set.InjOn x s) {a b w : ℝ} (hab : a ≤ b) (hw : 0 < w)
    (hx : ∀ i ∈ s, x i ∈ Set.Icc a b) :
    (s.card : ℝ) ≤ (b-a)/w + 1 +
      ∑ i : s, ∑ j : s, if 0 < x j.val - x i.val ∧ x j.val - x i.val ≤ w then (1 : ℝ) else 0 := by
  classical
  have hi : Set.InjOn (fun i : s => x i.val - a) Set.univ := by
    intro i _ j _ h
    exact Subtype.ext (hinj i.property j.property (sub_left_inj.mp h))
  have h := strict_pair_packing (Finset.univ : Finset s) (fun i => x i.val - a)
    (by simpa only [Finset.coe_univ] using hi) (sub_nonneg.mpr hab) hw (fun i _ => ⟨sub_nonneg.mpr (hx _ i.property).1,
      sub_le_sub_right (hx _ i.property).2 _⟩)
  simpa only [Finset.card_univ, Fintype.card_coe, sub_sub_sub_cancel_right] using h

end RiemannResearch.Analysis.MicroscopicPacking
