/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualGramTwoNeighborIsolation
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Three and four consecutive moderate gaps in the actual ordered zero array

Angón--Ross--Tang--Zhao, Theorem 1, arXiv:2610.22927v2.
The finite shifted intersection uses all copies sorted by ordinate, including
analytic multiplicities. A two-neighbor lower proportion q implies the lower
proportion 2q−1 for both three and four consecutive gaps. Each gap here
strictly exceeds the prescribed threshold.
-/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The actual zeros in the height cutoff, including analytically distinct
copies at the same ordinate, sorted in nondecreasing order. -/
def orderedCopies (T : ℝ) : Fin (Ncount 0 T) ≃ Copies T :=
  let e := (Fintype.equivFinOfCardEq (card_copies T)).symm
  (Tuple.sort (fun i => copyOrdinate T (e i))).trans e

theorem orderedCopies_monotone (T : ℝ) :
    Monotone (fun i => copyOrdinate T (orderedCopies T i)) := by
  exact Tuple.monotone_sort (fun i =>
    copyOrdinate T ((Fintype.equivFinOfCardEq (card_copies T)).symm i))

private def finiteOrdinate (T : ℝ) (i : ℕ) : ℝ :=
  if hi : i < Ncount 0 T then copyOrdinate T (orderedCopies T ⟨i, hi⟩) else 0

/-- Starting indices for k consecutive gaps wholly inside the finite height
list. Its zero-based starting ordinal j corresponds to the paper's j+1. -/
def moderateGapStarts (T c : ℝ) (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Ncount 0 T)).filter fun i => i + k < Ncount 0 T ∧
    ∀ j : ℕ, j < k → 2 * Real.pi * c / Real.log T <
      finiteOrdinate T (i + j + 1) - finiteOrdinate T (i + j)

def moderateGapProportion (T c : ℝ) (k : ℕ) : ℝ :=
  ((moderateGapStarts T c k).card : ℝ) / (Ncount 0 T : ℝ)

private def isolatedIndices (T c : ℝ) : Finset ℕ := by
  classical
  exact (Finset.univ.filter fun i => KimIsolatedCopy T c (orderedCopies T i)).image Fin.val

private theorem isolatedIndex_mem {T c : ℝ} {i : ℕ} :
    i ∈ isolatedIndices T c ↔ ∃ hi : i < Ncount 0 T,
      KimIsolatedCopy T c (orderedCopies T ⟨i, hi⟩) := by
  classical
  simp only [isolatedIndices, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.isLt, hj⟩
  · rintro ⟨hi, hj⟩
    exact ⟨⟨i, hi⟩, hj, rfl⟩

private theorem isolatedIndices_card (T c : ℝ) :
    ((isolatedIndices T c).card : ℝ) / (Ncount 0 T : ℝ) = kimIsolatedProportion T c := by
  classical
  unfold isolatedIndices kimIsolatedProportion
  rw [Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  rw [← (orderedCopies T).sum_comp (fun j => if KimIsolatedCopy T c j then (1 : ℝ) else 0)]
  simp

private theorem distinct_from_isolated {T c : ℝ} {a b : Copies T}
    (ha : KimIsolatedCopy T c a) (hne : a ≠ b) : b.1.1 ≠ a.1.1 := by
  rintro he
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  have hab : b = a := Subtype.ext he
  subst b
  have h := ha.1
  change zeroMult a.val = 1 at h
  have hi := i.isLt
  have hj := j.isLt
  have hij : i = j := Fin.ext (by omega)
  exact hne (by cases hij; rfl)

private theorem isolated_gap {T c : ℝ} {i j : ℕ} (hi : i ∈ isolatedIndices T c)
    (hj : j < Ncount 0 T) (hne : i ≠ j) :
    2 * Real.pi * c / Real.log T < |finiteOrdinate T j - finiteOrdinate T i| := by
  obtain ⟨hiT, h⟩ := isolatedIndex_mem.mp hi
  let a := orderedCopies T ⟨i, hiT⟩
  let b := orderedCopies T ⟨j, hj⟩
  have hne' : a ≠ b := fun he => hne (congrArg Fin.val ((orderedCopies T).injective he))
  have hmem := mem_cutoff.mp b.1.property
  have hh := h.2.2 b.1.1 hmem.1 hmem.2.1 (distinct_from_isolated h hne')
  simpa only [finiteOrdinate, dif_pos hiT, dif_pos hj, a, b, copyOrdinate] using hh

private theorem finiteOrdinate_mono {T : ℝ} {i j : ℕ} (hij : i ≤ j) (hj : j < Ncount 0 T) :
    finiteOrdinate T i ≤ finiteOrdinate T j := by
  have hi := hij.trans_lt hj
  simpa only [finiteOrdinate, dif_pos hi, dif_pos hj] using
    orderedCopies_monotone T (show (⟨i, hi⟩ : Fin (Ncount 0 T)) ≤ ⟨j, hj⟩ from hij)

/-- At most two full-list isolated indices are lost on requiring both
gaps to lie inside the height cutoff. -/
private theorem finite_two_moderate_gaps (T c : ℝ) :
    (isolatedIndices T c).card ≤ (moderateGapStarts T c 2).card + 2 := by
  classical
  let N := Ncount 0 T
  let I := isolatedIndices T c
  let S := I.filter fun i => 0 < i ∧ i + 1 < N
  have htrim : I.card ≤ S.card + 2 := by
    have hs : I ⊆ S ∪ ({0, N-1} : Finset ℕ) := by
      intro i hi
      have hiN : i < N := (isolatedIndex_mem.mp hi).choose
      by_cases h : 0 < i ∧ i+1 < N
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
      · apply Finset.mem_union_right
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    have hb : ({0,N-1} : Finset ℕ).card ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le 0 ({N-1} : Finset ℕ)
    exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans (by omega))
  have hsubset : S ⊆ (moderateGapStarts T c 2).image (fun i => i+1) := by
    intro i hi
    obtain ⟨hi, hi0, hiN⟩ := Finset.mem_filter.mp hi
    have hl := isolated_gap hi (j := i-1) (show i-1 < N by omega) (by omega)
    have hr := isolated_gap hi (j := i+1) (show i+1 < N by omega) (by omega)
    rw [abs_of_nonpos (sub_nonpos.mpr (finiteOrdinate_mono (by omega) (show i < N by omega)))] at hl
    rw [abs_of_nonneg (sub_nonneg.mpr (finiteOrdinate_mono (by omega) (show i+1 < N by omega)))] at hr
    apply Finset.mem_image.mpr
    refine ⟨i-1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩, by omega⟩
    intro j hj
    interval_cases j
    · simpa only [Nat.add_zero, show i-1+1 = i by omega, neg_sub] using hl
    · simpa only [show i-1+1 = i by omega] using hr
  have hs := (Finset.card_le_card hsubset).trans Finset.card_image_le
  exact htrim.trans (Nat.add_le_add_right hs 2)

/-- Finite inclusion-exclusion for concatenation of two runs, with the
exact denominator N and no boundary subtraction. -/
theorem moderateGapStarts_append (T c : ℝ) (k l : ℕ) :
    (moderateGapStarts T c k).card + (moderateGapStarts T c l).card ≤
      Ncount 0 T + (moderateGapStarts T c (k+l)).card := by
  classical
  let A := moderateGapStarts T c k
  let B := moderateGapStarts T c l
  let P := A.image (fun i => i+k)
  have hP : P.card = A.card := Finset.card_image_of_injective _ (by
    intro i j hh
    change i+k = j+k at hh
    omega)
  have hU : (P ∪ B).card ≤ Ncount 0 T := by
    rw [← Finset.card_range (Ncount 0 T)]
    apply Finset.card_le_card
    intro j hj
    rcases Finset.mem_union.mp hj with hp | hb
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2.1
    · exact (Finset.mem_filter.mp hb).1
  have hsub : P ∩ B ⊆ (moderateGapStarts T c (k+l)).image (fun i => i+k) := by
    intro j hj
    obtain ⟨hp, hb⟩ := Finset.mem_inter.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hi0, hik, hv⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, hjl, hw⟩ := Finset.mem_filter.mp hb
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨hi0, by omega, ?_⟩, rfl⟩
    intro a ha
    by_cases h : a < k
    · exact hv a h
    · have hh := hw (a-k) (by omega)
      simpa only [show i+k+(a-k) = i+a by omega] using hh
  have hR := (Finset.card_le_card hsub).trans Finset.card_image_le
  have huv := Finset.card_union_add_card_inter P B
  change A.card + B.card ≤ _
  omega

/-- Finite Bonferroni inequality for arbitrary even run lengths. -/
theorem finite_moderate_gap_blocks (T c : ℝ) (m : ℕ) :
    (m+1) * (isolatedIndices T c).card ≤
      (moderateGapStarts T c (2*(m+1))).card + m*(Ncount 0 T) + 2*(m+1) := by
  have h2 := finite_two_moderate_gaps T c
  induction m with
  | zero => simpa using h2
  | succ m ih =>
    have hh := moderateGapStarts_append T c (2*(m+1)) 2
    rw [show 2*(m+1)+2 = 2*(m+1+1) by omega] at hh
    simp only [Nat.add_mul, one_mul] at ih ⊢
    omega

private theorem moderateGapStarts_mono {T c : ℝ} {j k : ℕ} (hjk : j ≤ k) :
    moderateGapStarts T c k ⊆ moderateGapStarts T c j := by
  classical
  intro i hi
  obtain ⟨hi, h, hh⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi, by omega, fun a ha => hh a (ha.trans_le hjk)⟩

private theorem eventually_count_exceeds (b : ℝ) :
    ∀ᶠ T : ℝ in atTop, b ≤ (Ncount 0 T : ℝ) := by
  have hp : 0 < 16 * Real.pi := by positivity
  filter_upwards [eventually_count_ge_log, eventually_ge_atTop (b * (16 * Real.pi)),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (0 : ℝ)]
    with T hN hT hL hT0
  have hb := (le_div_iff₀ hp).mpr hT
  have hmul := mul_le_mul_of_nonneg_left hL (div_nonneg hT0 hp.le)
  calc
    b ≤ T / (16 * Real.pi) := hb
    _ ≤ T / (16 * Real.pi) * Real.log T := by simpa only [mul_one] using hmul
    _ = _ := by ring
    _ ≤ _ := hN

/-- A two-neighbor proportion q implies a lower proportion (m+1)q−m
for every run of at most 2(m+1) consecutive moderate gaps. -/
theorem moderateGapLower_of_isolation_blocks {c q : ℝ} (hq : KimIsolationLower c q)
    (m : ℕ) {k : ℕ} (hk : k ≤ 2 * (m + 1)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ((m : ℝ)+1)*q - m - ε ≤ moderateGapProportion T c k := by
  let M := (m : ℝ)+1
  have hM : 0 < M := by dsimp [M]; positivity
  let δ := ε/(2*M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : M*δ = ε/2 := by dsimp [δ]; field_simp
  filter_upwards [hq δ hδ, eventually_count_exceeds (4*M/ε), eventually_count_pos]
    with T hqT hNT hNp
  have hp : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hNp
  rw [← isolatedIndices_card] at hqT
  have hh := mul_le_mul_of_nonneg_left ((le_div_iff₀ hp).mp hqT) hM.le
  have hf := finite_moderate_gap_blocks T c m
  have hm := Finset.card_le_card (moderateGapStarts_mono (T := T) (c := c) hk)
  have hnat : (m+1)*(isolatedIndices T c).card ≤ (moderateGapStarts T c k).card +
      m*Ncount 0 T + 2*(m+1) := by omega
  have hfin : ((m : ℝ)+1)*((isolatedIndices T c).card : ℝ) ≤
      ((moderateGapStarts T c k).card : ℝ) + (m : ℝ)*(Ncount 0 T : ℝ) + 2*((m : ℝ)+1) := by
    exact_mod_cast hnat
  change M * ((isolatedIndices T c).card : ℝ) ≤
      ((moderateGapStarts T c k).card : ℝ) + (m : ℝ)*(Ncount 0 T : ℝ) + 2*M at hfin
  have hN := (div_le_iff₀ hε).mp hNT
  change M*q - (m : ℝ) - ε ≤ _
  apply (le_div_iff₀ hp).mpr
  nlinarith only [hh, hfin, hN, congrArg (· * (Ncount 0 T : ℝ)) hδε]

/-- The three- and four-gap specialization. -/
theorem moderateGapLower_of_isolation {c q : ℝ} (hq : KimIsolationLower c q)
    {k : ℕ} (hk : k ≤ 4) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, 2*q-1-ε ≤ moderateGapProportion T c k := by
  simpa only [Nat.cast_one, one_add_one_eq_two] using
    moderateGapLower_of_isolation_blocks hq 1 hk ε hε

/-- At quarter mean spacing, both three and four consecutive moderate gaps
have lower density at least 0.20739876 relative to all zero copies. -/
theorem three_four_consecutive_quarter (hC : ConreyStopLossHypothesis)
    (hW : tenPointIsolationWindow.energyInput) (hI : FixedGapIsolationCase.quarter.certificate)
    {c : ℝ} (hc : 0 < c) (hcut : c ≤ 1 / 4) {k : ℕ} (hk : k = 3 ∨ k = 4)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, (20739876 / 10^8 : ℝ)-ε ≤ moderateGapProportion T c k := by
  have hh := kimIsolationLower_of_fixedGapCase .quarter hC hW hI hc
    (hcut.trans (by norm_num [FixedGapIsolationCase.row]))
  have h := moderateGapLower_of_isolation hh (k := k) (by omega) ε hε
  simpa only [FixedGapIsolationCase.row, show (2 * (60369938 / 10 ^ 8 : ℝ) - 1) =
    20739876 / 10 ^ 8 by norm_num] using h

/-- At the microscopic cutoff the lower density for six consecutive
strict gaps is 0.020912143; the same bound applies to five. -/
theorem five_six_consecutive_microscopic (hC : ConreyStopLossHypothesis)
    (hW : tenPointIsolationWindow.energyInput)
    (hI : FixedGapIsolationCase.tenMicroscopic.certificate)
    {c : ℝ} (hc : 0 < c) (hcut : c ≤ 1 / 100000) {k : ℕ} (hk : k = 5 ∨ k = 6)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, (20912143 / 10^9 : ℝ)-ε ≤ moderateGapProportion T c k := by
  have hh := kimIsolationLower_of_fixedGapCase .tenMicroscopic hC hW hI hc hcut
  have h := moderateGapLower_of_isolation_blocks hh 2 (k := k) (by omega) ε hε
  simpa only [FixedGapIsolationCase.row, Nat.cast_ofNat,
    show ((2:ℝ)+1) * (673637381 / 10^9) - 2 = 20912143 / 10^9 by norm_num] using h

end RiemannResearch.Analysis.ActualZeroOrdinate
