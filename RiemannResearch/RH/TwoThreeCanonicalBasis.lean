/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.TwoThreeCanonicalBudget
import RiemannResearch.RH.FiniteResidueIndependence
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# Independence of the ordinary canonical two-seed family

Source: the elementary maximal-pivot argument in Christian Noack's
15 September 2026 resonance-cell continuation. Ternary pivots are eliminated
first; the retained binary pivots have no factor of three.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
noncomputable section

private theorem collect_residue_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (S : Finset ℕ) (u : ι → ℕ) (c : ι → ℝ)
    (hu : ∀ i ∈ s, 0 < u i)
    (hS : ∀ n ∈ S, 2 ≤ n)
    (humem : ∀ i ∈ s, 2 ≤ u i → u i ∈ S) (k : ℕ) :
    (∑ n ∈ S, (∑ i ∈ s, if u i = n then c i else 0) * residue n k) =
      ∑ i ∈ s, c i * residue (u i) k := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hui : 2 ≤ u i
  · calc
      _ = (if u i = u i then c i else 0) * residue (u i) k := by
        apply Finset.sum_eq_single (u i)
        · intro n hn hni
          have h : u i ≠ n := Ne.symm hni
          simp [h]
        · intro hnot
          exact False.elim (hnot (humem i hi hui))
      _ = c i * residue (u i) k := by simp
  · have hui1 : u i = 1 := by have := hu i hi; omega
    have hzero : ∀ n ∈ S, u i ≠ n := by
      intro n hn
      have := hS n hn
      omega
    simp only [hui1, residue, Nat.mod_one, Nat.cast_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro n hn
    have hne : 1 ≠ n := by have := hS n hn; omega
    simp [hne]

/-- Extract an arbitrary residue coefficient from a finite relation of residue
    differences. Repeated moduli are collected, and the zero sequence at modulus
    one is handled explicitly. -/
theorem finite_residue_difference_coefficient_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u v : ι → ℕ) (c : ι → ℝ)
    (hu : ∀ i ∈ s, 0 < u i) (hv : ∀ i ∈ s, 0 < v i)
    (hz : ∀ k, ∑ i ∈ s, c i * (residue (u i) k - residue (v i) k) = 0)
    (r : ℕ) (hr : 2 ≤ r) :
    (∑ i ∈ s, if u i = r then c i else 0) -
      (∑ i ∈ s, if v i = r then c i else 0) = 0 := by
  classical
  let S := (insert r (s.image u ∪ s.image v)).filter (fun n => 2 ≤ n)
  let C : ℕ → ℝ := fun n =>
    (∑ i ∈ s, if u i = n then c i else 0) -
      (∑ i ∈ s, if v i = n then c i else 0)
  have hS : ∀ n ∈ S, 2 ≤ n := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have humem : ∀ i ∈ s, 2 ≤ u i → u i ∈ S := by
    intro i hi hui
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)), hui⟩
  have hvmem : ∀ i ∈ s, 2 ≤ v i → v i ∈ S := by
    intro i hi hvi
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)), hvi⟩
  have hzero : ∀ k : ℕ, ∑ n ∈ S, C n * residue n k = 0 := by
    intro k
    simp only [C, sub_mul, Finset.sum_sub_distrib]
    rw [collect_residue_sum s S u c hu hS humem k,
      collect_residue_sum s S v c hv hS hvmem k]
    rw [← Finset.sum_sub_distrib]
    simpa only [mul_sub] using hz k
  exact finite_residue_coefficients_zero S C hS hzero r
    (Finset.mem_filter.mpr ⟨Finset.mem_insert_self r _, hr⟩)

/-- Finite coefficients of the canonical generators vanish whenever their
    resulting arithmetic sequence vanishes. -/
theorem canonical_generator_coefficients_zero
    (s : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℝ)
    (hs : ∀ i ∈ s, 0 < i.2 ∧
      (i.1 = 3 ∨ (i.1 = 2 ∧ ¬ 3 ∣ i.2)))
    (hz : ∀ k : ℕ, ∑ i ∈ s, c i * dilation i.2 (residue i.1) k = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  have hmod (r : ℕ) (hr : 2 ≤ r) :
      (∑ i ∈ s, if i.1*i.2 = r then c i else 0) -
        (∑ i ∈ s, if i.2 = r then c i else 0) = 0 := by
    apply finite_residue_difference_coefficient_zero s
      (fun i => i.1*i.2) Prod.snd c ?_ ?_ ?_ r hr
    · intro i hi
      obtain ⟨hip, hi3 | ⟨hi2, hni⟩⟩ := hs i hi
      · rw [hi3]; omega
      · rw [hi2]; omega
    · intro i hi
      exact (hs i hi).1
    · intro k
      convert hz k using 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [residue_mul_floor, Nat.mul_comm]
  have hternary : ∀ i ∈ s, i.1 = 3 → c i = 0 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨i, his, hi3, hci⟩ := hnot
    let t := s.filter (fun i => i.1 = 3 ∧ c i ≠ 0)
    have hit : i ∈ t := Finset.mem_filter.mpr ⟨his, hi3, hci⟩
    have ht : (t.image Prod.snd).Nonempty := ⟨i.2, Finset.mem_image.mpr ⟨i, hit, rfl⟩⟩
    let m := (t.image Prod.snd).max' ht
    obtain ⟨j, hjt, hjm⟩ := Finset.mem_image.mp (Finset.max'_mem _ ht)
    change j.2 = m at hjm
    have hjs : j ∈ s := (Finset.mem_filter.mp hjt).1
    have hj3 : j.1 = 3 := (Finset.mem_filter.mp hjt).2.1
    have hcj : c j ≠ 0 := (Finset.mem_filter.mp hjt).2.2
    have hm : 0 < m := by simpa only [hjm] using (hs j hjs).1
    have hleast (i : ℕ × ℕ) (hi : i ∈ s) (hi3 : i.1 = 3)
        (hci : c i ≠ 0) : i.2 ≤ m :=
      Finset.le_max' (t.image Prod.snd) i.2
        (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hi3, hci⟩, rfl⟩)
    have hpositive : (∑ i ∈ s, if i.1*i.2 = 3*m then c i else 0) = c j := by
      calc
        _ = (if j.1*j.2 = 3*m then c j else 0) := by
          apply Finset.sum_eq_single j
          · intro i hi hij
            by_cases hci : c i = 0
            · simp [hci]
            · have hne : i.1*i.2 ≠ 3*m := by
                intro heq
                rcases (hs i hi).2 with hi3 | ⟨hi2, hiN⟩
                · rw [hi3] at heq
                  have him : i.2 = m := by omega
                  apply hij
                  exact Prod.ext (by omega) (by omega)
                · rw [hi2] at heq
                  have hidiv : 3 ∣ i.2 := by
                    apply Nat.dvd_of_mod_eq_zero
                    omega
                  exact hiN hidiv
              simp [hne]
          · exact fun hj => False.elim (hj hjs)
        _ = c j := by simp [hj3, hjm]
    have hnegative : (∑ i ∈ s, if i.2 = 3*m then c i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hci : c i = 0
      · simp [hci]
      · have hne : i.2 ≠ 3*m := by
          intro him
          rcases (hs i hi).2 with hi3 | ⟨hi2, hiN⟩
          · have := hleast i hi hi3 hci
            omega
          · exact hiN ⟨m, him⟩
        simp [hne]
    have := hmod (3*m) (by omega)
    rw [hpositive, hnegative, sub_zero] at this
    exact hcj this
  intro i his
  by_contra hci
  let t := s.filter (fun j => c j ≠ 0)
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨his, hci⟩
  have ht : (t.image Prod.snd).Nonempty := ⟨i.2, Finset.mem_image.mpr ⟨i, hit, rfl⟩⟩
  let m := (t.image Prod.snd).max' ht
  obtain ⟨j, hjt, hjm⟩ := Finset.mem_image.mp (Finset.max'_mem _ ht)
  change j.2 = m at hjm
  have hjs : j ∈ s := (Finset.mem_filter.mp hjt).1
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hjt).2
  have hj2 : j.1 = 2 := by
    rcases (hs j hjs).2 with hj3 | ⟨hj2, hjN⟩
    · exact False.elim (hcj (hternary j hjs hj3))
    · exact hj2
  have hm : 0 < m := by simpa only [hjm] using (hs j hjs).1
  have hleast (i : ℕ × ℕ) (hi : i ∈ s) (hci : c i ≠ 0) : i.2 ≤ m :=
    Finset.le_max' (t.image Prod.snd) i.2
      (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩, rfl⟩)
  have hpositive : (∑ i ∈ s, if i.1*i.2 = 2*m then c i else 0) = c j := by
    calc
      _ = (if j.1*j.2 = 2*m then c j else 0) := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          by_cases hci : c i = 0
          · simp [hci]
          · have hi2 : i.1 = 2 := by
              rcases (hs i hi).2 with hi3 | ⟨hi2, hiN⟩
              · exact False.elim (hci (hternary i hi hi3))
              · exact hi2
            have hne : i.1*i.2 ≠ 2*m := by
              intro heq
              rw [hi2] at heq
              have him : i.2 = m := by omega
              apply hij
              exact Prod.ext (by omega) (by omega)
            simp [hne]
        · exact fun hj => False.elim (hj hjs)
      _ = c j := by simp [hj2, hjm]
  have hnegative : (∑ i ∈ s, if i.2 = 2*m then c i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hci : c i = 0
    · simp [hci]
    · have hne : i.2 ≠ 2*m := by
        have := hleast i hi hci
        omega
      simp [hne]
  have := hmod (2*m) (by omega)
  rw [hpositive, hnegative, sub_zero] at this
  exact hcj this


/-- A finite index set without redundant binary generators. -/
def canonicalIndices (M : ℕ) : Finset (ℕ × ℕ) :=
  ({3} ×ˢ Finset.Icc 1 M) ∪
    ({2} ×ˢ (Finset.Icc 1 M).filter (fun n => ¬ 3 ∣ n))

theorem mem_canonicalIndices (M : ℕ) (i : ℕ × ℕ) :
    i ∈ canonicalIndices M ↔ 0 < i.2 ∧ i.2 ≤ M ∧
      (i.1 = 3 ∨ (i.1 = 2 ∧ ¬ 3 ∣ i.2)) := by
  simp only [canonicalIndices, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro (⟨hi3, hlow, hupp⟩ | ⟨hi2, ⟨hlow, hupp⟩, hn⟩)
    · exact ⟨by omega, hupp, Or.inl hi3⟩
    · exact ⟨by omega, hupp, Or.inr ⟨hi2, hn⟩⟩
  · rintro ⟨hpos, hupp, hi3 | ⟨hi2, hn⟩⟩
    · exact Or.inl ⟨hi3, by omega, hupp⟩
    · exact Or.inr ⟨hi2, ⟨by omega, hupp⟩, hn⟩

/-- The retained finite arithmetic family. -/
def canonicalFamily (M : ℕ) (i : canonicalIndices M) : ℕ → ℝ :=
  dilation i.val.2 (residue i.val.1)

/-- The canonical finite family is actually independent in the sequence space. -/
theorem canonicalFamily_linearIndependent (M : ℕ) :
    LinearIndependent ℝ (canonicalFamily M) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hz i hi
  let C : (ℕ × ℕ) → ℝ := fun j =>
    if hj : j ∈ canonicalIndices M then c ⟨j, hj⟩ else 0
  have hc (j : canonicalIndices M) : C j.val = c j := by simp [C]
  have ht : ∀ j ∈ s.image Subtype.val, 0 < j.2 ∧
      (j.1 = 3 ∨ (j.1 = 2 ∧ ¬ 3 ∣ j.2)) := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    have h := (mem_canonicalIndices M a.val).mp a.property
    exact ⟨h.1, h.2.2⟩
  have hzero : ∀ k : ℕ,
      ∑ j ∈ s.image Subtype.val, C j * dilation j.2 (residue j.1) k = 0 := by
    intro k
    rw [Finset.sum_image]
    · have heval := congrArg (fun f : ℕ → ℝ => f k) hz
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, canonicalFamily, hc] using heval
    · intro a ha b hb hab
      exact Subtype.ext hab
  have hcz := canonical_generator_coefficients_zero
    (s.image Subtype.val) C ht hzero i.val (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  simpa only [hc] using hcz

/-- The range of the independent family is exactly the already established
    canonical generating set. -/
theorem canonicalFamily_span (M : ℕ) :
    Submodule.span ℝ (Set.range (canonicalFamily M)) = canonicalSpan M := by
  apply congrArg (Submodule.span ℝ)
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨hpos, hupp, hi3 | ⟨hi2, hn⟩⟩ :=
      (mem_canonicalIndices M i.val).mp i.property
    · exact ⟨i.val.2, hpos, hupp, Or.inl (by simp [canonicalFamily, hi3])⟩
    · exact ⟨i.val.2, hpos, hupp, Or.inr ⟨hn, by simp [canonicalFamily, hi2]⟩⟩
  · rintro ⟨n, hpos, hupp, hf | ⟨hn, hf⟩⟩
    · refine ⟨⟨(3,n), (mem_canonicalIndices M (3,n)).mpr
        ⟨hpos, hupp, Or.inl rfl⟩⟩, ?_⟩
      exact hf.symm
    · refine ⟨⟨(2,n), (mem_canonicalIndices M (2,n)).mpr
        ⟨hpos, hupp, Or.inr ⟨rfl, hn⟩⟩⟩, ?_⟩
      exact hf.symm

private theorem card_multiples_three (M : ℕ) :
    ((Finset.Icc 1 M).filter (fun n => 3 ∣ n)).card = M / 3 := by
  have heq : (Finset.Icc 1 M).filter (fun n => 3 ∣ n) =
      (Finset.Icc 1 (M/3)).image (fun n => 3*n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnIcc, hn3⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnlow, hnupp⟩ := Finset.mem_Icc.mp hnIcc
      obtain ⟨k, rfl⟩ := hn3
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · intro hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hklow, hkupp⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  rw [heq, Finset.card_image_of_injective]
  · simp [Nat.card_Icc]
  · intro a b hab
    dsimp at hab
    omega

private theorem card_nonmultiples_three (M : ℕ) :
    ((Finset.Icc 1 M).filter (fun n => ¬ 3 ∣ n)).card = M - M/3 := by
  let S := Finset.Icc 1 M
  have hd : Disjoint (S.filter (fun n => 3 ∣ n)) (S.filter (fun n => ¬ 3 ∣ n)) := by
    apply Finset.disjoint_left.mpr
    intro n hyes hno
    exact (Finset.mem_filter.mp hno).2 ((Finset.mem_filter.mp hyes).2)
  have hu : S.filter (fun n => 3 ∣ n) ∪ S.filter (fun n => ¬ 3 ∣ n) = S := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  have hyes : (S.filter (fun n => 3 ∣ n)).card = M/3 := card_multiples_three M
  have hS : S.card = M := by simp [S, Nat.card_Icc]
  rw [hyes, hS] at hc
  change (S.filter (fun n => ¬ 3 ∣ n)).card = _
  omega

/-- The exact number of retained generators at every ordinary budget. -/
theorem card_canonicalIndices (M : ℕ) :
    (canonicalIndices M).card = 2*M-M/3 := by
  have hd : Disjoint ({3} ×ˢ Finset.Icc 1 M)
      ({2} ×ˢ (Finset.Icc 1 M).filter (fun n => ¬ 3 ∣ n)) := by
    apply Finset.disjoint_left.mpr
    intro i hi3 hi2
    have h3 : i.1 = 3 := Finset.mem_singleton.mp (Finset.mem_product.mp hi3).1
    have h2 : i.1 = 2 := Finset.mem_singleton.mp (Finset.mem_product.mp hi2).1
    omega
  simp only [canonicalIndices, Finset.card_union_of_disjoint hd,
    Finset.card_product, Finset.card_singleton, one_mul]
  rw [card_nonmultiples_three]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]
  omega

/-- Exact dimension of the original two-seed budget, proved using the actual
    arithmetic generators and the independent canonical subfamily. -/
theorem finrank_budgetSpan (M : ℕ) :
    Module.finrank ℝ (budgetSpan M) = 2*M-M/3 := by
  rw [← canonicalSpan_eq_budgetSpan M, ← canonicalFamily_span M,
    finrank_span_eq_card (canonicalFamily_linearIndependent M),
    Fintype.card_coe, card_canonicalIndices]

end
end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
