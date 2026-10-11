/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Fin

/-!
# Chronological finite cutoffs of the actual zeta ordinates

We sort all copies of actual nontrivial zeros of `riemannZeta` with
`0 < im ≤ T`. Multiplicity and equal ordinates at different real parts are
retained. In particular, no simplicity or Riemann-hypothesis assumption enters
the construction.

The natural-index sequence is padded by the cutoff height `T`. Its last gap is
therefore the interval from the final zero to `T`, not a gap to the next zero.
The exact pair-sum formula below isolates this boundary term.

Source: user-provided consecutive-ordinate argument, 2026-10-11. This module
formalizes the actual-zero enumeration needed to apply finite gap identities;
it does not formalize Fujii's moment estimates or Hlawka's theorem.
-/

noncomputable section
open scoped BigOperators
open Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Chronologically sorted actual zero ordinates, with every copy retained. -/
def chronologicalList (T : ℝ) : List ℝ :=
  ((Finset.univ : Finset (Copies T)).toList.map (copyOrdinate T)).mergeSort (· ≤ ·)

theorem chronologicalList_perm (T : ℝ) :
    (chronologicalList T).Perm
      ((Finset.univ : Finset (Copies T)).toList.map (copyOrdinate T)) :=
  List.mergeSort_perm _ _

@[simp] theorem chronologicalList_length (T : ℝ) :
    (chronologicalList T).length = Ncount 0 T := by
  classical
  simp only [chronologicalList, List.length_mergeSort, List.length_map,
    Finset.length_toList, Finset.card_univ, card_copies]

theorem chronologicalList_sorted (T : ℝ) : (chronologicalList T).SortedLE :=
  List.sortedLE_mergeSort

theorem mem_chronologicalList {T x : ℝ} :
    x ∈ chronologicalList T ↔ ∃ c : Copies T, copyOrdinate T c = x := by
  classical
  rw [(chronologicalList_perm T).mem_iff]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]

theorem chronologicalList_bounds {T x : ℝ} (hx : x ∈ chronologicalList T) :
    0 < x ∧ x ≤ T := by
  obtain ⟨c, rfl⟩ := mem_chronologicalList.mp hx
  exact (mem_cutoff.mp c.1.property).2

/-- Sorting preserves every finite moment, without injectivity assumptions. -/
theorem chronologicalList_sum {A : Type*} [AddCommMonoid A]
    (T : ℝ) (f : ℝ → A) :
    ((chronologicalList T).map f).sum = ∑ c : Copies T, f (copyOrdinate T c) := by
  classical
  rw [((chronologicalList_perm T).map f).sum_eq]
  simp only [List.map_map, Finset.sum_map_toList, Function.comp_apply]

/-- Natural-index ordinate sequence within a fixed actual cutoff, padded by `T`. -/
def cutoffOrdinate (T : ℝ) (n : ℕ) : ℝ := (chronologicalList T).getD n T

theorem cutoffOrdinate_eq_get {T : ℝ} {n : ℕ}
    (hn : n < (chronologicalList T).length) :
    cutoffOrdinate T n = (chronologicalList T).get ⟨n, hn⟩ :=
  List.getD_eq_get (chronologicalList T) T ⟨n, hn⟩

theorem cutoffOrdinate_mem {T : ℝ} {n : ℕ} (hn : n < Ncount 0 T) :
    cutoffOrdinate T n ∈ chronologicalList T := by
  rw [cutoffOrdinate_eq_get (by simpa using hn)]
  exact List.get_mem _ _

theorem cutoffOrdinate_bounds {T : ℝ} {n : ℕ} (hn : n < Ncount 0 T) :
    0 < cutoffOrdinate T n ∧ cutoffOrdinate T n ≤ T :=
  chronologicalList_bounds (cutoffOrdinate_mem hn)

theorem cutoffOrdinate_of_count_le {T : ℝ} {n : ℕ} (hn : Ncount 0 T ≤ n) :
    cutoffOrdinate T n = T := by
  exact List.getD_eq_default _ _ (by simpa using hn)

@[simp] theorem cutoffOrdinate_at_count (T : ℝ) :
    cutoffOrdinate T (Ncount 0 T) = T := cutoffOrdinate_of_count_le le_rfl

theorem cutoffOrdinate_le (T : ℝ) (n : ℕ) : cutoffOrdinate T n ≤ T := by
  by_cases hn : n < Ncount 0 T
  · exact (cutoffOrdinate_bounds hn).2
  · rw [cutoffOrdinate_of_count_le (Nat.le_of_not_gt hn)]

theorem cutoffOrdinate_monotone (T : ℝ) : Monotone (cutoffOrdinate T) := by
  intro i j hij
  by_cases hj : j < Ncount 0 T
  · have hi : i < Ncount 0 T := lt_of_le_of_lt hij hj
    rw [cutoffOrdinate_eq_get (by simpa using hi),
      cutoffOrdinate_eq_get (by simpa using hj)]
    exact (chronologicalList_sorted T).monotone_get hij
  · rw [cutoffOrdinate_of_count_le (Nat.le_of_not_gt hj)]
    exact cutoffOrdinate_le T i

/-- Equality of arbitrary finite moments to sums over the actual zero copies. -/
theorem cutoffOrdinate_sum {A : Type*} [AddCommMonoid A]
    (T : ℝ) (f : ℝ → A) :
    ∑ j ∈ Finset.range (Ncount 0 T), f (cutoffOrdinate T j) =
      ∑ c : Copies T, f (copyOrdinate T c) := by
  classical
  rw [← chronologicalList_length T, ← Fin.sum_univ_eq_sum_range]
  calc
    ∑ j : Fin (chronologicalList T).length, f (cutoffOrdinate T j) =
        ∑ j : Fin (chronologicalList T).length, f ((chronologicalList T)[j.1]) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [cutoffOrdinate_eq_get j.isLt]
      rfl
    _ = ((chronologicalList T).map f).sum := Fin.sum_univ_fun_getElem _ _
    _ = _ := chronologicalList_sum T f

/-- The concrete chronological character sum is the actual weighted zeta sum. -/
theorem cutoffOrdinate_phase_sum (T u : ℝ) :
    ∑ j ∈ Finset.range (Ncount 0 T), ZeroOrdinate.phase u (cutoffOrdinate T j) =
      ordinateSum T u := by
  rw [cutoffOrdinate_sum, ordinateSum, sum_eq_copies]
  rfl

/-- The final gap is to the cutoff endpoint; interior gaps are actual consecutive
ordinate gaps, with zero gaps retained. -/
def cutoffGap (T : ℝ) (n : ℕ) : ℝ := cutoffOrdinate T (n + 1) - cutoffOrdinate T n

theorem cutoffGap_nonneg (T : ℝ) (n : ℕ) : 0 ≤ cutoffGap T n :=
  sub_nonneg.mpr (cutoffOrdinate_monotone T (Nat.le_succ n))

/-- Exact telescoping including the endpoint from the last zero to `T`. -/
theorem sum_cutoffGap (T : ℝ) :
    ∑ j ∈ Finset.range (Ncount 0 T), cutoffGap T j = T - cutoffOrdinate T 0 := by
  simp only [cutoffGap, Finset.sum_range_sub, cutoffOrdinate_at_count]

/-- Exact decomposition into genuine interior consecutive pairs and one explicit
artificial boundary pair. It applies to every test function. -/
theorem cutoff_pair_sum_boundary {A : Type*} [AddCommMonoid A]
    (T : ℝ) (f : ℝ → ℝ → A) (n : ℕ) (hn : Ncount 0 T = n + 1) :
    (∑ j ∈ Finset.range (Ncount 0 T), f (cutoffOrdinate T j) (cutoffOrdinate T (j + 1))) =
      (∑ j ∈ Finset.range n, f (cutoffOrdinate T j) (cutoffOrdinate T (j + 1))) +
        f (cutoffOrdinate T n) T := by
  rw [hn, Finset.sum_range_succ]
  rw [cutoffOrdinate_of_count_le (by omega : Ncount 0 T ≤ n + 1)]

/-- Replacing the artificial endpoint by any proposed next ordinate has exactly
one signed correction. No claim that `B` is the next zero is hidden here. -/
theorem cutoff_pair_sum_replace_endpoint (T B : ℝ) (f : ℝ → ℝ → ℂ)
    (n : ℕ) (hn : Ncount 0 T = n + 1) :
    (∑ j ∈ Finset.range (Ncount 0 T), f (cutoffOrdinate T j) (cutoffOrdinate T (j + 1))) =
      ((∑ j ∈ Finset.range n, f (cutoffOrdinate T j) (cutoffOrdinate T (j + 1))) +
        f (cutoffOrdinate T n) B) +
      (f (cutoffOrdinate T n) T - f (cutoffOrdinate T n) B) := by
  rw [cutoff_pair_sum_boundary T f n hn]
  ring

/-- Character endpoint replacement costs at most two before normalization. -/
theorem phase_endpoint_correction_le (T B a b : ℝ) (n : ℕ) :
    ‖ZeroOrdinate.phase a (cutoffOrdinate T n) * ZeroOrdinate.phase b T -
      ZeroOrdinate.phase a (cutoffOrdinate T n) * ZeroOrdinate.phase b B‖ ≤ 2 := by
  calc
    _ ≤ ‖ZeroOrdinate.phase a (cutoffOrdinate T n) * ZeroOrdinate.phase b T‖ +
        ‖ZeroOrdinate.phase a (cutoffOrdinate T n) * ZeroOrdinate.phase b B‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_mul, ZeroOrdinate.phase_norm]

/-- There are no repeated ordinates exactly when the copy projection is injective. -/
theorem chronologicalList_nodup_iff_injective (T : ℝ) :
    (chronologicalList T).Nodup ↔ Function.Injective (copyOrdinate T) := by
  classical
  rw [(chronologicalList_perm T).nodup_iff,
    List.nodup_map_iff_inj_on (Finset.nodup_toList _)]
  simp only [Finset.mem_toList, Finset.mem_univ, forall_true_left]
  rfl

/-- Strictly ordered actual ordinates are an RH-and-simplicity assertion at that
cutoff. One must not build strict ordering into an unconditional model. -/
theorem chronologicalList_nodup_iff (T : ℝ) :
    (chronologicalList T).Nodup ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  rw [chronologicalList_nodup_iff_injective, copyOrdinate_injective_iff]

theorem chronologicalList_strict_iff (T : ℝ) :
    (chronologicalList T).SortedLT ↔
      ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  rw [List.sortedLT_iff_nodup_and_sortedLE, chronologicalList_nodup_iff]
  exact and_iff_left (chronologicalList_sorted T)

end RiemannResearch.Analysis.ActualZeroOrdinate
