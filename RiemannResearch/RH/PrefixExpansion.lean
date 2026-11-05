/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeSubtreeBudget

/-! # Upward aggregation on the ordered prime-prefix tree

Source: discrete summation by parts on the finite rooted tree obtained by
removing the largest prime. Applying the identity to a point indicator
recovers the exact upward recurrence, including the mass of the vertex itself.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimeSubtreeBudget

/-- A function on vertices is recovered by its differences along the path from 1. -/
theorem prefix_gradient_sum (f : ℕ → ℝ) (m : ℕ) (hm : 0 < m) :
    ∑ r ∈ prefixes m, (f r - f (parent r)) = f m - f 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [prefixes]
    split
    next h =>
      obtain ⟨hp,hlt,_⟩ := parent_spec m h
      have hout : m ∉ prefixes (parent m) := fun hx =>
        (Nat.not_le_of_lt hlt) (prefix_bounds hx).2
      rw [Finset.sum_insert hout, ih _ hlt hp]
      ring
    next h =>
      have he : m = 1 := by omega
      simp [he]

/-- Discrete integration by parts: pair a vertex test with the atomic masses,
or pair its edge differences with the signed subtree masses. -/
theorem subtree_gradient_pairing (b f : ℕ → ℝ) (H : ℕ) :
    ∑ r ∈ Finset.Icc 2 H, (f r - f (parent r)) * subtree b H r =
      ∑ m ∈ Finset.Icc 1 H, (f m - f 1) * (b m / (m : ℝ)) := by
  classical
  unfold subtree
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  rw [← prefix_gradient_sum f m hm'.1, Finset.sum_mul]
  have hsub : prefixes m ⊆ Finset.Icc 2 H := fun r hr =>
    Finset.mem_Icc.mpr ⟨(prefix_bounds hr).1, (prefix_bounds hr).2.trans hm'.2⟩
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨hsub h, h⟩⟩

/-- Reading upward: the local mass and all immediate children add exactly to the subtree. -/
theorem subtree_eq_node_add_children (b : ℕ → ℝ) (H r : ℕ)
    (hr : r ∈ Finset.Icc 2 H) :
    subtree b H r = b r / (r : ℝ) +
      ∑ c ∈ (Finset.Icc 2 H).filter (fun c => parent c = r), subtree b H c := by
  classical
  have hr' := Finset.mem_Icc.mp hr
  have hr1 : r ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨by omega, hr'.2⟩
  let f := fun n : ℕ => if n = r then (1 : ℝ) else 0
  have hf : f 1 = 0 := if_neg (by omega)
  have h := subtree_gradient_pairing b f H
  have ha : (∑ c ∈ Finset.Icc 2 H, f c * subtree b H c) = subtree b H r := by
    simp [f, ite_mul, hr]
  have hp : (∑ c ∈ Finset.Icc 2 H, f (parent c) * subtree b H c) =
      ∑ c ∈ (Finset.Icc 2 H).filter (fun c => parent c = r), subtree b H c := by
    simp only [f, ite_mul, zero_mul, one_mul, Finset.sum_filter]
  have hm : (∑ m ∈ Finset.Icc 1 H, (f m - f 1) * (b m / (m : ℝ))) =
      b r / (r : ℝ) := by
    simp [hf, f, ite_mul, hr1]
  rw [hm] at h
  simp_rw [sub_mul] at h
  rw [Finset.sum_sub_distrib, ha, hp] at h
  linarith

/-- A bottom-up evaluation is uniquely determined by the child recursion at this horizon. -/
theorem subtree_unique_of_children (b t : ℕ → ℝ) (H : ℕ)
    (hrec : ∀ r ∈ Finset.Icc 2 H, t r = b r / (r : ℝ) +
      ∑ c ∈ (Finset.Icc 2 H).filter (fun c => parent c = r), t c) :
    ∀ r ∈ Finset.Icc 2 H, t r = subtree b H r := by
  classical
  have aux : ∀ k r : ℕ, H - r = k → r ∈ Finset.Icc 2 H → t r = subtree b H r := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro r hk hr
      rw [hrec r hr, subtree_eq_node_add_children b H r hr]
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨hcA,hpar⟩ := Finset.mem_filter.mp hc
      obtain ⟨hclo,hchi⟩ := Finset.mem_Icc.mp hcA
      have hlt := (parent_spec c hclo).2.1
      exact ih (H - c) (by omega) c rfl hcA
  exact fun r hr => aux (H - r) r rfl hr

end RiemannResearch.RH.QPrimeSubtreeBudget
