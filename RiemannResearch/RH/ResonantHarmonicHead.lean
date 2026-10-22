/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ResonantDigitOverlap

/-!
# Exact harmonic head of the binary/ternary resonance

Source: the independently derived covariance calculation in
`RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md` and its Lean continuation.
The interval endpoints and finite reindexing give the exact harmonic head for
all four nonempty binary/ternary overlaps. The complete signed infinite tail
remains explicitly present in the final covariance identity.
-/

namespace RiemannResearch.RH.Pareto.AdjacentDigit
open scoped BigOperators
noncomputable section

/-- The exact endpoints of every aligned binary/ternary overlap. -/
theorem two_three_overlap_endpoints (k r s t : ℕ) :
    max ((3*k+r)*(2*t)) ((2*k+s)*(3*t)) =
      (6*k+max (2*r) (3*s))*t ∧
    min ((3*k+r+1)*(2*t)) ((2*k+s+1)*(3*t)) =
      (6*k+min (2*(r+1)) (3*(s+1)))*t := by
  constructor
  · by_cases h : 2*r ≤ 3*s
    · rw [max_eq_right h, max_eq_right (by nlinarith [Nat.mul_le_mul_right t h])]
      ring
    · have h' : 3*s ≤ 2*r := by omega
      rw [max_eq_left h', max_eq_left (by nlinarith [Nat.mul_le_mul_right t h'])]
      ring
  · by_cases h : 2*(r+1) ≤ 3*(s+1)
    · rw [min_eq_left h, min_eq_left (by nlinarith [Nat.mul_le_mul_right t h])]
      ring
    · have h' : 3*(s+1) ≤ 2*(r+1) := by omega
      rw [min_eq_right h', min_eq_right (by nlinarith [Nat.mul_le_mul_right t h'])]
      ring

/-- Exact aligned mass after the cutoff has passed the complete interval. -/
theorem two_three_aligned_overlapMass (k r s t K : ℕ) (ht : 0 < t)
    (hpos : max (2*r) (3*s) < min (2*(r+1)) (3*(s+1)))
    (hK : (6*k+min (2*(r+1)) (3*(s+1)))*t ≤ K) :
    overlapMass (3*k+r) (2*k+s) K (2*t) (3*t) =
      1 / (((6*k+max (2*r) (3*s))*t : ℕ):ℝ) -
      1 / (((6*k+min (2*(r+1)) (3*(s+1)))*t : ℕ):ℝ) := by
  obtain ⟨hlo,hhi⟩ := two_three_overlap_endpoints k r s t
  unfold overlapMass
  rw [hlo, ← min_assoc, hhi, min_eq_left hK]
  exact if_pos (Nat.mul_lt_mul_of_pos_right (by omega) ht)

/-- The exact reciprocal overlap sum is one harmonic coefficient. -/
theorem reciprocal_interval_harmonic_sum (a b T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T,
      (2:ℝ) * (1/((a*t:ℕ):ℝ) - 1/((b*t:ℕ):ℝ))) =
      (2/(a:ℝ)-2/(b:ℝ)) * (harmonic T:ℝ) := by
  have hh : (∑ t ∈ Finset.Icc 1 T, (1:ℝ)/(t:ℝ)) = (harmonic T:ℝ) := by
    rw [show Finset.Icc 1 T = Finset.Ico 1 (T+1) by ext t; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_right, Nat.add_comm 1]
    simp [harmonic, one_div]
  rw [← hh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  push_cast
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring


/-- The finite overlap sum collapses to its exact harmonic main term. -/
theorem two_three_finite_head (k r s T : ℕ) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 1) (hT : 12*T ≤ k)
    (hpos : max (2*r) (3*s) < min (2*(r+1)) (3*(s+1))) :
    (∑ j ∈ Finset.Icc 1 (3*k+r), ∑ i ∈ Finset.Icc 1 (2*k+s),
      (jump 2 j * jump 3 i) *
        overlapMass (3*k+r) (2*k+s)
          ((6*k+min (2*(r+1)) (3*(s+1)))*T) j i) =
      (2/((6*k+max (2*r) (3*s):ℕ):ℝ) -
        2/((6*k+min (2*(r+1)) (3*(s+1)):ℕ):ℝ)) * (harmonic T:ℝ) := by
  classical
  let U := min (2*(r+1)) (3*(s+1))
  let N := (6*k+U)*T
  let J := Finset.Icc 1 (3*k+r)
  let I := Finset.Icc 1 (2*k+s)
  let S := (Finset.Icc 1 T).image (fun t : ℕ => (2*t,3*t))
  let F : ℕ × ℕ → ℝ := fun z =>
    (jump 2 z.1 * jump 3 z.2) * overlapMass (3*k+r) (2*k+s) N z.1 z.2
  have hU : U ≤ 6 := (min_le_left _ _).trans (by omega)
  have hUT := Nat.mul_le_mul_right T hU
  have hTk := Nat.mul_le_mul_left k hT
  have hN : N ≤ k*k := by dsimp [N]; nlinarith
  have hS : S ⊆ J ×ˢ I := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
    have ht' := Finset.mem_Icc.mp ht
    simp only [Finset.mem_product, J, I, Finset.mem_Icc]
    omega
  have hz : ∀ z ∈ J ×ˢ I, z ∉ S → F z = 0 := by
    intro z hz hzS
    obtain ⟨hj,hi⟩ := Finset.mem_product.mp hz
    have hj' := Finset.mem_Icc.mp hj
    have hi' := Finset.mem_Icc.mp hi
    dsimp [F, overlapMass]
    split_ifs with hLU
    · exfalso
      let n := max ((3*k+r)*z.1) ((2*k+s)*z.2)
      have hnN : n < N := lt_of_lt_of_le hLU
        ((min_le_right _ _).trans (min_le_right _ _))
      have hnj : n ∈ Finset.Ico ((3*k+r)*z.1) ((3*k+r+1)*z.1) :=
        Finset.mem_Ico.mpr ⟨le_max_left _ _, lt_of_lt_of_le hLU (min_le_left _ _)⟩
      have hni : n ∈ Finset.Ico ((2*k+s)*z.2) ((2*k+s+1)*z.2) :=
        Finset.mem_Ico.mpr ⟨le_max_right _ _, lt_of_lt_of_le hLU
          ((min_le_right _ _).trans (min_le_left _ _))⟩
      obtain ⟨t,hjt,hit⟩ := two_three_alignment_below_square k r s z.1 z.2 n
        hk hr hs (lt_of_lt_of_le hnN hN) hnj hni
      have htpos : 1 ≤ t := by omega
      have hstart : 6*k*t ≤ n := by
        have hh := (Finset.mem_Ico.mp hnj).1
        rw [hjt] at hh
        nlinarith
      have htT : t ≤ T := by
        by_contra h
        have hmul := Nat.mul_le_mul_left (6*k) (show T+1 ≤ t by omega)
        dsimp [N] at hnN
        nlinarith
      apply hzS
      apply Finset.mem_image.mpr
      refine ⟨t, Finset.mem_Icc.mpr ⟨htpos,htT⟩, ?_⟩
      exact Prod.ext hjt.symm hit.symm
    · simp
  change (∑ j ∈ J, ∑ i ∈ I, F (j,i)) = _
  calc
    _ = ∑ z ∈ J ×ˢ I, F z := by simp only [Finset.sum_product]
    _ = ∑ z ∈ S, F z := (Finset.sum_subset hS hz).symm
    _ = ∑ t ∈ Finset.Icc 1 T, F (2*t,3*t) := by
      dsimp [S]
      apply Finset.sum_image
      intro a ha b hb hab
      have h := congrArg Prod.fst hab
      change 2*a = 2*b at h
      omega
    _ = ∑ t ∈ Finset.Icc 1 T,
        (2:ℝ) * (1/(((6*k+max (2*r) (3*s))*t:ℕ):ℝ) -
          1/(((6*k+U)*t:ℕ):ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      dsimp [F]
      rw [two_three_resonant_jump t ht'.1,
        two_three_aligned_overlapMass k r s t N ht'.1 hpos
          (Nat.mul_le_mul_left (6*k+U) ht'.2)]
    _ = _ := reciprocal_interval_harmonic_sum _ _ T

/-- Exact resonant covariance, with the original entire signed tail still present. -/
theorem two_three_exact_harmonic_tail (k r s T : ℕ) (hk : 0 < k)
    (hr : r ≤ 2) (hs : s ≤ 1) (hT : 12*T ≤ k)
    (hpos : max (2*r) (3*s) < min (2*(r+1)) (3*(s+1))) :
    crossCovariance 2 3 (3*k+r) (2*k+s) =
      (2/((6*k+max (2*r) (3*s):ℕ):ℝ) -
        2/((6*k+min (2*(r+1)) (3*(s+1)):ℕ):ℝ)) * (harmonic T:ℝ) +
      ∑' n, crossTail 2 3 (3*k+r) (2*k+s)
        ((6*k+min (2*(r+1)) (3*(s+1)))*T) n := by
  have hU : min (2*(r+1)) (3*(s+1)) ≤ 6 := (min_le_left _ _).trans (by omega)
  have hUT := Nat.mul_le_mul_right T hU
  have hTk := Nat.mul_le_mul_left k hT
  have hN : (6*k+min (2*(r+1)) (3*(s+1)))*T ≤ k*k := by nlinarith
  rw [cross_exact_head_tail 2 3 (3*k+r) (2*k+s)
    ((6*k+min (2*(r+1)) (3*(s+1)))*T) (by omega) (by omega)
    (by omega) (by omega) (by nlinarith) (by nlinarith),
    two_three_finite_head k r s T hk hr hs hT hpos]

end
end RiemannResearch.RH.Pareto.AdjacentDigit
