/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ResonantDigitOverlap

/-!
# Exact old/new digit covariance and its periodic harmonic means

Source: the independently derived covariance calculation in
`RH_Resonance_Cell_and_Canonical_Budget_2026-09-15.md` and its Lean continuation.
The aligned old-scale interval contains each new-scale interval. The exact
finite reindexing retains the entire signed tail, and direct period-six
calculations supply the four old/new means required by the resonance cell.
-/

namespace RiemannResearch.RH.Pareto.AdjacentDigit
open scoped BigOperators
noncomputable section

def sampledJump (p q a k : ℕ) : ℝ := jump p (k+1) * jump q (a*(k+1))

def sampledHarmonic (p q a T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, jump p t * jump q (a*t) / (t:ℝ)

/-- An old-scale jump contains the entire aligned new-scale jump interval. -/
theorem old_new_aligned_overlapMass (a k r t K : ℕ) (ht : 0 < t)
    (hr : r < a) (hK : (a*k+r+1)*t ≤ K) :
    overlapMass (a*k+r) k K t (a*t) =
      1 / (((a*k+r)*t:ℕ):ℝ) - 1 / (((a*k+r+1)*t:ℕ):ℝ) := by
  have hlo : max ((a*k+r)*t) (k*(a*t)) = (a*k+r)*t :=
    max_eq_left (by nlinarith)
  have hhi : min ((a*k+r+1)*t) ((k+1)*(a*t)) = (a*k+r+1)*t :=
    min_eq_left (by nlinarith [Nat.mul_le_mul_right t (show r+1 ≤ a by omega)])
  unfold overlapMass
  rw [hlo, ← min_assoc, hhi, min_eq_left hK]
  exact if_pos (by nlinarith)

/-- Only pairs `(t,a*t)` survive in the old/new finite overlap sum. -/
theorem old_new_finite_head (p q a k r T : ℕ) (ha : 1 ≤ a) (ha3 : a ≤ 3)
    (hk : 0 < k) (hr : r < a) (hT : 12*T ≤ k) :
    (∑ j ∈ Finset.Icc 1 (a*k+r), ∑ i ∈ Finset.Icc 1 k,
      (jump p j * jump q i) * overlapMass (a*k+r) k ((a*k+r+1)*T) j i) =
      (1/((a*k+r:ℕ):ℝ) - 1/((a*k+r+1:ℕ):ℝ)) * sampledHarmonic p q a T := by
  classical
  let N := (a*k+r+1)*T
  let J := Finset.Icc 1 (a*k+r)
  let I := Finset.Icc 1 k
  let S := (Finset.Icc 1 T).image (fun t : ℕ => (t,a*t))
  let F : ℕ × ℕ → ℝ := fun z =>
    (jump p z.1 * jump q z.2) * overlapMass (a*k+r) k N z.1 z.2
  have hT3 : (a:ℕ)*T ≤ 3*T := Nat.mul_le_mul_right T ha3
  have hTk := Nat.mul_le_mul_left k hT
  have hT3k := Nat.mul_le_mul_left k hT3
  have hkk : k ≤ k*k := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (Nat.succ_le_of_lt hk)
  have hrT := Nat.mul_le_mul_right T (show r+1 ≤ a by omega)
  have hN : N ≤ k*k := by dsimp [N]; nlinarith
  have hS : S ⊆ J ×ˢ I := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
    have ht' := Finset.mem_Icc.mp ht
    have hat := Nat.mul_le_mul_left a ht'.2
    have hatpos := Nat.mul_pos (by omega : 0 < a) (by omega : 0 < t)
    have hka := Nat.mul_le_mul_right k ha
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
      let n := max ((a*k+r)*z.1) (k*z.2)
      have hnN : n < N := lt_of_lt_of_le hLU
        ((min_le_right _ _).trans (min_le_right _ _))
      have hn : n < k*k := lt_of_lt_of_le hnN hN
      have hnj : n ∈ Finset.Ico ((a*k+r)*z.1) ((a*k+r+1)*z.1) :=
        Finset.mem_Ico.mpr ⟨le_max_left _ _, lt_of_lt_of_le hLU (min_le_left _ _)⟩
      have hni : n ∈ Finset.Ico (k*z.2) ((k+1)*z.2) :=
        Finset.mem_Ico.mpr ⟨le_max_right _ _, lt_of_lt_of_le hLU
          ((min_le_right _ _).trans (min_le_left _ _))⟩
      have hjwidth : (r+1)*z.1 ≤ k := by
        have haj : a*z.1 < k := by
          by_contra h
          have hm := Nat.mul_le_mul_left k (Nat.le_of_not_gt h)
          have hl := (Finset.mem_Ico.mp hnj).1
          nlinarith
        have hm := Nat.mul_le_mul_right z.1 (show r+1 ≤ a by omega)
        omega
      have hiwidth : z.2 ≤ k := by
        by_contra h
        have hm := Nat.mul_le_mul_left k (show k+1 ≤ z.2 by omega)
        have hl := (Finset.mem_Ico.mp hni).1
        nlinarith
      have he : a*z.1 = z.2 := by
        simpa only [one_mul, add_zero, zero_add] using
          aligned_of_short_intersection a 1 k r 0 z.1 z.2 n hjwidth
            (by simpa using hiwidth) hnj (by simpa using hni)
      have hstart : a*k*z.1 ≤ n := by
        have hh := (Finset.mem_Ico.mp hnj).1
        nlinarith
      have hjT : z.1 ≤ T := by
        by_contra h
        have hmul := Nat.mul_le_mul_left (a*k) (show T+1 ≤ z.1 by omega)
        have hka := Nat.mul_le_mul_right k ha
        dsimp [N] at hnN
        nlinarith
      apply hzS
      apply Finset.mem_image.mpr
      refine ⟨z.1, Finset.mem_Icc.mpr ⟨hj'.1,hjT⟩, ?_⟩
      exact Prod.ext rfl he
    · simp
  change (∑ j ∈ J, ∑ i ∈ I, F (j,i)) = _
  calc
    _ = ∑ z ∈ J ×ˢ I, F z := by simp only [Finset.sum_product]
    _ = ∑ z ∈ S, F z := (Finset.sum_subset hS hz).symm
    _ = ∑ t ∈ Finset.Icc 1 T, F (t,a*t) := by
      dsimp [S]
      apply Finset.sum_image
      intro a' ha' b hb hab
      exact congrArg Prod.fst hab
    _ = _ := by
      unfold sampledHarmonic
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      dsimp [F]
      rw [old_new_aligned_overlapMass a k r t N ht'.1 hr
        (Nat.mul_le_mul_left (a*k+r+1) ht'.2)]
      push_cast
      simp only [mul_inv_rev, div_eq_mul_inv]
      ring

/-- Exact old/new covariance, without suppressing any signed tail. -/
theorem old_new_exact_harmonic_tail (p q a k r T : ℕ) (hp : 0 < p) (hq : 0 < q)
    (ha : 1 ≤ a) (ha3 : a ≤ 3) (hk : 0 < k) (hr : r < a) (hT : 12*T ≤ k) :
    crossCovariance p q (a*k+r) k =
      (1/((a*k+r:ℕ):ℝ) - 1/((a*k+r+1:ℕ):ℝ)) * sampledHarmonic p q a T +
      ∑' n, crossTail p q (a*k+r) k ((a*k+r+1)*T) n := by
  have hT3 : a*T ≤ 3*T := Nat.mul_le_mul_right T ha3
  have hTk := Nat.mul_le_mul_left k hT
  have hT3k := Nat.mul_le_mul_left k hT3
  have hkk : k ≤ k*k := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (Nat.succ_le_of_lt hk)
  have hrT := Nat.mul_le_mul_right T (show r+1 ≤ a by omega)
  have hN : (a*k+r+1)*T ≤ k*k := by nlinarith
  have hak := Nat.mul_le_mul_right k ha
  rw [cross_exact_head_tail p q (a*k+r) k ((a*k+r+1)*T) hp hq
    (by omega) hk (by nlinarith) (by nlinarith),
    old_new_finite_head p q a k r T ha ha3 hk hr hT]

/-- A uniform jump bound applies before the periodic mean is used. -/
theorem jump_abs_le (p j : ℕ) (hp : 0 < p) : |jump p j| ≤ p := by
  have h1 : 0 ≤ digitSequence p 1 j := Nat.cast_nonneg _
  have h2 : 0 ≤ digitSequence p 1 (j-1) := Nat.cast_nonneg _
  have h3 := digitSequence_abs_le p 1 hp j
  have h4 := digitSequence_abs_le p 1 hp (j-1)
  rw [abs_of_nonneg h1] at h3
  rw [abs_of_nonneg h2] at h4
  exact abs_le.mpr ⟨by unfold jump; linarith, by unfold jump; linarith⟩

private theorem jump_two_sample_period (a k : ℕ) (ha : 0 < a) :
    jump 2 (a*(k+6+1)) = jump 2 (a*(k+1)) := by
  have hprev (j : ℕ) : a*(j+1)-1 = a*j+(a-1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  simp [jump, digitSequence, hprev, Nat.add_mod, Nat.mul_mod]

private theorem jump_three_sample_period (a k : ℕ) (ha : 0 < a) :
    jump 3 (a*(k+6+1)) = jump 3 (a*(k+1)) := by
  have hprev (j : ℕ) : a*(j+1)-1 = a*j+(a-1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  simp [jump, digitSequence, hprev, Nat.add_mod, Nat.mul_mod]

private theorem sampledHarmonic_range (p q a T : ℕ) :
    sampledHarmonic p q a T =
      ∑ t ∈ Finset.range T, sampledJump p q a t / ((t:ℝ)+1) := by
  unfold sampledHarmonic
  rw [show Finset.Icc 1 T = Finset.Ico 1 (T+1) by ext t; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right, Nat.add_comm 1]
  push_cast
  rfl

private theorem sampledHarmonic_error (p q a T : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hperiod : ∀ t, sampledJump p q a (t+6) = sampledJump p q a t) :
    |sampledHarmonic p q a T -
      RiemannResearch.Analysis.periodicMean (sampledJump p q a) 6 * (harmonic T:ℝ)| ≤
      12*((p:ℝ)*q+|RiemannResearch.Analysis.periodicMean (sampledJump p q a) 6|) := by
  have h := RiemannResearch.Analysis.periodic_harmonic_mean_error_bound
    (sampledJump p q a) 6 (by omega) hperiod ((p:ℝ)*q)
    (fun t => bounded_product (fun t => jump_abs_le p (t+1) hp)
      (fun t => jump_abs_le q (a*(t+1)) hq) t) T
  rw [← sampledHarmonic_range] at h
  norm_num at h ⊢
  exact h

theorem old_new_binary_harmonic_error (T : ℕ) :
    |sampledHarmonic 2 2 3 T - (harmonic T:ℝ)| ≤ 60 := by
  have h := sampledHarmonic_error 2 2 3 T (by omega) (by omega) (fun t => by
    unfold sampledJump
    have h1 := jump_two_sample_period 1 t (by omega)
    simp only [one_mul] at h1
    rw [h1, jump_two_sample_period 3 t (by omega)])
  have hm : RiemannResearch.Analysis.periodicMean (sampledJump 2 2 3) 6 = 1 := by
    norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ,
      sampledJump, jump, digitSequence]
  norm_num [hm] at h
  exact h

theorem old_new_ternary_harmonic_error (T : ℕ) :
    |sampledHarmonic 3 3 2 T - 2*(harmonic T:ℝ)| ≤ 132 := by
  have h := sampledHarmonic_error 3 3 2 T (by omega) (by omega) (fun t => by
    unfold sampledJump
    have h1 := jump_three_sample_period 1 t (by omega)
    simp only [one_mul] at h1
    rw [h1, jump_three_sample_period 2 t (by omega)])
  have hm : RiemannResearch.Analysis.periodicMean (sampledJump 3 3 2) 6 = 2 := by
    norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ,
      sampledJump, jump, digitSequence]
  norm_num [hm] at h
  exact h

theorem old_new_binary_ternary_harmonic_bound (T : ℕ) :
    |sampledHarmonic 2 3 3 T| ≤ 72 := by
  have h := sampledHarmonic_error 2 3 3 T (by omega) (by omega) (fun t => by
    unfold sampledJump
    have h1 := jump_two_sample_period 1 t (by omega)
    simp only [one_mul] at h1
    rw [h1, jump_three_sample_period 3 t (by omega)])
  have hm : RiemannResearch.Analysis.periodicMean (sampledJump 2 3 3) 6 = 0 := by
    norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ,
      sampledJump, jump, digitSequence]
  norm_num [hm] at h
  exact h

theorem old_new_ternary_binary_harmonic_bound (T : ℕ) :
    |sampledHarmonic 3 2 2 T| ≤ 72 := by
  have h := sampledHarmonic_error 3 2 2 T (by omega) (by omega) (fun t => by
    unfold sampledJump
    have h1 := jump_three_sample_period 1 t (by omega)
    simp only [one_mul] at h1
    rw [h1, jump_two_sample_period 2 t (by omega)])
  have hm : RiemannResearch.Analysis.periodicMean (sampledJump 3 2 2) 6 = 0 := by
    norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ,
      sampledJump, jump, digitSequence]
  norm_num [hm] at h
  exact h

end
end RiemannResearch.RH.Pareto.AdjacentDigit
