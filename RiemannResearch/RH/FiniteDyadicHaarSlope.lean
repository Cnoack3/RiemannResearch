/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteMeanZeroSlope
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Finite dyadic Haar atoms in slope coordinates

The literal slope index is Fin (2 ^ m). At each valid level l<m and block q,
the atom is + 1 on its first half, -1 on its second half, and zero outside.
Exact counting proves zero sum and squared norm 2 ^ (m-l). The atoms are
pairwise orthogonal for the unweighted counting inner product, and their
adjacent differences are the three jumps + 1, -2, + 1, with boundary truncation.

Source: user-provided argument, RH_Proof_First_Continuation_2026-09-04.md,
Section 5, and RH_Lean_Autonomous_Next_Task_Handoff.md, version 14.
These sources support the finite dyadic construction and research direction.
The detailed Haar algebra is developed here without a novelty claim.
No arithmetic kernel, analytic density, or RH positivity is established.
-/

open scoped BigOperators
namespace RiemannResearch.RH.PrimeGapCurvature
noncomputable section
/-- The number of natural coordinates in a half-open interval inside Fin N. -/
lemma finiteIntervalIndicator_sum (N a b : ℕ) (hb : b ≤ N) :
    (∑ j : Fin N, if a ≤ j.val ∧ j.val < b then (1 : ℝ) else 0) =
      ((b - a : ℕ) : ℝ) := by
  classical
  calc
    _ = ∑ k ∈ Finset.range N, if a ≤ k ∧ k < b then (1 : ℝ) else 0 :=
      Fin.sum_univ_eq_sum_range (fun k => if a ≤ k ∧ k < b then (1 : ℝ) else 0) N
    _ = _ := by
      rw [Finset.sum_boole]
      have hf : {k ∈ Finset.range N | a ≤ k ∧ k < b} = Finset.Ico a b := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hf, Nat.card_Ico]

private lemma dyadic_factor (m l : ℕ) (hl : l < m) :
    2 ^ l * (2 * 2 ^ (m - l - 1)) = 2 ^ m := by
  rw [← pow_succ']
  rw [← pow_add]
  congr 1
  omega

/-- The unnormalised Haar atom on two adjacent dyadic half-blocks. -/
def finiteDyadicHaarAtom (m l : ℕ) (q : Fin (2 ^ l)) (j : Fin (2 ^ m)) : ℝ :=
  let h := 2 ^ (m - l - 1)
  let a := 2 * q.val * h
  (if a ≤ j.val ∧ j.val < a + h then 1 else 0) -
    (if a + h ≤ j.val ∧ j.val < a + 2 * h then 1 else 0)

private lemma dyadic_block_bound (m l : ℕ) (hl : l < m) (q : Fin (2 ^ l)) :
    2 * q.val * 2 ^ (m - l - 1) + 2 * 2 ^ (m - l - 1) ≤ 2 ^ m := by
  have hq : q.val + 1 ≤ 2 ^ l := q.isLt
  have h := Nat.mul_le_mul_right (2 * 2 ^ (m - l - 1)) hq
  rw [dyadic_factor m l hl] at h
  nlinarith

/-- The two equal-length halves have cancelling coordinate sums. -/
theorem finiteDyadicHaarAtom_sum_zero (m l : ℕ) (hl : l < m) (q : Fin (2 ^ l)) :
    (∑ j, finiteDyadicHaarAtom m l q j) = 0 := by
  have hb := dyadic_block_bound m l hl q
  unfold finiteDyadicHaarAtom
  simp only
  rw [Finset.sum_sub_distrib]
  rw [finiteIntervalIndicator_sum _ _ _ (by omega), finiteIntervalIndicator_sum _ _ _ hb]
  simp only [Nat.add_sub_cancel_left]
  have he : 2 * q.val * 2 ^ (m - l - 1) + 2 * 2 ^ (m - l - 1) -
      (2 * q.val * 2 ^ (m - l - 1) + 2 ^ (m - l - 1)) = 2 ^ (m - l - 1) := by omega
  rw [he]
  exact sub_self _

/-- The explicit dimension equality used to transport to the slope submodule. -/
lemma dyadicDimension_eq (m : ℕ) : 2 ^ m - 1 + 1 = 2 ^ m := by
  have : 0 < 2 ^ m := by positivity
  omega

/-- The literal atom, transported by the dimension equality, is a zero-sum slope. -/
theorem finiteDyadicHaarAtom_mem_meanZeroSlopeSubmodule
    (m l : ℕ) (hl : l < m) (q : Fin (2 ^ l)) :
    (fun j : Fin (2 ^ m - 1 + 1) =>
      finiteDyadicHaarAtom m l q (Fin.cast (dyadicDimension_eq m) j)) ∈
        meanZeroSlopeSubmodule (2 ^ m - 1) := by
  change (∑ j : Fin (2 ^ m - 1 + 1),
    finiteDyadicHaarAtom m l q (Fin.cast (dyadicDimension_eq m) j)) = 0
  rw [show (∑ j : Fin (2 ^ m - 1 + 1),
    finiteDyadicHaarAtom m l q (Fin.cast (dyadicDimension_eq m) j)) =
    ∑ j : Fin (2 ^ m), finiteDyadicHaarAtom m l q j from
      (Fin.castOrderIso (dyadicDimension_eq m)).toEquiv.sum_comp _]
  exact finiteDyadicHaarAtom_sum_zero m l hl q

/-- The squared atom is exactly the indicator of its whole dyadic block. -/
theorem finiteDyadicHaarAtom_sq
    (m l : ℕ) (q : Fin (2 ^ l)) (j : Fin (2 ^ m)) :
    finiteDyadicHaarAtom m l q j ^ 2 =
      if 2 * q.val * 2 ^ (m - l - 1) ≤ j.val ∧
        j.val < 2 * q.val * 2 ^ (m - l - 1) + 2 * 2 ^ (m - l - 1) then 1 else 0 := by
  unfold finiteDyadicHaarAtom
  dsimp only
  split_ifs <;> norm_num <;> omega

/-- The exact counting squared norm of a valid atom is its block length. -/
theorem finiteDyadicHaarAtom_sum_sq
    (m l : ℕ) (hl : l < m) (q : Fin (2 ^ l)) :
    (∑ j, finiteDyadicHaarAtom m l q j ^ 2) = ((2 ^ (m - l) : ℕ) : ℝ) := by
  simp_rw [finiteDyadicHaarAtom_sq]
  rw [finiteIntervalIndicator_sum _ _ _ (dyadic_block_bound m l hl q)]
  simp only [Nat.add_sub_cancel_left]
  congr 1
  have he : m - l = (m - l - 1) + 1 := by omega
  conv_rhs => rw [he, pow_succ']


private def intervalHaar (h r j : ℕ) : ℝ :=
  (if 2 * r * h ≤ j ∧ j < 2 * r * h + h then 1 else 0) -
  (if 2 * r * h + h ≤ j ∧ j < 2 * r * h + 2 * h then 1 else 0)
private theorem threshold_constancy {B r j t : ℕ} (hlo : r * B ≤ j) (hhi : j < (r + 1) * B) :
    (t * B ≤ j ↔ t ≤ r) ∧ (j < t * B ↔ r < t) := by
  constructor
  · constructor
    · intro h
      by_contra hn
      have hh : r + 1 ≤ t := by omega
      have hm := Nat.mul_le_mul_right B hh
      omega
    · intro h
      exact (Nat.mul_le_mul_right B h).trans hlo
  · constructor
    · intro h
      by_contra hn
      have hh : t ≤ r := by omega
      have hm := Nat.mul_le_mul_right B hh
      omega
    · intro h
      have hh : r + 1 ≤ t := by omega
      exact hhi.trans_le (Nat.mul_le_mul_right B hh)

private theorem intervalHaar_support {h r j : ℕ}
    (hn : intervalHaar h r j ≠ 0) :
    r * (2 * h) ≤ j ∧ j < (r + 1) * (2 * h) := by
  unfold intervalHaar at hn
  split_ifs at hn <;> simp_all <;> constructor <;> nlinarith

private theorem intervalHaar_constant_on_fine {h D q r j : ℕ}
    (hj : intervalHaar h r j ≠ 0) :
    intervalHaar (D * (2 * h)) q j =
      (if 2 * q * D ≤ r ∧ r < (2 * q + 1) * D then 1 else 0) -
      (if (2 * q + 1) * D ≤ r ∧ r < (2 * q + 2) * D then 1 else 0) := by
  have hs := intervalHaar_support hj
  have h0 := threshold_constancy (t:=2 * q * D) hs.1 hs.2
  have h1 := threshold_constancy (t:=(2 * q + 1) * D) hs.1 hs.2
  have h2 := threshold_constancy (t:=(2 * q + 2) * D) hs.1 hs.2
  have e0 : 2 * q * (D * (2 * h)) = (2 * q * D) * (2 * h) := by ring
  unfold intervalHaar
  rw [e0]
  have e1' : 2 * q * D * (2 * h) + D * (2 * h) = ((2 * q + 1) * D) * (2 * h) := by ring
  have e2' : 2 * q * D * (2 * h) + 2 * (D * (2 * h)) = ((2 * q + 2) * D) * (2 * h) := by ring
  simp only [e1', e2', h0.1, h1.2, h1.1, h2.2]

private theorem intervalHaar_cross_inner_zero {N h D q r : ℕ}
    (hz : ∑ j : Fin N, intervalHaar h r j.val = 0) :
    ∑ j : Fin N, intervalHaar (D * (2 * h)) q j.val * intervalHaar h r j.val = 0 := by
  let c : ℝ :=
      (if 2 * q * D ≤ r ∧ r < (2 * q + 1) * D then 1 else 0) -
      (if (2 * q + 1) * D ≤ r ∧ r < (2 * q + 2) * D then 1 else 0)
  have heq : ∀ j : Fin N, intervalHaar (D * (2 * h)) q j.val * intervalHaar h r j.val
      = c * intervalHaar h r j.val := by
    intro j
    by_cases hj : intervalHaar h r j.val = 0
    · simp [hj]
    · rw [intervalHaar_constant_on_fine hj]
  calc
    _ = ∑ j : Fin N, c * intervalHaar h r j.val := Finset.sum_congr rfl (by intros; apply heq)
    _ = c * ∑ j : Fin N, intervalHaar h r j.val := (Finset.mul_sum _ _ _).symm
    _ = 0 := by rw [hz, mul_zero]

private theorem intervalHaar_same_scale_mul_zero {h q r j : ℕ} (hqr : q ≠ r) :
    intervalHaar h q j * intervalHaar h r j = 0 := by
  by_cases hq : intervalHaar h q j = 0
  · simp [hq]
  by_cases hr : intervalHaar h r j = 0
  · simp [hr]
  have hqs := intervalHaar_support hq
  have hrs := intervalHaar_support hr
  have hle : r ≤ q := (threshold_constancy (t:=r) hqs.1 hqs.2).1.mp hrs.1
  have hge : q ≤ r := (threshold_constancy (t:=q) hrs.1 hrs.2).1.mp hqs.1
  exact False.elim (hqr (Nat.le_antisymm hge hle))

private theorem dyadic_cross_factor (m l k : ℕ) (hlk : l < k) (hkm : k < m) :
    2 ^ (m - l - 1) = 2 ^ (k - l - 1) * (2 * 2 ^ (m - k - 1)) := by
  rw [← pow_succ', ← pow_add]
  congr 1
  omega

/-- A coarser atom is constant on the support of a finer atom. -/
theorem finiteDyadicHaarAtom_inner_zero_of_lt
    (m l k : ℕ) (hlk : l < k) (hkm : k < m)
    (q : Fin (2 ^ l)) (r : Fin (2 ^ k)) :
    (∑ j, finiteDyadicHaarAtom m l q j * finiteDyadicHaarAtom m k r j) = 0 := by
  change (∑ j : Fin (2 ^ m), intervalHaar (2 ^ (m - l - 1)) q.val j.val *
      intervalHaar (2 ^ (m - k - 1)) r.val j.val) = 0
  rw [dyadic_cross_factor m l k hlk hkm]
  apply intervalHaar_cross_inner_zero
  exact finiteDyadicHaarAtom_sum_zero m k hkm r

/-- Distinct blocks at the same scale have disjoint support. -/
theorem finiteDyadicHaarAtom_inner_zero_same_level
    (m l : ℕ) (q r : Fin (2 ^ l)) (hqr : q ≠ r) :
    (∑ j, finiteDyadicHaarAtom m l q j * finiteDyadicHaarAtom m l r j) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact intervalHaar_same_scale_mul_zero (Fin.val_ne_of_ne hqr)

/-- Atoms with different valid level/block labels are orthogonal. -/
theorem finiteDyadicHaarAtom_inner_zero
    (m l k : ℕ) (hlm : l < m) (hkm : k < m)
    (q : Fin (2 ^ l)) (r : Fin (2 ^ k)) (hqr : l ≠ k ∨ q.val ≠ r.val) :
    (∑ j, finiteDyadicHaarAtom m l q j * finiteDyadicHaarAtom m k r j) = 0 := by
  rcases lt_trichotomy l k with hlk | hlk | hlk
  · exact finiteDyadicHaarAtom_inner_zero_of_lt m l k hlk hkm q r
  · subst k
    apply finiteDyadicHaarAtom_inner_zero_same_level m l q r
    rcases hqr with hn | hn
    · exact False.elim (hn rfl)
    · exact fun he => hn (congrArg Fin.val he)
  · calc
      _ = ∑ j, finiteDyadicHaarAtom m k r j * finiteDyadicHaarAtom m l q j :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = 0 := finiteDyadicHaarAtom_inner_zero_of_lt m k l hlk hlm r q






private theorem finiteIntervalIndicator_difference (a b k : ℕ) (hab : a ≤ b) :
    (if a ≤ k + 1 ∧ k + 1 < b then (1 : ℝ) else 0) -
        (if a ≤ k ∧ k < b then (1 : ℝ) else 0) =
      (if k + 1 = a then 1 else 0) - (if k + 1 = b then 1 else 0) := by
  split_ifs <;> norm_num <;> omega

/-- The curvature coordinates of a finite Haar atom are the three endpoint
jumps, with exterior endpoint jumps absent from the finite difference range. -/
theorem finiteDyadicHaarAtom_slopeDifference
    (m l : ℕ) (q : Fin (2 ^ l)) (i : Fin (2 ^ m - 1)) :
    finiteSlopeDifferenceMap (2 ^ m - 1)
      (fun j => finiteDyadicHaarAtom m l q
        (Fin.cast (dyadicDimension_eq m) j)) i =
      let h := 2 ^ (m - l - 1)
      let a := 2 * q.val * h
      (if i.val + 1 = a then 1 else 0) -
        2 * (if i.val + 1 = a + h then 1 else 0) +
        (if i.val + 1 = a + 2 * h then 1 else 0) := by
  let h := 2 ^ (m - l - 1)
  let a := 2 * q.val * h
  change
    ((if a ≤ i.val + 1 ∧ i.val + 1 < a + h then (1 : ℝ) else 0) -
      (if a + h ≤ i.val + 1 ∧ i.val + 1 < a + 2 * h then 1 else 0)) -
    ((if a ≤ i.val ∧ i.val < a + h then 1 else 0) -
      (if a + h ≤ i.val ∧ i.val < a + 2 * h then 1 else 0)) = _
  calc
    _ =
      ((if a ≤ i.val + 1 ∧ i.val + 1 < a + h then (1 : ℝ) else 0) -
        (if a ≤ i.val ∧ i.val < a + h then 1 else 0)) -
      ((if a + h ≤ i.val + 1 ∧ i.val + 1 < a + 2 * h then 1 else 0) -
        (if a + h ≤ i.val ∧ i.val < a + 2 * h then 1 else 0)) := by ring
    _ = _ := by
      rw [finiteIntervalIndicator_difference a (a + h) i.val (Nat.le_add_right a h),
        finiteIntervalIndicator_difference (a + h) (a + 2 * h) i.val
          (Nat.add_le_add_left (by simp [two_mul]) a)]
      ring

end

end RiemannResearch.RH.PrimeGapCurvature
