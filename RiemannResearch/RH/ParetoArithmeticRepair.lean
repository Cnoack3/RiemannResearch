/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoPrimePackets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# ParetoArithmeticRepair

The finite arithmetic part of the head-preserving repairs in
*Noise, signal, and arithmetic repair* (2026-09-07), §§4–5.
The residue functions and Möbius difference functionals are genuine. These
results prove cancellation and identify exactly which conductor defects change.
They do not assume or prove a smooth-number gap estimate, a variance bound,
or convergence of an infinite family of repairs.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A four-residue repair with an old scale `E` and new scale `p`. -/
def arithmeticRepair (b p E k : ℕ) : ℝ :=
  (p : ℝ)⁻¹ *
    (residue p k - residue (b*p) k - residue E k + residue (b*E) k)

theorem arithmeticRepair_eq_quotient (b p E k : ℕ) :
    arithmeticRepair b p E k =
      (residue p k - residue (b*p) k - residue E k + residue (b*E) k) /
        (p : ℝ) := by
  simp only [arithmeticRepair, div_eq_mul_inv, mul_comm]

/-- Every value strictly before the new conductor is preserved. -/
theorem arithmeticRepair_head_zero (b p E k : ℕ)
    (hb : 1 ≤ b) (hpE : p ≤ E) (hk : k < p) :
    arithmeticRepair b p E k = 0 := by
  have hbp : k < b*p := by nlinarith
  have hE : k < E := by omega
  have hbE : k < b*E := by nlinarith
  simp [arithmeticRepair, residue, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt hbp, Nat.mod_eq_of_lt hE, Nat.mod_eq_of_lt hbE]

/-- The same repair is a difference of two floor dilations. -/
theorem arithmeticRepair_eq_dilation (b p E k : ℕ) :
    arithmeticRepair b p E k = (p : ℝ)⁻¹ *
      (dilation E (residue b) k - dilation p (residue b) k) := by
  rw [residue_mul_floor, residue_mul_floor]
  simp only [arithmeticRepair, Nat.mul_comm]
  ring

/-- The floor representation used to compute the full noise cost. -/
theorem arithmeticRepair_eq_floor (b p E k : ℕ) (hp : 0 < p) :
    arithmeticRepair b p E k =
      (E : ℝ) / (p : ℝ) * residue b (k/E) - residue b (k/p) := by
  rw [arithmeticRepair_eq_dilation]
  unfold dilation
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  field_simp [hp0]
  <;> ring

theorem mobiusDifference_add_fn (m : ℕ) (f g : ℕ → ℝ) :
    mobiusDifference m (fun k => f k + g k) =
      mobiusDifference m f + mobiusDifference m g := by
  unfold mobiusDifference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem mobiusDifference_sub_fn (m : ℕ) (f g : ℕ → ℝ) :
    mobiusDifference m (fun k => f k - g k) =
      mobiusDifference m f - mobiusDifference m g := by
  unfold mobiusDifference
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem mobiusDifference_const_mul_fn (m : ℕ) (a : ℝ) (f : ℕ → ℝ) :
    mobiusDifference m (fun k => a * f k) = a * mobiusDifference m f := by
  unfold mobiusDifference
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Exact response at every Möbius defect index, including composite indices. -/
theorem mobiusDifference_arithmeticRepair (m b p E : ℕ) (hm : 1 < m) :
    mobiusDifference m (arithmeticRepair b p E) = (p : ℝ)⁻¹ *
      ((if m = p then -(p : ℝ) else 0) -
       (if m = b*p then -((b*p : ℕ) : ℝ) else 0) -
       (if m = E then -(E : ℝ) else 0) +
       (if m = b*E then -((b*E : ℕ) : ℝ) else 0)) := by
  unfold arithmeticRepair
  rw [mobiusDifference_const_mul_fn, mobiusDifference_add_fn,
    mobiusDifference_sub_fn, mobiusDifference_sub_fn]
  simp only [mobiusDifference_residue _ _ hm]

theorem arithmeticRepair_new_defect (b p E : ℕ) (hp : 1 < p)
    (hbp : p ≠ b*p) (hE : p ≠ E) (hbE : p ≠ b*E) :
    mobiusDifference p (arithmeticRepair b p E) = -1 := by
  rw [mobiusDifference_arithmeticRepair p b p E hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  simp [hbp, hE, hbE, hp0]

theorem arithmeticRepair_other_defect (m b p E : ℕ) (hm : 1 < m)
    (hmp : m ≠ p) (hmbp : m ≠ b*p) (hmE : m ≠ E) (hmbE : m ≠ b*E) :
    mobiusDifference m (arithmeticRepair b p E) = 0 := by
  rw [mobiusDifference_arithmeticRepair m b p E hm]
  simp [hmp, hmbp, hmE, hmbE]

/-- Composite old scales guarantee that other prime defects are preserved. -/
theorem arithmeticRepair_other_prime (q b p E : ℕ) (hq : q.Prime)
    (hqp : q ≠ p) (hbp : ¬ (b*p).Prime) (hE : ¬ E.Prime)
    (hbE : ¬ (b*E).Prime) :
    mobiusDifference q (arithmeticRepair b p E) = 0 := by
  apply arithmeticRepair_other_defect q b p E hq.one_lt hqp
  · intro h
    exact hbp (h ▸ hq)
  · intro h
    exact hE (h ▸ hq)
  · intro h
    exact hbE (h ▸ hq)

/-- A convenient finite mixed-packet sum; its indices are `r*d` with `d>1`. -/
def mixedPrimeLift (r n k : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => 1 < d), ramanujanPacket (r*d) k

theorem ramanujanPacket_divisor_sum_gt_one (n k : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => 1 < d), ramanujanPacket d k) =
      residue n k := by
  calc
    _ = ∑ d ∈ n.divisors, ramanujanPacket d k := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      have hdpos := Nat.pos_of_mem_divisors hd
      have hdle : ¬ 1 < d := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hd, h⟩)
      have hd1 : d = 1 := by omega
      subst d
      simp [ramanujanPacket, residue] <;> omega
    _ = residue n k := ramanujanPacket_divisor_sum n k hn

/-- Genuine packet legality, proved by finite divisor inversion. -/
theorem mixedPrimeLift_eq_residues (r n k : ℕ) (hr : r.Prime)
    (hn : 0 < n) (hrn : ¬ r ∣ n) :
    mixedPrimeLift r n k = residue (r*n) k - residue r k - residue n k := by
  unfold mixedPrimeLift
  calc
    _ = ∑ d ∈ n.divisors.filter (fun d => 1 < d),
        (dilation r (ramanujanPacket d) k - ramanujanPacket d k) := by
      apply Finset.sum_congr rfl
      intro d hd
      rcases Finset.mem_filter.mp hd with ⟨hd, hd1⟩
      exact ramanujanPacket_mul_prime_of_not_dvd r d k hr hd1
        (fun h => hrn (dvd_trans h (Nat.dvd_of_mem_divisors hd)))
    _ = dilation r (residue n) k - residue n k := by
      unfold dilation
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        ramanujanPacket_divisor_sum_gt_one n (k/r) hn,
        ramanujanPacket_divisor_sum_gt_one n k hn]
    _ = residue (r*n) k - residue r k - residue n k := by
      rw [residue_mul_floor]

/-- In particular, the binary repair is a finite sum of mixed packet sums. -/
theorem arithmeticRepair_eq_mixedPrimeLift (b p E k : ℕ) (hb : b.Prime)
    (hp : 0 < p) (hE : 0 < E) (hbp : ¬ b ∣ p) (hbE : ¬ b ∣ E) :
    arithmeticRepair b p E k = (p : ℝ)⁻¹ *
      (mixedPrimeLift b E k - mixedPrimeLift b p k) := by
  rw [mixedPrimeLift_eq_residues b E k hb hE hbE,
    mixedPrimeLift_eq_residues b p k hb hp hbp]
  unfold arithmeticRepair
  ring

/-- The two-index functional exposing the binary repair family's limitation. -/
def binaryRepairInvariant (p : ℕ) (f : ℕ → ℝ) : ℝ :=
  mobiusDifference (2*p) f + 2 * mobiusDifference p f

/-- Each binary repair is annihilated when the old scale avoids the two
indices and distinct new scales cannot meet across the factor `2`. -/
theorem binaryRepairInvariant_arithmeticRepair (p q E : ℕ) (hp : 1 < p)
    (hp2q : p ≠ 2*q) (h2pq : 2*p ≠ q)
    (hpE : p ≠ E) (hp2E : p ≠ 2*E)
    (h2pE : 2*p ≠ E) (h2p2E : 2*p ≠ 2*E) :
    binaryRepairInvariant p (arithmeticRepair 2 q E) = 0 := by
  unfold binaryRepairInvariant
  rw [mobiusDifference_arithmeticRepair (2*p) 2 q E (by omega),
    mobiusDifference_arithmeticRepair p 2 q E hp]
  by_cases hpq : p = q
  · subst q
    simp only [if_neg hp2q, if_neg h2pq, if_neg hpE, if_neg hp2E,
      if_neg h2pE, if_neg h2p2E, if_pos rfl, Nat.cast_mul, Nat.cast_ofNat]
    simp only [ite_true]
    ring
  · have h2p2q : 2*p ≠ 2*q := by omega
    simp [hpq, h2p2q, hp2q, h2pq, hpE, hp2E, h2pE, h2p2E]

theorem binaryRepairInvariant_sum (p : ℕ) (s : Finset ℕ)
    (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    binaryRepairInvariant p (fun k => ∑ q ∈ s, c q * f q k) =
      ∑ q ∈ s, c q * binaryRepairInvariant p (f q) := by
  unfold binaryRepairInvariant
  rw [mobiusDifference_sum, mobiusDifference_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- No finite linear combination can escape an invariant satisfied by each
direction. This is the finite arithmetic premise of the continuity argument. -/
theorem binaryRepairInvariant_sum_zero (p : ℕ) (s : Finset ℕ)
    (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ q ∈ s, binaryRepairInvariant p (f q) = 0) :
    binaryRepairInvariant p (fun k => ∑ q ∈ s, c q * f q k) = 0 := by
  rw [binaryRepairInvariant_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [hf q hq, mul_zero]

theorem binaryRepairInvariant_add_fn (p : ℕ) (f g : ℕ → ℝ) :
    binaryRepairInvariant p (fun k => f k + g k) =
      binaryRepairInvariant p f + binaryRepairInvariant p g := by
  unfold binaryRepairInvariant
  rw [mobiusDifference_add_fn, mobiusDifference_add_fn]
  ring

end
end RiemannResearch.RH.Pareto
