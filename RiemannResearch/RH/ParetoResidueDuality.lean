/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# ParetoResidueDuality

Genuine residue functions, Möbius difference duality, packet incidence, and bounded prime-factor annihilation. Source: user-provided argument RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md, §§3,5,6,13. The finite divisor inversion uses Mathlib's genuine Möbius function. No all-scale estimate or RH is assumed or proved.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def residue (n k : ℕ) : ℝ := (k % n : ℕ)
def dilation (n : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ := n * f (k / n)
def ramanujanPacket (q k : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, (ArithmeticFunction.moebius (q / d) : ℝ) * residue d k
def mobiusDifference (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m / d) : ℝ) * (f d - f (d-1))

theorem residue_mul_floor (n r k : ℕ) :
    dilation n (residue r) k = residue (n*r) k - residue n k := by
  unfold dilation residue
  rw [Nat.mod_mul, Nat.cast_add, Nat.cast_mul]
  ring

private theorem residue_difference_int (n k : ℕ) (hk : 0 < k) :
    ((k % n : ℕ) : ℤ) - (((k-1) % n : ℕ) : ℤ) =
      1 - if n ∣ k then (n : ℤ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.mod_zero, zero_dvd_iff, ne_of_gt hk, ↓reduceIte, sub_zero]
    omega
  have hmod := Nat.mod_lt (k-1) (Nat.pos_of_ne_zero hn)
  have hm : ((k-1) % n + 1) % n = k % n := by
    rw [Nat.mod_add_mod, Nat.sub_add_cancel hk]
  by_cases hb : (k-1) % n + 1 < n
  · rw [Nat.mod_eq_of_lt hb] at hm
    have hd : ¬ n ∣ k := by
      intro h
      have := Nat.mod_eq_zero_of_dvd h
      omega
    simp only [hd, ↓reduceIte, sub_zero]
    omega
  · have he : (k-1) % n + 1 = n := by omega
    rw [he, Nat.mod_self] at hm
    have hd : n ∣ k := Nat.dvd_of_mod_eq_zero hm.symm
    simp only [hd, ↓reduceIte]
    omega

theorem residue_difference (n k : ℕ) (hk : 0 < k) :
    residue n k - residue n (k-1) = 1 - if n ∣ k then (n : ℝ) else 0 := by
  unfold residue
  have h := residue_difference_int n k hk
  split_ifs at h ⊢ with hd <;> exact_mod_cast h

theorem mobius_inversion (f g : ℕ → ℝ) :
    (∀ n > 0, ∑ d ∈ n.divisors, f d = g n) ↔
      ∀ n > 0, ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius (n/d) : ℝ) * g d = f n := by
  simpa only [Nat.sum_divisorsAntidiagonal'
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * g b)] using
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := f) (g := g))

theorem mobiusDifference_residue (m n : ℕ) (hm : 1 < m) :
    mobiusDifference m (residue n) = if m = n then -(n : ℝ) else 0 := by
  let f : ℕ → ℝ := fun d => (if d = 1 then 1 else 0) -
    (if d = n then (n : ℝ) else 0)
  have hs : ∀ k > 0, ∑ d ∈ k.divisors, f d = residue n k - residue n (k-1) := by
    intro k hk
    rw [residue_difference n k hk]
    simp [f, Finset.sum_sub_distrib, Nat.mem_divisors, ne_of_gt hk]
  have hi := (mobius_inversion f (fun k => residue n k - residue n (k-1))).mp hs m
    (by omega)
  simp only [f, if_neg (ne_of_gt hm), zero_sub] at hi
  by_cases he : m = n <;> simpa [mobiusDifference, he] using hi

theorem mobiusDifference_packet (m q : ℕ) (hm : 1 < m) (hq : 0 < q) :
    mobiusDifference m (ramanujanPacket q) =
      if m ∣ q then -(m : ℝ) * ArithmeticFunction.moebius (q/m) else 0 := by
  unfold mobiusDifference ramanujanPacket
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (d : ℕ) :
      (∑ k ∈ m.divisors, (ArithmeticFunction.moebius (m/k) : ℝ) *
        ((ArithmeticFunction.moebius (q/d) : ℝ) *
          (residue d k - residue d (k-1)))) =
        (ArithmeticFunction.moebius (q/d) : ℝ) *
          (if m = d then -(d : ℝ) else 0) := by
    rw [← mobiusDifference_residue m d hm]
    unfold mobiusDifference
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm]
  simp [Nat.mem_divisors, ne_of_gt hq, mul_comm]

theorem ramanujanPacket_divisor_sum (n k : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, ramanujanPacket d k = residue n k := by
  exact (mobius_inversion (fun d => ramanujanPacket d k) (fun d => residue d k)).mpr
    (by intro d hd; rfl) n hn

theorem mobiusDifference_one (m : ℕ) (hm : 0 < m) :
    mobiusDifference m (fun k => if k = 0 then 0 else 1) =
      ArithmeticFunction.moebius m := by
  unfold mobiusDifference
  have h (d : ℕ) (hd : d ∈ m.divisors) :
      ((if d = 0 then 0 else 1 : ℝ) - (if d-1 = 0 then 0 else 1)) =
        if d = 1 then 1 else 0 := by
    have hp := Nat.pos_of_mem_divisors hd
    by_cases h1 : d = 1
    · subst d; norm_num
    · have h0 : d ≠ 0 := by omega
      have hp0 : d-1 ≠ 0 := by omega
      simp [h1, h0, hp0]
  trans ∑ d ∈ m.divisors, (ArithmeticFunction.moebius (m/d) : ℝ) *
    (if d = 1 then 1 else 0)
  · apply Finset.sum_congr rfl
    intro d hd
    rw [h d hd]
  · simp [mul_ite, Nat.mem_divisors, ne_of_gt hm]

theorem mobiusDifference_sum (m : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) :
    mobiusDifference m (fun k => ∑ q ∈ s, c q * f q k) =
      ∑ q ∈ s, c q * mobiusDifference m (f q) := by
  unfold mobiusDifference
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem packet_dual_zero_of_primeFactors_card_lt (m q : ℕ)
    (hm : 1 < m) (hq : 0 < q)
    (hcard : q.primeFactors.card < m.primeFactors.card) :
    mobiusDifference m (ramanujanPacket q) = 0 := by
  rw [mobiusDifference_packet m q hm hq]
  have hnd : ¬ m ∣ q := by
    intro hd
    have hc := Finset.card_le_card (Nat.primeFactors_mono hd (ne_of_gt hq))
    omega
  simp [hnd]

theorem primePowerPacket_dual_zero (m p a : ℕ) (hm : 1 < m)
    (hc : 1 < m.primeFactors.card) (hp : p.Prime) :
    mobiusDifference m (ramanujanPacket (p^a)) = 0 := by
  apply packet_dual_zero_of_primeFactors_card_lt m (p^a) hm (pow_pos hp.pos a)
  by_cases ha : a = 0
  · subst a; simpa using (show 0 < m.primeFactors.card by omega)
  · simpa [Nat.primeFactors_prime_pow ha hp] using hc

theorem boundedPrimeSupport_dual_zero (m r : ℕ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hm : 1 < m) (hc : r < m.primeFactors.card)
    (hs : ∀ q ∈ s, 0 < q ∧ q.primeFactors.card ≤ r) :
    mobiusDifference m (fun k => ∑ q ∈ s, c q * ramanujanPacket q k) = 0 := by
  rw [mobiusDifference_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [packet_dual_zero_of_primeFactors_card_lt m q hm (hs q hq).1 (by
    have := (hs q hq).2
    omega), mul_zero]

/-- Coefficients of the finite Möbius difference witness on positive coordinates. -/
def dualCoeff (m k : ℕ) : ℤ :=
  (if k ∣ m then ArithmeticFunction.moebius (m/k) else 0) -
    (if k+1 ∣ m then ArithmeticFunction.moebius (m/(k+1)) else 0)

end
end RiemannResearch.RH.Pareto
