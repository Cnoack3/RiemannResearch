import RiemannResearch.RH.ParetoAnchoredGreen
import RiemannResearch.RH.ParetoCovariance
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exact packet Gram identity for the Pareto Green kernel

Source: user-provided argument in
`RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md`.
The Ramanujan sum is given by its classical divisor formula. The finite
identity keeps the right boundary 1/(N+1), and the full inner product keeps
the genuine infinite Pareto tail. No asymptotic approximation claim is made.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The classical divisor formula for the Ramanujan sum. -/
def ramanujanSum (q k : ℕ) : ℝ :=
  ∑ d ∈ q.divisors,
    (ArithmeticFunction.moebius (q / d) : ℝ) * (if d ∣ k then (d : ℝ) else 0)

theorem ramanujanPacket_increment (q k : ℕ) (hq : 1 < q) (hk : 0 < k) :
    ramanujanPacket q k - ramanujanPacket q (k-1) = -ramanujanSum q k := by
  unfold ramanujanPacket
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, residue_difference _ k hk, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, sum_moebius_div q hq]
  simp [ramanujanSum]

theorem ramanujanPacket_prefix (q k : ℕ) (hq : 1 < q) :
    ramanujanPacket q k = -∑ m ∈ Finset.Ico 1 (k+1), ramanujanSum q m := by
  induction k with
  | zero => simp [ramanujanPacket, residue]
  | succ k ih =>
    have hd := ramanujanPacket_increment q (k+1) hq (by omega)
    simp only [Nat.add_sub_cancel] at hd
    rw [Finset.sum_Ico_eq_sub _ (by omega)] at ih ⊢
    rw [Finset.sum_range_succ]
    linarith

private theorem sum_prefix_indicator (f : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    (∑ m ∈ Finset.Ico 1 (N+1), if m ≤ k then f m else 0) =
      ∑ m ∈ Finset.Ico 1 (k+1), f m := by
  rw [← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico]
  omega

private theorem finite_prefix_gram (s : Finset ℕ) (a b w : ℕ → ℝ) :
    (∑ k ∈ s, w k *
        ((∑ m ∈ s, if m ≤ k then a m else 0) *
          (∑ n ∈ s, if n ≤ k then b n else 0))) =
      ∑ m ∈ s, ∑ n ∈ s, a m * b n *
        (∑ k ∈ s, if max m n ≤ k then w k else 0) := by
  calc
    _ = ∑ k ∈ s, ∑ m ∈ s, ∑ n ∈ s,
        (if m ≤ k then a m else 0) * (if n ≤ k then b n else 0) * w k := by
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ m ∈ s, ∑ n ∈ s, ∑ k ∈ s,
        (if m ≤ k then a m else 0) * (if n ≤ k then b n else 0) * w k := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hm : m ≤ k <;> by_cases hn : n ≤ k <;>
        simp [hm, hn]

private theorem pareto_kernel_sum (N m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmN : m ≤ N) (hnN : n ≤ N) :
    (∑ k ∈ Finset.Ico 1 (N+1), if max m n ≤ k then positiveWeight k else 0) =
      anchoredGreen N m n := by
  rw [← Finset.sum_filter]
  have hset : (Finset.Ico 1 (N+1)).filter (fun k => max m n ≤ k) =
      Finset.Ico (max m n) (N+1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, max_le_iff]
    omega
  rw [hset, positiveWeight_interval _ _ (by omega) (by omega)]
  simp only [anchoredGreen, Nat.cast_add, Nat.cast_one]

/-- Exact finite Green/Ramanujan Gram identity with the right boundary retained. -/
theorem ramanujanPacket_green_gram (N q r : ℕ) (hq : 1 < q) (hr : 1 < r) :
    (∑ k ∈ Finset.Ico 1 (N+1), positiveWeight k *
      (ramanujanPacket q k * ramanujanPacket r k)) =
    ∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
      ramanujanSum q m * ramanujanSum r n * anchoredGreen N m n := by
  calc
    _ = ∑ k ∈ Finset.Ico 1 (N+1), positiveWeight k *
        ((∑ m ∈ Finset.Ico 1 (N+1), if m ≤ k then ramanujanSum q m else 0) *
         (∑ n ∈ Finset.Ico 1 (N+1), if n ≤ k then ramanujanSum r n else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := by have := (Finset.mem_Ico.mp hk).2; omega
      rw [sum_prefix_indicator _ N k hkN, sum_prefix_indicator _ N k hkN,
        ramanujanPacket_prefix q k hq, ramanujanPacket_prefix r k hr]
      ring
    _ = _ := by
      rw [finite_prefix_gram]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      have hm' := Finset.mem_Ico.mp hm
      have hn' := Finset.mem_Ico.mp hn
      rw [pareto_kernel_sum N m n (by omega) (by omega) (by omega) (by omega)]

/-- The full packet inner product is the finite Green Gram plus the actual tail. -/
theorem ramanujanPacket_green_gram_with_tail (N q r : ℕ) (hq : 1 < q) (hr : 1 < r) :
    paretoInner (ramanujanPacket q) (ramanujanPacket r) =
      (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        ramanujanSum q m * ramanujanSum r n * anchoredGreen N m n) +
      ∑' k, positiveWeight (k+(N+1)) *
        (ramanujanPacket q (k+(N+1)) * ramanujanPacket r (k+(N+1))) := by
  rw [← ramanujanPacket_green_gram N q r hq hr]
  unfold paretoInner
  have h := (ramanujanPacket_product_weighted_summable q r).sum_add_tsum_nat_add (N+1)
  rw [Finset.sum_Ico_eq_sub _ (by omega)]
  simp only [Finset.sum_range_one, positiveWeight, Nat.cast_zero, zero_mul,
    zero_add, div_zero, sub_zero]
  exact h.symm

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The indicator definition is exactly the classical gcd-divisor formula. -/
theorem ramanujanSum_gcd_divisors (q k : ℕ) (hq : 0 < q) :
    ramanujanSum q k =
      ∑ d ∈ (q.gcd k).divisors,
        (d : ℝ) * (ArithmeticFunction.moebius (q / d) : ℝ) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hg0 : q.gcd k ≠ 0 := by
    intro hg
    have hqz : q = 0 := by
      simpa only [hg, zero_dvd_iff] using Nat.gcd_dvd_left q k
    exact hq0 hqz
  have hset : q.divisors.filter (fun d => d ∣ k) = (q.gcd k).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdk⟩
      exact ⟨⟨hdq, hdk⟩, hg0⟩
    · rintro ⟨⟨hdq, hdk⟩, _⟩
      exact ⟨⟨hdq, hq0⟩, hdk⟩
  unfold ramanujanSum
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, hset]
  apply Finset.sum_congr rfl
  intro d _
  ring

end
end RiemannResearch.RH.Pareto
