import RiemannResearch.RH.ParetoResidueMean
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


/-!
## Full Green boundary and marked scores for arbitrary finite packet combinations

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`, §5,
equations (5.1)--(5.4). These formulas reuse the finite summation lemmas above.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

/-- Splitting a full mixed inner product preserves its genuine infinite tail. -/
theorem paretoInner_head_add_tail (N : ℕ) {F G : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D) :
    paretoInner F G =
      (∑ k ∈ Finset.Ico 1 (N+1), positiveWeight k * (F k * G k)) +
      ∑' k, positiveWeight (k+(N+1)) * (F (k+(N+1)) * G (k+(N+1))) := by
  unfold paretoInner
  have h := (weighted_summable_of_bounded (bounded_product hF hG)).sum_add_tsum_nat_add (N+1)
  rw [Finset.sum_Ico_eq_sub _ (by omega)]
  simp only [Finset.sum_range_one, positiveWeight, Nat.cast_zero, zero_mul,
    zero_add, div_zero, sub_zero]
  exact h.symm

/-- The finite Green Gram applies to any signed cumulative charges. -/
theorem green_gram_of_prefix (N : ℕ) (F G c d : ℕ → ℝ)
    (hF : ∀ k, F k = -∑ m ∈ Finset.Ico 1 (k+1), c m)
    (hG : ∀ k, G k = -∑ m ∈ Finset.Ico 1 (k+1), d m) :
    (∑ k ∈ Finset.Ico 1 (N+1), positiveWeight k * (F k * G k)) =
      ∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        c m * d n * anchoredGreen N m n := by
  calc
    _ = ∑ k ∈ Finset.Ico 1 (N+1), positiveWeight k *
        ((∑ m ∈ Finset.Ico 1 (N+1), if m ≤ k then c m else 0) *
          (∑ n ∈ Finset.Ico 1 (N+1), if n ≤ k then d n else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := by have := (Finset.mem_Ico.mp hk).2; omega
      rw [sum_prefix_indicator _ N k hkN, sum_prefix_indicator _ N k hkN, hF k, hG k]
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

/-- The complete Green Gram, without a deleted or truncated tail. -/
theorem paretoInner_green_gram_of_prefix (N : ℕ) (F G c d : ℕ → ℝ) {C D : ℝ}
    (hFb : ∀ k, |F k| ≤ C) (hGb : ∀ k, |G k| ≤ D)
    (hF : ∀ k, F k = -∑ m ∈ Finset.Ico 1 (k+1), c m)
    (hG : ∀ k, G k = -∑ m ∈ Finset.Ico 1 (k+1), d m) :
    paretoInner F G =
      (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        c m * d n * anchoredGreen N m n) +
      ∑' k, positiveWeight (k+(N+1)) * (F (k+(N+1)) * G (k+(N+1))) := by
  rw [paretoInner_head_add_tail N hFb hGb, green_gram_of_prefix N F G c d hF hG]

/-- Expanding the anchored kernel exposes the exact negative boundary. -/
theorem green_gram_boundary (N : ℕ) (c d : ℕ → ℝ) :
    (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
      c m * d n * anchoredGreen N m n) =
      (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        c m * d n * (1 / (max m n : ℕ))) -
      (∑ m ∈ Finset.Ico 1 (N+1), c m) *
        (∑ n ∈ Finset.Ico 1 (N+1), d n) / ((N : ℝ)+1) := by
  simp only [anchoredGreen, mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp only [div_eq_mul_inv, one_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- For cumulative charges, the boundary is precisely `-F(N)G(N)/(N+1)`. -/
theorem green_gram_boundary_of_prefix (N : ℕ) (F G c d : ℕ → ℝ)
    (hF : F N = -∑ m ∈ Finset.Ico 1 (N+1), c m)
    (hG : G N = -∑ m ∈ Finset.Ico 1 (N+1), d m) :
    (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
      c m * d n * anchoredGreen N m n) =
      (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        c m * d n * (1 / (max m n : ℕ))) - F N * G N / ((N : ℝ)+1) := by
  rw [green_gram_boundary, hF, hG]
  ring

/-- Finite Green summation for a marked score, with its negative charge sign. -/
theorem green_score_of_prefix (N : ℕ) (F e c : ℕ → ℝ)
    (hF : ∀ k, F k = -∑ m ∈ Finset.Ico 1 (k+1), c m) :
    (∑ k ∈ Finset.Ico 1 (N+1), positiveWeight k * (F k * e k)) =
      -∑ m ∈ Finset.Ico 1 (N+1), c m *
        ∑ k ∈ Finset.Ico m (N+1), positiveWeight k * e k := by
  calc
    _ = -∑ k ∈ Finset.Ico 1 (N+1), ∑ m ∈ Finset.Ico 1 (N+1),
        if m ≤ k then c m * (positiveWeight k * e k) else 0 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := by have := (Finset.mem_Ico.mp hk).2; omega
      have he : (∑ m ∈ Finset.Ico 1 (N+1),
          if m ≤ k then c m * (positiveWeight k * e k) else 0) =
          (∑ m ∈ Finset.Ico 1 (k+1), c m) * (positiveWeight k * e k) := by
        rw [← sum_prefix_indicator c N k hkN, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m _
        by_cases hmk : m ≤ k <;> simp [hmk]
      rw [he, hF k]
      ring
    _ = -∑ m ∈ Finset.Ico 1 (N+1), ∑ k ∈ Finset.Ico 1 (N+1),
        if m ≤ k then c m * (positiveWeight k * e k) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_filter]
      have hset : (Finset.Ico 1 (N+1)).filter (fun k => m ≤ k) =
          Finset.Ico m (N+1) := by
        have hm' := Finset.mem_Ico.mp hm
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      rw [hset, Finset.mul_sum]

/-- Complete residual score: finite Green score plus the full marked tail. -/
theorem paretoInner_green_score_of_prefix (N : ℕ) (F e c : ℕ → ℝ) {C D : ℝ}
    (hFb : ∀ k, |F k| ≤ C) (heb : ∀ k, |e k| ≤ D)
    (hF : ∀ k, F k = -∑ m ∈ Finset.Ico 1 (k+1), c m) :
    paretoInner F e =
      (-∑ m ∈ Finset.Ico 1 (N+1), c m *
        ∑ k ∈ Finset.Ico m (N+1), positiveWeight k * e k) +
      ∑' k, positiveWeight (k+(N+1)) * (F (k+(N+1)) * e (k+(N+1))) := by
  rw [paretoInner_head_add_tail N hFb heb, green_score_of_prefix N F e c hF]

/-- Every finite legal packet combination has exactly its combined Ramanujan charge. -/
theorem packetCombination_prefix (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ q ∈ s, 1 < q) (k : ℕ) :
    (∑ q ∈ s, a q * ramanujanPacket q k) =
      -∑ m ∈ Finset.Ico 1 (k+1), ∑ q ∈ s, a q * ramanujanSum q m := by
  calc
    _ = ∑ q ∈ s, a q * (-∑ m ∈ Finset.Ico 1 (k+1), ramanujanSum q m) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [ramanujanPacket_prefix q k (hs q hq)]
    _ = _ := by
      simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Equation (5.1) for arbitrary signed finite legal combinations. -/
theorem packetCombination_green_gram_with_tail
    (s t : Finset ℕ) (a b : ℕ → ℝ) (N : ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q) :
    paretoInner (fun k => ∑ q ∈ s, a q * ramanujanPacket q k)
      (fun k => ∑ q ∈ t, b q * ramanujanPacket q k) =
      (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        (∑ q ∈ s, a q * ramanujanSum q m) *
          (∑ q ∈ t, b q * ramanujanSum q n) * anchoredGreen N m n) +
      ∑' k, positiveWeight (k+(N+1)) *
        ((∑ q ∈ s, a q * ramanujanPacket q (k+(N+1))) *
          (∑ q ∈ t, b q * ramanujanPacket q (k+(N+1)))) := by
  obtain ⟨C,hC⟩ := packetCombination_bounded s a
  obtain ⟨D,hD⟩ := packetCombination_bounded t b
  exact paretoInner_green_gram_of_prefix N _ _ _ _ hC hD
    (packetCombination_prefix s a hs) (packetCombination_prefix t b ht)

/-- Equation (5.4) includes every old and new conductor in the legal combination. -/
theorem packetCombination_green_score_with_tail
    (s : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) (e : ℕ → ℝ) {D : ℝ}
    (hs : ∀ q ∈ s, 1 < q) (he : ∀ k, |e k| ≤ D) :
    paretoInner (fun k => ∑ q ∈ s, a q * ramanujanPacket q k) e =
      (-∑ m ∈ Finset.Ico 1 (N+1), (∑ q ∈ s, a q * ramanujanSum q m) *
        ∑ k ∈ Finset.Ico m (N+1), positiveWeight k * e k) +
      ∑' k, positiveWeight (k+(N+1)) *
        ((∑ q ∈ s, a q * ramanujanPacket q (k+(N+1))) * e (k+(N+1))) := by
  obtain ⟨C,hC⟩ := packetCombination_bounded s a
  exact paretoInner_green_score_of_prefix N _ _ _ hC he (packetCombination_prefix s a hs)

/-- Centering uses complete means, not truncated head means. -/
theorem ramanujanPacket_green_covariance_with_tail (N q r : ℕ) (hq : 1 < q) (hr : 1 < r) :
    paretoInner (ramanujanPacket q) (ramanujanPacket r) -
      paretoMean (ramanujanPacket q) * paretoMean (ramanujanPacket r) =
      (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        ramanujanSum q m * ramanujanSum r n * anchoredGreen N m n) +
      (∑' k, positiveWeight (k+(N+1)) *
        (ramanujanPacket q (k+(N+1)) * ramanujanPacket r (k+(N+1)))) -
      ArithmeticFunction.vonMangoldt q * ArithmeticFunction.vonMangoldt r := by
  rw [ramanujanPacket_green_gram_with_tail N q r hq hr,
    paretoMean_ramanujanPacket, paretoMean_ramanujanPacket]

/-- For fixed bounded functions the complete signed tail tends to zero.
No uniform bound over changing packet coefficients or conductors is asserted. -/
theorem paretoInner_tail_tendsto_zero {F G : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D) :
    Tendsto (fun N : ℕ => ∑' k, positiveWeight (k+(N+1)) *
      (F (k+(N+1)) * G (k+(N+1)))) atTop (nhds 0) := by
  let f : ℕ → ℝ := fun k => positiveWeight k * (F k * G k)
  have hs : Summable f := weighted_summable_of_bounded (bounded_product hF hG)
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N+1), f k)
      atTop (nhds (∑' k, f k)) :=
    hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑' k, f k)
    atTop (nhds (∑' k, f k))).sub hsum
  have he : (fun N : ℕ => ∑' k, f (k+(N+1))) =
      (fun N : ℕ => (∑' k, f k) - ∑ k ∈ Finset.range (N+1), f k) := by
    funext N
    have h := hs.sum_add_tsum_nat_add (N+1)
    linarith
  change Tendsto (fun N : ℕ => ∑' k, f (k+(N+1))) atTop (nhds 0)
  rw [he]
  simpa only [sub_self] using hlim

/-- The finite signed Green boundary also tends to zero for fixed bounded data. -/
theorem green_boundary_tendsto_zero {F G : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D) :
    Tendsto (fun N : ℕ => F N * G N / ((N : ℝ)+1)) atTop (nhds 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹) atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1))
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have hbound : Tendsto (fun N : ℕ => C*D / ((N : ℝ)+1)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (C*D)
  apply squeeze_zero_norm _ hbound
  intro N
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ)+1)]
  exact div_le_div_of_nonneg_right (bounded_product hF hG N) (by positivity)

end
end RiemannResearch.RH.Pareto
