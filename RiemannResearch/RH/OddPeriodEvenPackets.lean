import RiemannResearch.RH.OddPeriodBlock
import RiemannResearch.RH.ParetoPrimePackets

/-!
# Dyadic cancellation for even mixed conductors

Doubling shifts the signed block test by exactly one scale. At the first
factor of two of a mixed packet the resulting difference is a single end
block, which converges to zero. Every further factor of two only shifts
the same limit. Parity itself contributes exactly one nonzero scale.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.OddPeriodBlock

private theorem paired_range_sum (H : ℕ) (f : ℕ → ℝ) :
    (∑ u ∈ Finset.range (2*H), f u) =
      ∑ u ∈ Finset.range H, (f (2*u) + f (2*u+1)) := by
  induction H with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    ring

private theorem block_one_dilation (Q : ℕ) (f : ℕ → ℝ) : block Q 1 (dilation 2 f) = 0 := by
  have div₀ (a : ℕ) : 2*a / 2 = a := by omega
  have div₁ (a : ℕ) : (2*a+1) / 2 = a := by omega
  simp [block, dilation, div₀, div₁]

theorem block_double_dilation (Q H : ℕ) (f : ℕ → ℝ) :
    block Q (2*H) (dilation 2 f) = 4 * block Q H f := by
  unfold block
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [paired_range_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have div₀ (a : ℕ) : 2*a / 2 = a := by omega
  have div₁ (a : ℕ) : (2*a+1) / 2 = a := by omega
  have a₀ : 2*(2*H)*(Q+n)+2*H+2*u = 2*(2*H*(Q+n)+H+u) := by ring
  have b₀ : 2*(2*H)*(Q+n)+2*u = 2*(2*H*(Q+n)+u) := by ring
  have a₁ : 2*(2*H)*(Q+n)+2*H+(2*u+1) = 2*(2*H*(Q+n)+H+u)+1 := by ring
  have b₁ : 2*(2*H)*(Q+n)+(2*u+1) = 2*(2*H*(Q+n)+u)+1 := by ring
  simp only [dilation, a₀, b₀, a₁, b₁, div₀, div₁, Nat.cast_ofNat]
  ring

private theorem partial_step (Q K : ℕ) (f : ℕ → ℝ) :
    partialSum Q (K+1) f = partialSum Q K f + (1/4 : ℝ)^(K+1) * block Q (2^K) f := by
  simp only [partialSum, Finset.sum_range_succ]

/-- Every dyadic dilation deletes precisely the first scale of the test. -/
theorem partialSum_succ_dilation (Q K : ℕ) (f : ℕ → ℝ) :
    partialSum Q (K+1) (dilation 2 f) = partialSum Q K f := by
  induction K with
  | zero => simp [partialSum, block_one_dilation]
  | succ K ih =>
    rw [partial_step Q (K+1), ih, partial_step Q K,
      show (2 : ℕ)^(K+1) = 2*2^K by rw [pow_succ, Nat.mul_comm],
      block_double_dilation, pow_succ (1/4 : ℝ) (K+1)]
    ring

private theorem partial_difference (Q K : ℕ) (f g : ℕ → ℝ) :
    partialSum Q K (fun n => f n - g n) = partialSum Q K f - partialSum Q K g := by
  have h (k l : ℕ) : f k - g k - (f l - g l) = (f k - f l) - (g k - g l) := by ring
  simp only [partialSum, block, h, Finset.sum_sub_distrib, mul_sub]

/-- All cancellation is exact except the last single dyadic window. -/
theorem partialSum_succ_dilation_sub (Q K : ℕ) (f : ℕ → ℝ) :
    partialSum Q (K+1) (fun n => dilation 2 f n - f n) =
      -((1/4 : ℝ)^(K+1) * block Q (2^K) f) := by
  rw [partial_difference, partialSum_succ_dilation, partial_step Q K]
  ring

private theorem abs_block_of_bounded (Q H : ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hC : ∀ n, |f n| ≤ C) : |block Q H f| ≤ (Q : ℝ)*H*(2*C) := by
  have h (a b : ℕ) : |f a - f b| ≤ 2*C := by
    calc |f a - f b| ≤ |f a| + |f b| := abs_sub _ _
         _ ≤ 2*C := by linarith [hC a, hC b]
  unfold block
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _n ∈ Finset.range Q, ∑ _u ∈ Finset.range H, 2*C := by
      apply Finset.sum_le_sum
      intro n hn
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => h _ _)
    _ = _ := by simp; ring

theorem partialSum_dilation_sub_tendsto_zero (Q : ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hC : ∀ n, |f n| ≤ C) :
    Tendsto (fun K => partialSum Q K (fun n => dilation 2 f n - f n)) atTop (𝓝 0) := by
  have hpow (K : ℕ) : (1/4 : ℝ)^K * (2:ℝ)^K = (1/2:ℝ)^K := by
    rw [← mul_pow]
    norm_num
  have hb (K : ℕ) :
      |partialSum Q (K+1) (fun n => dilation 2 f n - f n)| ≤
        ((Q : ℝ)*C/2) * (1/2:ℝ)^K := by
    rw [partialSum_succ_dilation_sub, abs_neg, abs_mul, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ (1/4:ℝ)^(K+1))]
    apply (mul_le_mul_of_nonneg_left (abs_block_of_bounded Q (2^K) f C hC) (by positivity)).trans_eq
    push_cast
    rw [pow_succ]
    linear_combination ((Q : ℝ)*C/2) * hpow K
  have hlim : Tendsto (fun K : ℕ => ((Q : ℝ)*C/2) * (1/2:ℝ)^K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul ((Q : ℝ)*C/2)
  have hshift : Tendsto (fun K => partialSum Q (K+1) (fun n => dilation 2 f n - f n))
      atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero, Real.norm_eq_abs] using
      (squeeze_zero (fun K => abs_nonneg _) hb hlim)
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- For integrated parity the first scale contributes Q/4 and all later scales vanish. -/
theorem partialSum_succ_parity (Q K : ℕ) :
    partialSum Q (K+1) (ramanujanPacket 2) = (Q:ℝ)/4 := by
  have htwo : ramanujanPacket 2 = residue 2 := ramanujanPacket_prime_eq_residue 2 Nat.prime_two
  have ho (a : ℕ) : (2*a+1)%2 = 1 := by omega
  have hone : block Q 1 (residue 2) = Q := by simp [block, residue, ho]
  have hrest (j : ℕ) : block Q (2^(j+1)) (residue 2) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro u hu
    have hmod (a b c : ℕ) : (a + 2*b + c)%2 = (a+c)%2 := by omega
    simp only [show (2:ℕ)^(j+1) = 2*2^j by rw [pow_succ, Nat.mul_comm], residue, hmod, sub_self]
  rw [htwo]
  induction K with
  | zero => simp [partialSum, hone, div_eq_mul_inv, mul_comm]
  | succ K ih => rw [partial_step Q (K+1), ih, hrest, mul_zero, add_zero]

private theorem residue_difference_sub_parity (m : ℕ) :
    (fun n => (residue (2*m) n - residue m n) - ramanujanPacket 2 n) =
      (fun n => dilation 2 (residue m) n - residue m n) := by
  funext n
  rw [ramanujanPacket_prime_eq_residue 2 Nat.prime_two, residue_mul_floor]
  ring

/-- The finite dyadic residue payoff is the parity payoff with precisely one
endpoint correction, expressed using a bounded residue. -/
theorem partialSum_succ_dyadicResidue (Q K m : ℕ) :
    partialSum Q (K+1) (fun n => residue (2*m) n - residue m n) =
      (Q:ℝ)/4 - (1/4:ℝ)^(K+1) * block Q (2^K) (residue m) := by
  have h := congrArg (partialSum Q (K+1)) (residue_difference_sub_parity m)
  rw [partial_difference, partialSum_succ_parity, partialSum_succ_dilation_sub] at h
  linarith

theorem partialSum_tendsto_dyadicResidue (Q m : ℕ) (hm : 0 < m) :
    Tendsto (fun K => partialSum Q K (fun n => residue (2*m) n - residue m n))
      atTop (𝓝 ((Q:ℝ)/4)) := by
  have hp : Tendsto (fun K => partialSum Q K (ramanujanPacket 2)) atTop (𝓝 ((Q:ℝ)/4)) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [partialSum_succ_parity] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (Q:ℝ)/4) atTop (𝓝 ((Q:ℝ)/4)))
  have hd := partialSum_dilation_sub_tendsto_zero Q (residue m) (m:ℝ) (fun n => residue_abs_le m n hm)
  rw [← residue_difference_sub_parity m] at hd
  simpa only [partial_difference, sub_add_cancel, zero_add] using hd.add hp

/-- The signed tests annihilate every even mixed conductor in the limit, with
no condition on its odd factors. -/
theorem partialSum_even_mixed_tendsto_zero (Q q : ℕ) (hq : 1 < q) (he : 2 ∣ q)
    (hm : ¬IsPrimePow q) :
    Tendsto (fun K => partialSum Q K (ramanujanPacket q)) atTop (𝓝 0) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    obtain ⟨a, rfl⟩ := he
    have ha : 1 < a := by
      by_contra! hsmall
      have hp : a = 1 := by omega
      exact hm (by simpa only [hp, Nat.mul_one] using Nat.prime_two.isPrimePow)
    by_cases hd : 2 ∣ a
    · have hna : ¬ IsPrimePow a := by
        intro ha'
        obtain ⟨p,k,hp,hk,hpk⟩ := (isPrimePow_nat_iff a).mp ha'
        have hd' : 2 ∣ p^k := hpk ▸ hd
        have hpeq : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
          (Nat.prime_two.dvd_of_dvd_pow hd')
        subst p
        apply hm
        exact (isPrimePow_nat_iff _).mpr ⟨2,k+1,Nat.prime_two,by omega,by rw [pow_succ,hpk]; omega⟩
      have hrec := ih a (by omega) ha hd hna
      have hpacket : ramanujanPacket (2*a) = dilation 2 (ramanujanPacket a) :=
        funext fun k => ramanujanPacket_mul_prime_of_dvd 2 a k Nat.prime_two ha hd
      rw [hpacket]
      apply (tendsto_add_atTop_iff_nat 1).mp
      simpa only [partialSum_succ_dilation] using hrec
    · have hpacket : ramanujanPacket (2*a) =
          fun k => dilation 2 (ramanujanPacket a) k - ramanujanPacket a k :=
        funext fun k => ramanujanPacket_mul_prime_of_not_dvd 2 a k Nat.prime_two ha hd
      rw [hpacket]
      exact partialSum_dilation_sub_tendsto_zero Q _ _ (ramanujanPacket_abs_le a)

end RiemannResearch.RH.Pareto.OddPeriodBlock
