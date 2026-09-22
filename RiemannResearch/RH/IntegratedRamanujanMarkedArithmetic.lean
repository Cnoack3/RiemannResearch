import RiemannResearch.RH.IntegratedRamanujanInverse
import RiemannResearch.RH.ParetoPacketGreenGram

/-!
# Marked Ramanujan coordinates and exact prime-power Pareto scaling

Source: user-provided Ramanujan / periodic Green / Schur argument, 22 September 2026.
The argument supplies the statements and proof strategy.
Uses the existing full-tail Pareto inner product and the existing legal packets.
The packet convention is B_q = -sum_{k <= n} c_q(k), so B_q(1) = -mu(q).
No new orthonormal basis, uniform bound, limiting saturation, or RH result is asserted.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The actual first-site marking in integrated Ramanujan coordinates. -/
theorem ramanujanPacket_at_one_moebius (q : ℕ) (hq : 1 < q) :
    ramanujanPacket q 1 = -(ArithmeticFunction.moebius q : ℝ) := by
  have hzero : ramanujanPacket q 0 = 0 := by
    simp [ramanujanPacket, residue]
  have hram : ramanujanSum q 1 = (ArithmeticFunction.moebius q : ℝ) := by
    rw [ramanujanSum_gcd_divisors q 1 (by omega)]
    simp
  have h := ramanujanPacket_increment q 1 hq (by norm_num)
  simpa only [Nat.sub_self, hzero, sub_zero, hram] using h

/-- Nonsquarefree conductors have zero direct first-site marking.
This does not assert zero correlations or zero Schur innovation. -/
theorem ramanujanPacket_at_one_eq_zero_of_not_squarefree (q : ℕ)
    (hq : 1 < q) (hns : ¬ Squarefree q) :
    ramanujanPacket q 1 = 0 := by
  rw [ramanujanPacket_at_one_moebius q hq,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
  simp

/-- Every prime-power packet is exactly a scaled floor dilation of its prime seed. -/
theorem ramanujanPacket_prime_pow_succ (p n : ℕ) (hp : p.Prime) :
    ramanujanPacket (p ^ (n + 1)) = dilation (p ^ n) (residue p) := by
  have hpu : ¬ p ∣ 1 := by
    intro h
    exact hp.ne_one (Nat.dvd_one.mp h)
  funext k
  simpa using ramanujanPacket_prime_pow_mul_inverse p 1 n k hp (by norm_num) hpu

/-- Pointwise version retaining both the integer floor and the exact scale. -/
theorem ramanujanPacket_prime_pow_succ_apply (p n k : ℕ) (hp : p.Prime) :
    ramanujanPacket (p ^ (n + 1)) k =
      (p : ℝ) ^ n * residue p (k / p ^ n) := by
  rw [ramanujanPacket_prime_pow_succ p n hp]
  simp only [dilation, Nat.cast_pow]

/-- Higher prime-power packets vanish on an explicitly growing initial block. -/
theorem ramanujanPacket_prime_pow_head_zero (p n k : ℕ) (hp : p.Prime)
    (hk : k < p ^ n) : ramanujanPacket (p ^ (n + 1)) k = 0 := by
  rw [ramanujanPacket_prime_pow_succ_apply p n k hp]
  simp [residue, Nat.div_eq_of_lt hk]

/-- The first nonzero value of a prime-power packet is its dilation scale. -/
theorem ramanujanPacket_prime_pow_first_value (p n : ℕ) (hp : p.Prime) :
    ramanujanPacket (p ^ (n + 1)) (p ^ n) = (p : ℝ) ^ n := by
  rw [ramanujanPacket_prime_pow_succ_apply p n (p ^ n) hp]
  simp [residue, Nat.div_self (pow_pos hp.pos n), Nat.mod_eq_of_lt hp.one_lt]

/-- Full-tail squared norm scales exactly along prime powers. -/
theorem ramanujanPacket_prime_pow_inner_self (p n : ℕ) (hp : p.Prime) :
    paretoInner (ramanujanPacket (p ^ (n + 1)))
        (ramanujanPacket (p ^ (n + 1))) =
      (p : ℝ) ^ n * paretoInner (residue p) (residue p) := by
  rw [ramanujanPacket_prime_pow_succ p n hp]
  simpa only [Nat.cast_pow] using
    paretoInner_dilation (fun k => residue_abs_le p k hp.pos)
      (fun k => residue_abs_le p k hp.pos) (by simp [residue])
      (p ^ n) (pow_pos hp.pos n)

/-- Removing a common prime-power dilation gives an exact Gram correlation law.
The remaining lag correlation is retained, not replaced by orthogonality. -/
theorem ramanujanPacket_prime_pow_inner_lag (p n m : ℕ) (hp : p.Prime) :
    paretoInner (ramanujanPacket (p ^ (n + 1)))
        (ramanujanPacket (p ^ (n + m + 1))) =
      (p : ℝ) ^ n * paretoInner (residue p)
        (ramanujanPacket (p ^ (m + 1))) := by
  rw [ramanujanPacket_prime_pow_succ p n hp,
    ramanujanPacket_prime_pow_succ p (n + m) hp,
    ramanujanPacket_prime_pow_succ p m hp, pow_add, ← dilation_comp]
  simpa only [Nat.cast_pow] using
    paretoInner_dilation (fun k => residue_abs_le p k hp.pos)
      (dilation_abs_le (fun k => residue_abs_le p k hp.pos) (p ^ m))
      (by simp [residue]) (p ^ n) (pow_pos hp.pos n)

end
end RiemannResearch.RH.Pareto
