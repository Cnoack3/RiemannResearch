import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp

/-!
# Exact finite Möbius smoothing identities
Source: user-provided argument
RH_Smoothing_Mixed_Controls_and_Large_Prime_Gains_2026-09-07.md, §3.1.
This module proves finite identities for the genuine residues and Möbius function.
It contains no asymptotic estimate or RH assumption.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Integer-size logarithmic taper, including the genuine Möbius coefficient. -/
def smoothingWeight (N r : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ) *
    (1 - (Real.log (n : ℝ) / Real.log (N : ℝ)) ^ r), by simp⟩

/-- The complete scalar coefficient, including the n = 1 term. -/
def smoothingB (N r : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, smoothingWeight N r n / (n : ℝ)

/-- The legal finite residue approximant. -/
def smoothingSeed (N r k : ℕ) : ℝ :=
  -∑ n ∈ Finset.Ioc 0 N, smoothingWeight N r n / (n : ℝ) * residue n k

/-- Exact summatory logarithmic Möbius divisor convolution. -/
def smoothingTheta (r k : ℕ) : ℝ :=
  -∑ m ∈ Finset.Ioc 0 k, ∑ d ∈ m.divisors,
    (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) ^ r

private theorem residue_floor_real (n k : ℕ) :
    residue n k = (k : ℝ) - (n : ℝ) * (k / n : ℕ) := by
  have h : ((k % n : ℕ) : ℝ) + (n : ℝ) * (k / n : ℕ) = (k : ℝ) := by
    exact_mod_cast Nat.mod_add_div k n
  unfold residue
  linarith

/-- Exact residue-to-divisor-sum formula for any arithmetic coefficient.
The cutoff restriction is used only to remove identically zero floor terms. -/
theorem finite_residue_divisor_identity (a : ArithmeticFunction ℝ) (N k : ℕ)
    (hkN : k ≤ N) :
    -(∑ n ∈ Finset.Ioc 0 N, a n / (n : ℝ) * residue n k) =
      (∑ m ∈ Finset.Ioc 0 k, ∑ d ∈ m.divisors, a d) -
        (k : ℝ) * ∑ n ∈ Finset.Ioc 0 N, a n / (n : ℝ) := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Ioc 0 N) :
      -(a n / (n : ℝ) * residue n k) =
        a n * (k / n : ℕ) - (k : ℝ) * (a n / (n : ℝ)) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Finset.mem_Ioc.mp hn).1)
    rw [residue_floor_real]
    field_simp
    <;> ring
  rw [← Finset.sum_neg_distrib]
  simp_rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  have hcut : (∑ n ∈ Finset.Ioc 0 N, a n * (k / n : ℕ)) =
      ∑ n ∈ Finset.Ioc 0 k, a n * (k / n : ℕ) := by
    symm
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
        le_trans (Finset.mem_Ioc.mp hn).2 hkN⟩
    · intro n hn hnk
      have hlt : k < n := by
        have hnpos := (Finset.mem_Ioc.mp hn).1
        simp only [Finset.mem_Ioc, not_and] at hnk
        exact lt_of_not_ge (hnk hnpos)
      simp [Nat.div_eq_of_lt hlt]
  rw [hcut, ← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact ArithmeticFunction.coe_mul_zeta_apply

private theorem sum_real_moebius_divisors (m : ℕ) :
    (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ)) =
      if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f m)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h

private theorem smoothingWeight_divisor_sum (N r m : ℕ) :
    (∑ d ∈ m.divisors, smoothingWeight N r d) =
      (if m = 1 then 1 else 0) -
        (∑ d ∈ m.divisors,
          (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ) ^ r) /
            Real.log (N : ℝ) ^ r := by
  change (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) *
    (1 - (Real.log (d : ℝ) / Real.log (N : ℝ)) ^ r)) = _
  simp_rw [div_pow, mul_sub, mul_one, ← mul_div_assoc]
  rw [Finset.sum_sub_distrib, sum_real_moebius_divisors, ← Finset.sum_div]

/-- Exact head identity for every logarithmic taper order.
No estimate replaces the scalar B, and every prime-power term is retained. -/
theorem smoothingSeed_head (N r k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    smoothingSeed N r k = 1 + smoothingTheta r k / Real.log (N : ℝ) ^ r -
      (k : ℝ) * smoothingB N r := by
  unfold smoothingSeed smoothingB
  rw [finite_residue_divisor_identity _ N k hkN]
  simp_rw [smoothingWeight_divisor_sum]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  have hone : (∑ m ∈ Finset.Ioc 0 k, (if m = 1 then 1 else 0 : ℝ)) = 1 := by
    have hk1 : 1 ≤ k := hk
    simp [Finset.mem_Ioc, hk1]
  rw [hone]
  unfold smoothingTheta
  ring

/-- The first logarithmic convolution is exactly the Chebyshev prime-power sum. -/
theorem smoothingTheta_one (k : ℕ) :
    smoothingTheta 1 k = ∑ m ∈ Finset.Ioc 0 k, ArithmeticFunction.vonMangoldt m := by
  unfold smoothingTheta
  simp only [pow_one]
  have h (m : ℕ) : (∑ d ∈ m.divisors,
      (ArithmeticFunction.moebius d : ℝ) * Real.log (d : ℝ)) =
        -ArithmeticFunction.vonMangoldt m := by
    exact ArithmeticFunction.sum_moebius_mul_log_eq
  simp_rw [h]
  simp

/-- The linear taper's exact head error, with the genuine von Mangoldt function. -/
theorem smoothingSeed_linear_head_error (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    1 - smoothingSeed N 1 k = (k : ℝ) * smoothingB N 1 -
      (∑ m ∈ Finset.Ioc 0 k, ArithmeticFunction.vonMangoldt m) / Real.log (N : ℝ) := by
  rw [smoothingSeed_head N 1 k hk hkN, smoothingTheta_one, pow_one]
  ring


/-- The entire finite-head energy, retaining both the scalar-defect square
and its signed correlation with the Chebyshev discrepancy. -/
theorem smoothingSeed_linear_head_energy (N : ℕ) :
    (∑ k ∈ Finset.Ioc 0 N,
      (1 - smoothingSeed N 1 k) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) =
      (∑ k ∈ Finset.Ioc 0 N,
        ((k : ℝ) - ∑ m ∈ Finset.Ioc 0 k, ArithmeticFunction.vonMangoldt m) ^ 2 /
          ((k : ℝ) * ((k : ℝ) + 1))) / Real.log (N : ℝ) ^ 2 +
      (2 * (smoothingB N 1 - 1 / Real.log (N : ℝ)) / Real.log (N : ℝ)) *
        (∑ k ∈ Finset.Ioc 0 N,
          ((k : ℝ) - ∑ m ∈ Finset.Ioc 0 k, ArithmeticFunction.vonMangoldt m) /
            ((k : ℝ) + 1)) +
      (smoothingB N 1 - 1 / Real.log (N : ℝ)) ^ 2 *
        ∑ k ∈ Finset.Ioc 0 N, (k : ℝ) / ((k : ℝ) + 1) := by
  rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp : 0 < k := (Finset.mem_Ioc.mp hk).1
  have hkN : k ≤ N := (Finset.mem_Ioc.mp hk).2
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hkp
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [smoothingSeed_linear_head_error N k hkp hkN]
  by_cases hL : Real.log (N : ℝ) = 0
  · simp only [hL, div_zero, sub_zero, zero_mul, mul_zero, zero_add, add_zero]
    field_simp [hk0, hk1]
    <;> ring
  · field_simp [hk0, hk1, hL]
    <;> ring

end
end RiemannResearch.RH.Pareto

/-! Source: user-provided smoothing research note §4.2.
Exact packet coefficient specification for the genuine smoothed residue seed. -/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The full multiples sum specifying a smoothed seed in the packet basis. -/
def smoothingPacketCoefficient (N r q : ℕ) : ℝ :=
  -∑ n ∈ (Finset.Ioc 0 N).filter (fun n => q ∣ n),
    smoothingWeight N r n / (n : ℝ)

private theorem residue_packet_sum_cutoff (N n k : ℕ) (hn : n ∈ Finset.Ioc 0 N) :
    residue n k = ∑ q ∈ Finset.Ioc 0 N,
      if q ∣ n then ramanujanPacket q k else 0 := by
  have hnpos := (Finset.mem_Ioc.mp hn).1
  have hnN := (Finset.mem_Ioc.mp hn).2
  have he : (Finset.Ioc 0 N).filter (fun q => q ∣ n) = n.divisors := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2, ne_of_gt hnpos⟩
    · intro h
      have hqpos := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr h)
      exact ⟨⟨hqpos, le_trans (Nat.le_of_dvd hnpos h.1) hnN⟩, h.1⟩
  rw [← Finset.sum_filter, he]
  exact (ramanujanPacket_divisor_sum n k hnpos).symm

/-- Exact finite residue-to-packet conversion for the smoothed seed, keeping
all conductors and all multiples rather than retaining squarefree indices only. -/
theorem smoothingSeed_packet_expansion (N r k : ℕ) :
    smoothingSeed N r k = ∑ q ∈ Finset.Ioc 0 N,
      smoothingPacketCoefficient N r q * ramanujanPacket q k := by
  unfold smoothingSeed
  have h : (∑ n ∈ Finset.Ioc 0 N,
      smoothingWeight N r n / (n : ℝ) * residue n k) =
      ∑ n ∈ Finset.Ioc 0 N, smoothingWeight N r n / (n : ℝ) *
        ∑ q ∈ Finset.Ioc 0 N, if q ∣ n then ramanujanPacket q k else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [residue_packet_sum_cutoff N n k hn]
  rw [h]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  unfold smoothingPacketCoefficient
  rw [Finset.sum_filter, neg_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases hd : q ∣ n <;> simp [hd]


/-- The smoothed seed itself has only squarefree packet coefficients.
Non-squarefree mixed packets can still enter later optimized corrections. -/
theorem smoothingPacketCoefficient_eq_zero_of_not_squarefree (N r q : ℕ)
    (hq : ¬Squarefree q) : smoothingPacketCoefficient N r q = 0 := by
  unfold smoothingPacketCoefficient
  rw [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro n hn
  have hqn : q ∣ n := (Finset.mem_filter.mp hn).2
  have hnns : ¬Squarefree n := fun hn => hq (Squarefree.squarefree_of_dvd hqn hn)
  simp [smoothingWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnns]

end
end RiemannResearch.RH.Pareto
