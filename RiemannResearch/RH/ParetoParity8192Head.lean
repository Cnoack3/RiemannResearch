import RiemannResearch.RH.ParetoParity8192Data
import Mathlib.Tactic

/-! # Physical-site replay for the conductor-8192 trial

The signed difference at site `n` consists of a constant and the jumps at
divisors of `n`. The integer loss rounds upward separately at every site.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192

def coefficientSum : ℤ := ∑ d ∈ support, coeff d

private theorem residue_succ (n d : ℕ) (hd : 2 ≤ d) :
    (((n+1)%d : ℕ) : ℤ) = (n%d : ℕ) + 1 - (if d ∣ n+1 then (d:ℤ) else 0) := by
  have hr := Nat.mod_lt n (show 0 < d by omega)
  have h : (n + 1) % d = (n % d + 1) % d := by
    rw [Nat.add_mod n 1, Nat.mod_eq_of_lt (show 1 < d by omega)]
  by_cases hwrap : n%d + 1 = d
  · have hz : (n+1)%d = 0 := by rw [h,hwrap,Nat.mod_self]
    rw [if_pos (Nat.dvd_of_mod_eq_zero hz),hz]
    omega
  · have hlt : n%d + 1 < d := by omega
    rw [Nat.mod_eq_of_lt hlt] at h
    have hnd : ¬ d ∣ n+1 := fun hdiv => by
      have hz := Nat.mod_eq_zero_of_dvd hdiv
      omega
    rw [if_neg hnd,h]
    push_cast
    ring

theorem residual_succ (n : ℕ) :
    residual (n+1) = residual n - coefficientSum +
      ∑ d ∈ support.filter (fun d => d ∣ n+1), (d:ℤ) * coeff d := by
  have hsum : (∑ d ∈ support, coeff d * (((n+1)%d : ℕ) : ℤ)) =
      (∑ d ∈ support, coeff d * ((n%d : ℕ):ℤ)) + coefficientSum -
        ∑ d ∈ support.filter (fun d => d∣n+1), (d:ℤ)*coeff d := by
    rw [coefficientSum,Finset.sum_filter,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [residue_succ n d (Finset.mem_Icc.mp hd).1]
    by_cases hdiv : d ∣ n+1 <;> simp [hdiv] <;> ring
  unfold residual
  rw [hsum]
  ring

/-- Blocks starting at `length*b+1` partition the physical head exactly. -/
theorem roundedHead_eq_blocks (length blocks : ℕ) :
    roundedHead (length*blocks) =
      ∑ b ∈ Finset.range blocks, ∑ j ∈ Finset.range length,
        roundedUnit (length*b+j+1) := by
  unfold roundedHead
  induction blocks with
  | zero => simp
  | succ b ih => rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
-- The reduction reads all 8191 signed coefficient digits.
theorem coefficientSum_value : coefficientSum = 987443549 :=
  (fastSum_spec coeff).symm.trans (by decide +kernel)

/-- Evaluation using floor quotients only needs conductors at most `n`. -/
theorem residual_floor (n : ℕ) :
    residual n = 10^9 - (n:ℤ)*coefficientSum +
      ∑ d ∈ (Finset.Icc 2 (min n 8192)), (d:ℤ)*coeff d*(n/d : ℕ) := by
  have hset : support.filter (fun d => d≤n) = Finset.Icc 2 (min n 8192) := by
    ext d
    simp only [support,Finset.mem_filter,Finset.mem_Icc,le_min_iff]
    tauto
  have hsum : (∑ d ∈ support, coeff d*((n%d:ℕ):ℤ)) =
      (n:ℤ)*coefficientSum - ∑ d ∈ (Finset.Icc 2 (min n 8192)),
        (d:ℤ)*coeff d*(n/d : ℕ) := by
    rw [← hset,Finset.sum_filter,coefficientSum,Finset.mul_sum,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have he := congrArg (fun x : ℕ => (x:ℤ)) (Nat.mod_add_div n d)
    simp only [Nat.cast_add,Nat.cast_mul] at he
    by_cases h : d ≤ n
    · rw [if_pos h]
      linear_combination (coeff d)*he
    · rw [if_neg h,Nat.mod_eq_of_lt (by omega)]
      ring
  unfold residual
  rw [hsum]
  ring

/-- A kernel-reduced sample uses the same ceiling and signed data as the full replay. -/
theorem roundedHead128_value : roundedHead 128 = 1734335715509953 := by
  unfold roundedHead
  simp_rw [roundedUnit,residual_floor,coefficientSum_value]
  set_option maxRecDepth 100000 in
    set_option maxHeartbeats 100000000 in
      decide +kernel

end RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192
