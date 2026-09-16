import RiemannResearch.RH.PrimePowerCriticalEnergy
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Nth

/-!
# Complete increasing prime-power enumeration

Source: the user-provided V_Zeta_Vector_Spaces_Research_2026-09-16.md,
Sections 12-18. This supplies the previously open global enumeration and
support-completeness provider using Mathlib's actual von Mangoldt function.
The factor-two successor bound uses powers of two, without prime-gap inputs.
`enumerated_cumulative_eq_psi` identifies each endpoint cumulative value
with Mathlib's Chebyshev psi; no RH hypothesis is used.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.LinearAlgebra.CumulativeCellEnergy

namespace RiemannResearch.RH.PrimePowerCriticalEnergy

def primePowerEnumeration : ℕ → ℕ :=
  Nat.nth (fun n => ArithmeticFunction.vonMangoldt n ≠ 0)

theorem vonMangoldt_support_infinite :
    {n : ℕ | ArithmeticFunction.vonMangoldt n ≠ 0}.Infinite := by
  apply Nat.infinite_setOfPred_prime.mono
  intro n hn
  change ArithmeticFunction.vonMangoldt n ≠ 0
  rw [ArithmeticFunction.vonMangoldt_apply_prime hn]
  exact ne_of_gt (Real.log_pos (by exact_mod_cast hn.one_lt))

theorem primePowerEnumeration_strictMono : StrictMono primePowerEnumeration :=
  Nat.nth_strictMono vonMangoldt_support_infinite

theorem primePowerEnumeration_mem (n : ℕ) :
    ArithmeticFunction.vonMangoldt (primePowerEnumeration n) ≠ 0 :=
  Nat.nth_mem_of_infinite vonMangoldt_support_infinite n

theorem primePowerEnumeration_isPrimePow (n : ℕ) :
    IsPrimePow (primePowerEnumeration n) :=
  ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (primePowerEnumeration_mem n)

theorem primePowerEnumeration_pos (n : ℕ) : 0 < primePowerEnumeration n := by
  have h := primePowerEnumeration_mem n
  by_contra hn
  have hz : primePowerEnumeration n = 0 := by omega
  simp [hz] at h

theorem primePowerEnumeration_complete (n : ℕ) :
    CompleteThrough primePowerEnumeration n := by
  intro k hk hne
  obtain ⟨i, hi⟩ := Nat.subset_range_nth (p := fun k => ArithmeticFunction.vonMangoldt k ≠ 0) hne
  refine ⟨i, ?_, hi⟩
  apply Finset.mem_range.mpr
  have hki : primePowerEnumeration i ≤ primePowerEnumeration n := by
    change Nat.nth (fun k => ArithmeticFunction.vonMangoldt k ≠ 0) i ≤ _
    rw [hi]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  exact Nat.lt_succ_of_le (primePowerEnumeration_strictMono.le_iff_le.mp hki)

theorem primePowerEnumeration_zero : primePowerEnumeration 0 = 2 := by
  have htwo : ArithmeticFunction.vonMangoldt 2 ≠ 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact ne_of_gt (Real.log_pos (by norm_num))
  obtain ⟨i, hi⟩ := Nat.subset_range_nth (p := fun k => ArithmeticFunction.vonMangoldt k ≠ 0) htwo
  have hle := primePowerEnumeration_strictMono.monotone (Nat.zero_le i)
  change primePowerEnumeration 0 ≤ Nat.nth (fun k => ArithmeticFunction.vonMangoldt k ≠ 0) i at hle
  rw [hi] at hle
  have hpos := primePowerEnumeration_pos 0
  have hne := primePowerEnumeration_mem 0
  have hnotone : primePowerEnumeration 0 ≠ 1 := by
    intro he
    simp [he] at hne
  omega

theorem sum_vonMangoldt_range_eq_psi (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi (n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  congr 1
  ext k
  simp only [Finset.mem_range, Finset.mem_Icc]
  omega

theorem actualCumulative_le_psi (q : ℕ → ℕ) (hq : StrictMono q) (n : ℕ) :
    cumulative (actualJump q) (n + 1) ≤ Chebyshev.psi (q n : ℝ) := by
  classical
  have hsubset : (Finset.range (n + 1)).image q ⊆ Finset.range (q n + 1) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (hq.monotone (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  rw [← sum_vonMangoldt_range_eq_psi]
  calc
    cumulative (actualJump q) (n + 1) =
        ∑ k ∈ (Finset.range (n + 1)).image q, ArithmeticFunction.vonMangoldt k := by
      rw [Finset.sum_image]
      · rfl
      · intro i hi j hj hij
        exact hq.injective hij
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun k hk hnot => ArithmeticFunction.vonMangoldt_nonneg)

theorem enumerated_cumulative_eq_psi (n : ℕ) :
    cumulative (actualJump primePowerEnumeration) (n + 1) =
      Chebyshev.psi (primePowerEnumeration n : ℝ) := by
  rw [actualCumulative_eq_chebyshev _ primePowerEnumeration_strictMono n
    (primePowerEnumeration_complete n), sum_vonMangoldt_range_eq_psi]


theorem primePowerEnumeration_succ_le_twice (i : ℕ) :
    primePowerEnumeration (i + 1) ≤ 2 * primePowerEnumeration i := by
  classical
  have hex : ∃ n : ℕ, primePowerEnumeration i < 2 ^ n :=
    ⟨primePowerEnumeration i, Nat.lt_two_pow_self⟩
  let n := Nat.find hex
  have hn : primePowerEnumeration i < 2 ^ n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro he
    rw [he] at hn
    have hp := primePowerEnumeration_pos i
    norm_num at hn
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hprev : 2 ^ k ≤ primePowerEnumeration i := by
    apply Nat.le_of_not_gt
    exact Nat.find_min hex (by omega : k < n)
  have hpow : 2 ^ n ≤ 2 * primePowerEnumeration i := by
    rw [hk, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 hprev
  have hmem : ArithmeticFunction.vonMangoldt (2 ^ n) ≠ 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hn0,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact ne_of_gt (Real.log_pos (by norm_num))
  obtain ⟨j, hj⟩ := Nat.subset_range_nth
    (p := fun k => ArithmeticFunction.vonMangoldt k ≠ 0) hmem
  have hij : i < j := primePowerEnumeration_strictMono.lt_iff_lt.mp (by
    change primePowerEnumeration i < Nat.nth (fun k => ArithmeticFunction.vonMangoldt k ≠ 0) j
    rw [hj]
    exact hn)
  have hle := primePowerEnumeration_strictMono.monotone (Nat.succ_le_of_lt hij)
  change primePowerEnumeration (i + 1) ≤ Nat.nth (fun k => ArithmeticFunction.vonMangoldt k ≠ 0) j at hle
  rw [hj] at hle
  exact hle.trans hpow


end RiemannResearch.RH.PrimePowerCriticalEnergy
