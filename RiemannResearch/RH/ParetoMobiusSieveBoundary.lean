import RiemannResearch.RH.ParetoFiniteSieveBoundary
import RiemannResearch.RH.PrimeSievePointEnergy

/-!
# The coprime form of the exact finite Pareto sieve boundary

Source: Christian Noack's
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 27, equations (27.2)--(27.3). The sieve is the actual finite Möbius
sum. The positive conductor need not be squarefree, since repeated-factor
terms have zero Möbius coefficient. The cutoff boundary is never discarded.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative
noncomputable section

theorem sieveResidue_eq_finiteSignedResidueTest (P n : ℕ) :
    sieveResidue P n = finiteSignedResidueTest P.divisors (fun d => n * d)
      (fun d => (ArithmeticFunction.moebius d : ℝ) / ((n * d : ℕ) : ℝ)) := by
  funext k
  unfold sieveResidue finiteSignedResidueTest
  apply Finset.sum_congr rfl
  intro d hd
  unfold residueFraction residue
  ring

theorem sieve_scaled_reciprocal_sum (P n : ℕ) :
    (∑ d ∈ P.divisors,
      (ArithmeticFunction.moebius d : ℝ) / ((n * d : ℕ) : ℝ)) =
        sieveReciprocal P / (n : ℝ) := by
  unfold sieveReciprocal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.cast_mul, div_div]
  congr 1
  ring

/-- The exact arithmetic sieve mask at a positive physical coordinate. -/
theorem sieve_scaled_divisibility_mask (P n k : ℕ)
    (hP : 0 < P) (hn : 0 < n) (hk : 0 < k) :
    (∑ d ∈ P.divisors, if n * d ∣ k then
      ((ArithmeticFunction.moebius d : ℝ) / ((n * d : ℕ) : ℝ)) *
        ((n * d : ℕ) : ℝ) else 0) =
      if n ∣ k ∧ Nat.gcd P (k / n) = 1 then 1 else 0 := by
  by_cases hnk : n ∣ k
  · have hrep : n * (k / n) = k := by
      simpa only [Nat.mod_eq_zero_of_dvd hnk, zero_add] using Nat.mod_add_div k n
    have hiff (d : ℕ) : n * d ∣ k ↔ d ∣ k / n := by
      calc
        n * d ∣ k ↔ n * d ∣ n * (k / n) := by rw [hrep]
        _ ↔ d ∣ k / n := Nat.mul_dvd_mul_iff_left hn
    have hkn : 0 < k / n := Nat.div_pos (Nat.le_of_dvd hk hnk) hn
    calc
      _ = ∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : ℝ) * divisorIndicator d (k / n) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hnd : ((n * d : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt (Nat.mul_pos hn (Nat.pos_of_mem_divisors hd))
        rw [div_mul_cancel₀ _ hnd]
        simp [hiff, divisorIndicator, mul_ite]
      _ = if Nat.gcd P (k / n) = 1 then 1 else 0 :=
        sieve_divisorIndicator P (k / n) hP hkn
      _ = _ := by simp [hnk]
  · have hnd (d : ℕ) : ¬ n * d ∣ k := by
      intro hd
      exact hnk (dvd_trans (show n ∣ n * d from ⟨d, rfl⟩) hd)
    simp [hnd, hnk]

/-- The manuscript's finite coprime sieve identity in the full Hilbert
class. The positive multiples `k = n*j` through `K` are selected directly,
so no infinite rearrangement or absolute primitive summability is used. -/
theorem LegalAnnihilator.finite_mobius_sieve_boundary {h : ℕ → ℝ}
    (hh : LegalAnnihilator {n : ℕ | 0 < n} h)
    (P n K : ℕ) (hP : 0 < P) (hn : 0 < n) :
    (∑ k ∈ Finset.range (K + 1),
      if n ∣ k ∧ Nat.gcd P (k / n) = 1 then anchoredSignedTail h k else 0) =
      (sieveReciprocal P / (n : ℝ)) *
        (∑ k ∈ Finset.range (K + 1), anchoredSignedTail h k) -
          paretoFiniteBoundary h (sieveResidue P n) K := by
  have hq (d : ℕ) (hd : d ∈ P.divisors) : 0 < n * d :=
    Nat.mul_pos hn (Nat.pos_of_mem_divisors hd)
  have he := hh.finite_signed_sieve_boundary P.divisors (fun d => n * d)
    (fun d => (ArithmeticFunction.moebius d : ℝ) / ((n * d : ℕ) : ℝ)) hq K
  rw [← sieveResidue_eq_finiteSignedResidueTest,
    sieve_scaled_reciprocal_sum] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [anchoredSignedTail_zero]
  · rw [sieve_scaled_divisibility_mask P n k hP hn (Nat.pos_of_ne_zero hk0)]
    split_ifs <;> simp

end
end RiemannResearch.RH.Pareto
