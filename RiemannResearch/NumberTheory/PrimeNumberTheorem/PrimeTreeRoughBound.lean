/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeRoughReciprocal
import RiemannResearch.RH.QMobiusPrimePacketArithmetic
import Mathlib.Algebra.BigOperators.Associated

/-! # Sharp elementary bound for the reciprocal Möbius sum in a prime semigroup

Source: T. Tao, Bull. Aust. Math. Soc. 81 (2010), 343–349,
doi:10.1017/S0004972709000884, for the bound. At each finite cutoff the
complementary coprimality count and the positive fractional-part summands
have disjoint integer supports (the site one has zero fractional part).
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
open RiemannResearch.RH RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative RiemannResearch.RH.QPrimeSieve

private theorem shift_sum_Icc (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k+1)) = ∑ d ∈ Finset.Icc 1 N, a d := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

private def divisorWeight (P d : ℕ) : ℝ :=
  if d ∣ P then (ArithmeticFunction.moebius d : ℝ) else 0

private theorem divisor_floor_sum (N P : ℕ) (hP : P ≠ 0) :
    (∑ d ∈ Finset.Icc 1 N, divisorWeight P d * ((N/d : ℕ) : ℝ)) =
      coprimeCount P N := by
  classical
  rw [QMobiusPrimePacket.coprimeCount_eq_floor_sum P N hP]
  have hset : (Finset.Icc 1 N).filter (fun d => d ∣ P) =
      P.divisors.filter (fun d => d ≤ N) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, hd⟩, h⟩; exact ⟨⟨h,hP⟩,hd⟩
    · rintro ⟨⟨h,_⟩,hd⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hP),hd⟩,h⟩
  simp only [divisorWeight, ite_mul, zero_mul]
  rw [← Finset.sum_filter, hset]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hn : N < d := by
    by_contra! h
    exact hnot (Finset.mem_filter.mpr ⟨hd,h⟩)
  simp [Nat.div_eq_of_lt hn]

/-- This bound is uniform in both the cutoff and the allowed-prime product. -/
theorem truncated_divisor_reciprocal_bound (N P : ℕ) (hP : P ≠ 0) :
    |∑ d ∈ Finset.Icc 1 N, divisorWeight P d / (d : ℝ)| ≤ 1 := by
  classical
  by_cases hn : N = 0
  · simp [hn]
  have hnR : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  let c (d : ℕ) : ℝ := if d.Coprime P then 1 else 0
  have hc : (∑ d ∈ Finset.Icc 1 N, c d) = coprimeCount P N := (shift_sum_Icc c N).symm
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      (N : ℝ) * (divisorWeight P d / (d : ℝ)) =
      divisorWeight P d * ((N/d : ℕ) : ℝ) + divisorWeight P d * residueFraction d N := by
    rw [residueFraction_eq_div_sub_floor d N (Finset.mem_Icc.mp hd).1]
    ring
  have he : (N : ℝ) * (∑ d ∈ Finset.Icc 1 N, divisorWeight P d / (d : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N, (c d + divisorWeight P d * residueFraction d N) := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
      Finset.sum_add_distrib, divisor_floor_sum N P hP, hc]
  have bound (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      |c d + divisorWeight P d * residueFraction d N| ≤ 1 := by
    by_cases he : d = 1
    · simp [he, c, residueFraction, Nat.mod_one]
    by_cases hdiv : d ∣ P
    · have hcop : ¬d.Coprime P := fun h =>
        he ((Nat.gcd_eq_left_iff_dvd.mpr hdiv).symm.trans h)
      have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
      have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hr : 0 ≤ residueFraction d N := by
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hl : residueFraction d N ≤ 1 := by
        apply (div_le_one (by exact_mod_cast hd0 : 0 < (d : ℝ))).mpr
        exact_mod_cast (Nat.mod_lt N hd0).le
      simp only [c, if_neg hcop, divisorWeight, if_pos hdiv, zero_add, abs_mul, abs_of_nonneg hr]
      exact (mul_le_mul_of_nonneg_right hμ hr).trans (by simpa using hl)
    · simp only [divisorWeight, if_neg hdiv, zero_mul, add_zero, c]
      split <;> norm_num
  have hab : |(N : ℝ) * (∑ d ∈ Finset.Icc 1 N, divisorWeight P d / (d : ℝ))| ≤ N := by
    rw [he]
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N, |c d + divisorWeight P d * residueFraction d N| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 N, (1 : ℝ) := Finset.sum_le_sum bound
      _ = _ := by simp
  rw [abs_mul, abs_of_pos hnR] at hab
  exact (le_of_mul_le_mul_left (by simpa using hab :
    (N : ℝ) * |∑ d ∈ Finset.Icc 1 N, divisorWeight P d / (d : ℝ)| ≤ (N : ℝ) * 1) hnR)

/-- The sharp Tao bound for the finite-prime deletions occurring in a
fixed tree cone. -/
theorem roughReciprocal_abs_le_one (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (N : ℕ) :
    |roughReciprocal B N| ≤ 1 := by
  classical
  let A := (Finset.Icc 2 N).filter (fun p => p.Prime ∧ p ∉ B)
  let P := ∏ p ∈ A, p
  have hA (q : ℕ) (hq : q ∈ A) : q.Prime ∧ q ∉ B := (Finset.mem_filter.mp hq).2
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hA p hp).1.ne_zero
  have ht (d : ℕ) (hd : d ∈ Finset.Icc 1 N) : coefficient B d = divisorWeight P d := by
    by_cases hs : Squarefree d
    · have he : d ∣ P ↔ ∀ q ∈ B, ¬q ∣ d := by
        constructor
        · intro hdP q hq hqd
          obtain ⟨p,hp,hqp⟩ := ((hB q hq).prime.dvd_finsetProd_iff id).mp (hqd.trans hdP)
          have heq : q = p := (Nat.prime_dvd_prime_iff_eq (hB q hq) (hA p hp).1).mp hqp
          exact (hA p hp).2 (heq ▸ hq)
        · intro h
          rw [← Nat.prod_primeFactors_of_squarefree hs]
          apply Finset.prod_dvd_prod_of_subset
          intro p hp
          have hp' := Nat.prime_of_mem_primeFactors hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp'.two_le,
            (Nat.le_of_mem_primeFactors hp).trans (Finset.mem_Icc.mp hd).2⟩,
            hp', fun hB' => h p hB' (Nat.dvd_of_mem_primeFactors hp)⟩
      simp only [coefficient, divisorWeight, he]
    · simp [coefficient, divisorWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  apply le_trans _ (truncated_divisor_reciprocal_bound N P hP)
  apply le_of_eq
  congr 1
  unfold roughReciprocal
  rw [shift_sum_Icc (fun d : ℕ => coefficient B d / (d : ℝ)) N]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ht d hd]

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
