import RiemannResearch.Analysis.LaguerreMomentTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Linarith

/-!
# Orthogonality of the actual Laguerre polynomials

The ordinary Laguerre normalization is that of NIST DLMF §18.3.
The proof reduces the integral to Gamma factorial moments and the finite
difference formula for binomial coefficients. This supplies the exact
orthogonality used by the Pareto Parseval theorem.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis

theorem continuous_laguerreValue (n : ℕ) : Continuous (laguerreValue n) := by
  unfold laguerreValue
  exact continuous_finsetSum _ fun j hj => continuous_const.mul (continuous_id.pow j)

theorem integrableOn_pow_mul_exp_neg (j : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ j * Real.exp (-t)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa [Real.rpow_natCast, mul_comm] using
    (Real.GammaIntegral_convergent (s := (j : ℝ) + 1) (by positivity))

theorem integral_Ici_pow_mul_exp_neg (j : ℕ) :
    (∫ t : ℝ in Ici 0, t ^ j * Real.exp (-t)) = (j.factorial : ℝ) := by
  rw [integral_Ici_eq_integral_Ioi]
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using
    (Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (j : ℝ) + 1) (r := 1) (by positivity) (by norm_num))

private theorem alternating_choose_shift_int {n k : ℕ} (h : k ≤ n) (a : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ j * (n.choose j : ℤ) * ((a + j).choose k : ℤ)) =
      if n = k then (-1 : ℤ) ^ n else 0 := by
  have hd : (fwdDiff (1 : ℕ))^[n] (fun x : ℕ => (x.choose k : ℤ)) a =
      if n = k then 1 else 0 := by
    rcases lt_or_eq_of_le h with hlt | rfl
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      simp_rw [hlt.ne', if_false,
        (by omega : k + d + 1 = d + 1 + k), Function.iterate_add_apply,
        (show k + 0 = k by omega) ▸ fwdDiff_iter_choose 0 k,
        Nat.choose_zero_right, Nat.cast_one, Function.iterate_succ_apply,
        fwdDiff_const, fwdDiff_iter_eq_sum_shift, smul_zero, Finset.sum_const_zero]
      simp
    · simpa using congrFun (fwdDiff_iter_choose 0 k) a
  rw [fwdDiff_iter_eq_sum_shift] at hd
  simp only [nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_id, Nat.cast_id] at hd
  have hs := congrArg (fun z : ℤ => (-1) ^ n * z) hd
  rw [Finset.mul_sum] at hs
  have heq : (∑ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ n * (((-1 : ℤ) ^ (n - j) * (n.choose j : ℤ)) *
        ((a + j).choose k : ℤ))) =
      ∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * (n.choose j : ℤ) * ((a + j).choose k : ℤ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hp : (-1 : ℤ) ^ n * (-1 : ℤ) ^ (n - j) = (-1 : ℤ) ^ j := by
      rw [← pow_add, show n + (n - j) = 2 * (n - j) + j by omega,
        pow_add, pow_mul]
      simp
    calc
      _ = ((-1 : ℤ) ^ n * (-1 : ℤ) ^ (n - j)) *
          (n.choose j : ℤ) * ((a + j).choose k : ℤ) := by ring
      _ = _ := by rw [hp]
  rw [heq] at hs
  simpa only [mul_ite, mul_one, mul_zero] using hs

private theorem alternating_choose_shift {n k : ℕ} (h : k ≤ n) (a : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ j * (n.choose j : ℝ) * ((a + j).choose k : ℝ)) =
      if n = k then (-1 : ℝ) ^ n else 0 := by
  exact_mod_cast alternating_choose_shift_int h a

private theorem factorial_ratio (j k : ℕ) :
    ((j + k).factorial : ℝ) / (j.factorial : ℝ) =
      (k.factorial : ℝ) * ((k + j).choose k : ℝ) := by
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hc : ((k + j).choose k : ℝ) * (k.factorial : ℝ) *
      (j.factorial : ℝ) = ((j + k).factorial : ℝ) := by
    exact_mod_cast (by simpa [Nat.add_comm] using
      (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k j)))
  apply (div_eq_iff hj).2
  nlinarith [hc]

theorem integrableOn_laguerre_mul_pow_mul_exp_neg (n k : ℕ) :
    IntegrableOn (fun t : ℝ => laguerreValue n t * t ^ k * Real.exp (-t))
      (Ici 0) := by
  have heq : (fun t : ℝ => laguerreValue n t * t ^ k * Real.exp (-t)) =
      fun t => ∑ j ∈ Finset.range (n + 1),
        laguerreCoefficient n j * (t ^ (j + k) * Real.exp (-t)) := by
    funext t
    simp only [laguerreValue, Finset.sum_mul, pow_add]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  exact integrable_finsetSum _ fun j hj =>
    (integrableOn_pow_mul_exp_neg (j + k)).const_mul _

/-- All lower polynomial moments vanish; the leading moment is signed factorial. -/
theorem integral_Ici_laguerre_mul_pow_mul_exp_neg (n k : ℕ) (h : k ≤ n) :
    (∫ t : ℝ in Ici 0, laguerreValue n t * t ^ k * Real.exp (-t)) =
      if n = k then (-1 : ℝ) ^ n * (k.factorial : ℝ) else 0 := by
  have heq : (fun t : ℝ => laguerreValue n t * t ^ k * Real.exp (-t)) =
      fun t => ∑ j ∈ Finset.range (n + 1),
        laguerreCoefficient n j * (t ^ (j + k) * Real.exp (-t)) := by
    funext t
    simp only [laguerreValue, Finset.sum_mul, pow_add]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, integral_finsetSum]
  · simp_rw [integral_const_mul, integral_Ici_pow_mul_exp_neg]
    have heq' : (∑ j ∈ Finset.range (n + 1),
        laguerreCoefficient n j * ((j + k).factorial : ℝ)) =
        (k.factorial : ℝ) * ∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ j * (n.choose j : ℝ) * ((k + j).choose k : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      unfold laguerreCoefficient
      calc
        _ = ((-1 : ℝ) ^ j * (n.choose j : ℝ)) *
            (((j + k).factorial : ℝ) / (j.factorial : ℝ)) := by ring
        _ = _ := by rw [factorial_ratio]; ring
    rw [heq', alternating_choose_shift h]
    split_ifs <;> ring
  · intro j hj
    exact (integrableOn_pow_mul_exp_neg (j + k)).const_mul _

theorem integrableOn_laguerre_mul_laguerre_mul_exp_neg (m n : ℕ) :
    IntegrableOn (fun t : ℝ =>
      laguerreValue m t * laguerreValue n t * Real.exp (-t)) (Ici 0) := by
  have heq : (fun t : ℝ => laguerreValue m t * laguerreValue n t * Real.exp (-t)) =
      fun t => ∑ j ∈ Finset.range (n + 1),
        laguerreCoefficient n j * (laguerreValue m t * t ^ j * Real.exp (-t)) := by
    funext t
    change laguerreValue m t * (∑ j ∈ Finset.range (n + 1),
      laguerreCoefficient n j * t ^ j) * Real.exp (-t) = _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  exact integrable_finsetSum _ fun j hj =>
    (integrableOn_laguerre_mul_pow_mul_exp_neg m j).const_mul _

private theorem integral_Ici_laguerre_mul_laguerre_mul_exp_neg_of_le
    (m n : ℕ) (h : n ≤ m) :
    (∫ t : ℝ in Ici 0,
      laguerreValue m t * laguerreValue n t * Real.exp (-t)) =
      if m = n then 1 else 0 := by
  have heq : (fun t : ℝ => laguerreValue m t * laguerreValue n t * Real.exp (-t)) =
      fun t => ∑ j ∈ Finset.range (n + 1),
        laguerreCoefficient n j * (laguerreValue m t * t ^ j * Real.exp (-t)) := by
    funext t
    change laguerreValue m t * (∑ j ∈ Finset.range (n + 1),
      laguerreCoefficient n j * t ^ j) * Real.exp (-t) = _
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, integral_finsetSum]
  · simp_rw [integral_const_mul]
    by_cases hmn : m = n
    · subst m
      rw [if_pos rfl, Finset.sum_eq_single n]
      · rw [integral_Ici_laguerre_mul_pow_mul_exp_neg n n le_rfl, if_pos rfl,
          laguerreCoefficient_diagonal]
        have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        have hp : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm n 2, pow_mul]; simp
        field_simp
        nlinarith [hp]
      · intro j hj hjn
        rw [integral_Ici_laguerre_mul_pow_mul_exp_neg n j
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), if_neg (Ne.symm hjn), mul_zero]
      · simp
    · rw [if_neg hmn]
      apply Finset.sum_eq_zero
      intro j hj
      have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [integral_Ici_laguerre_mul_pow_mul_exp_neg m j (hjn.trans h),
        if_neg (by omega : m ≠ j), mul_zero]
  · intro j hj
    exact (integrableOn_laguerre_mul_pow_mul_exp_neg m j).const_mul _

/-- Exact orthonormality for Lebesgue measure with exponential weight. -/
theorem integral_Ici_laguerre_mul_laguerre_mul_exp_neg (m n : ℕ) :
    (∫ t : ℝ in Ici 0,
      laguerreValue m t * laguerreValue n t * Real.exp (-t)) =
      if m = n then 1 else 0 := by
  rcases le_total n m with h | h
  · exact integral_Ici_laguerre_mul_laguerre_mul_exp_neg_of_le m n h
  · have heq : (fun t : ℝ => laguerreValue m t * laguerreValue n t * Real.exp (-t)) =
        fun t => laguerreValue n t * laguerreValue m t * Real.exp (-t) := by
      funext t
      ring
    rw [heq, integral_Ici_laguerre_mul_laguerre_mul_exp_neg_of_le n m h]
    simp only [eq_comm]

theorem integrableOn_laguerre_sq_mul_exp_neg (n : ℕ) :
    IntegrableOn (fun t : ℝ => laguerreValue n t ^ 2 * Real.exp (-t)) (Ici 0) := by
  simpa only [pow_two] using integrableOn_laguerre_mul_laguerre_mul_exp_neg n n

theorem integral_Ici_laguerre_sq_mul_exp_neg (n : ℕ) :
    (∫ t : ℝ in Ici 0, laguerreValue n t ^ 2 * Real.exp (-t)) = 1 := by
  simpa [pow_two] using integral_Ici_laguerre_mul_laguerre_mul_exp_neg n n

end RiemannResearch.Analysis
