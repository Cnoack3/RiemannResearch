/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Floor-defined CRT carries

Source: the CRT carry identities developed with Christian Noack in
`CRT_Carries_and_Squarefree_Residual_Exhaustion`, 19 October 2026,
sections 2, 3 and 5. The source supports the mathematical statements and
proof strategy. The constructions here are pointwise arithmetic; no
Hilbert projection or asymptotic exhaustion hypothesis is assumed.
-/

noncomputable section

namespace RiemannResearch.RH.CRTCarryArithmetic

open ArithmeticCumulative

/-- The actual integer carry, defined by a floor rather than by a formal
linear combination of Hilbert vectors. -/
def carry (p q : ℕ) (a b : ℤ) (n : ℕ) : ℤ :=
  ⌊(a : ℝ) * residueFraction p n + (b : ℝ) * residueFraction q n⌋

/-- The integral quotient expression for a valid CRT carry. -/
def quotientCarry (p q : ℕ) (a b t : ℤ) (n : ℕ) : ℤ :=
  t * (n : ℤ) - a * ((n / p : ℕ) : ℤ) -
    b * ((n / q : ℕ) : ℤ) + ((n / (p * q) : ℕ) : ℤ)

theorem residueFraction_nonneg (d n : ℕ) : 0 ≤ residueFraction d n := by
  unfold residueFraction
  positivity

theorem residueFraction_lt_one (d n : ℕ) (hd : 0 < d) :
    residueFraction d n < 1 := by
  unfold residueFraction
  apply (div_lt_one (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  exact_mod_cast Nat.mod_lt n hd

/-- The harmless conductor zero is included, since division by zero is
totalized to zero in the existing residue definition. -/
theorem residueFraction_abs_le_one (d n : ℕ) : |residueFraction d n| ≤ 1 := by
  by_cases hd : d = 0
  · simp [residueFraction, hd]
  · rw [abs_of_nonneg (residueFraction_nonneg d n)]
    exact le_of_lt (residueFraction_lt_one d n (Nat.pos_of_ne_zero hd))

/-- A uniform bound for the actual floor carry, without any CRT condition. -/
theorem carry_abs_le (p q : ℕ) (a b : ℤ) (n : ℕ) :
    |(carry p q a b n : ℝ)| ≤ |(a : ℝ)| + |(b : ℝ)| + 1 := by
  let x : ℝ := (a : ℝ) * residueFraction p n + (b : ℝ) * residueFraction q n
  have hx : |x| ≤ |(a : ℝ)| + |(b : ℝ)| := by
    calc
      |x| ≤ |(a : ℝ) * residueFraction p n| +
          |(b : ℝ) * residueFraction q n| := abs_add_le _ _
      _ = |(a : ℝ)| * |residueFraction p n| +
          |(b : ℝ)| * |residueFraction q n| := by rw [abs_mul, abs_mul]
      _ ≤ |(a : ℝ)| * 1 + |(b : ℝ)| * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left (residueFraction_abs_le_one p n) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (residueFraction_abs_le_one q n) (abs_nonneg _))
      _ = |(a : ℝ)| + |(b : ℝ)| := by ring
  have hf : (⌊x⌋ : ℝ) ≤ x ∧ x < (⌊x⌋ : ℝ) + 1 := Int.floor_eq_iff.mp rfl
  obtain ⟨hlo, hhi⟩ := hf
  change |(⌊x⌋ : ℝ)| ≤ _
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem residueFraction_eq_div_sub_quotient (d n : ℕ) (hd : 0 < d) :
    residueFraction d n = (n : ℝ) / (d : ℝ) - ((n / d : ℕ) : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hn : (d : ℝ) * ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.div_add_mod n d
  unfold residueFraction
  field_simp [hdR]
  nlinarith

theorem floor_div_eq_nat_quotient (d n : ℕ) (hd : 0 < d) :
    ⌊(n : ℝ) / (d : ℝ)⌋ = ((n / d : ℕ) : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have h := residueFraction_eq_div_sub_quotient d n hd
  have hnon := residueFraction_nonneg d n
  have hlt := residueFraction_lt_one d n hd
  simp only [Int.cast_natCast]
  constructor <;> linarith

/-- The residue combination differs from the composite residue by the
explicit integer quotient expression. Integrality of `a,b,t` is essential. -/
theorem combination_eq_residue_add_quotient
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    (a : ℝ) * residueFraction p n + (b : ℝ) * residueFraction q n =
      residueFraction (p * q) n + (quotientCarry p q a b t n : ℝ) := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hqR : (q : ℝ) ≠ 0 := by positivity
  rw [residueFraction_eq_div_sub_quotient p n hp,
    residueFraction_eq_div_sub_quotient q n hq,
    residueFraction_eq_div_sub_quotient (p * q) n (Nat.mul_pos hp hq)]
  simp only [quotientCarry, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul]
  field_simp [hpR, hqR]
  linear_combination (n : ℝ) * hcrt

/-- The floor in the definition equals an explicit integer expression. -/
theorem carry_eq_quotientCarry
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    carry p q a b n = quotientCarry p q a b t n := by
  unfold carry
  apply Int.floor_eq_iff.mpr
  rw [combination_eq_residue_add_quotient p q a b t n hp hq hcrt]
  have hnon := residueFraction_nonneg (p * q) n
  have hlt := residueFraction_lt_one (p * q) n (Nat.mul_pos hp hq)
  constructor <;> linarith

/-- Exact real decomposition for the actual floor-defined carry. -/
theorem real_decomposition
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    (carry p q a b n : ℝ) =
      (a : ℝ) * residueFraction p n + (b : ℝ) * residueFraction q n -
        residueFraction (p * q) n := by
  rw [carry_eq_quotientCarry p q a b t n hp hq hcrt]
  have h := combination_eq_residue_add_quotient p q a b t n hp hq hcrt
  linarith

theorem real_quotient_formula
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    (carry p q a b n : ℝ) =
      (t : ℝ) * (n : ℝ) - (a : ℝ) * ((n / p : ℕ) : ℝ) -
        (b : ℝ) * ((n / q : ℕ) : ℝ) + ((n / (p * q) : ℕ) : ℝ) := by
  rw [carry_eq_quotientCarry p q a b t n hp hq hcrt]
  simp only [quotientCarry, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]

/-- The quotient formula stated directly with ordinary real floors. -/
theorem carry_floor_formula
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    carry p q a b n = t * (n : ℤ) - a * ⌊(n : ℝ) / (p : ℝ)⌋ -
      b * ⌊(n : ℝ) / (q : ℝ)⌋ + ⌊(n : ℝ) / ((p * q : ℕ) : ℝ)⌋ := by
  rw [floor_div_eq_nat_quotient p n hp, floor_div_eq_nat_quotient q n hq,
    floor_div_eq_nat_quotient (p * q) n (Nat.mul_pos hp hq)]
  exact carry_eq_quotientCarry p q a b t n hp hq hcrt

theorem residue_eq_combination_sub_carry
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    residueFraction (p * q) n =
      (a : ℝ) * residueFraction p n + (b : ℝ) * residueFraction q n -
        (carry p q a b n : ℝ) := by
  rw [real_decomposition p q a b t n hp hq hcrt]
  ring

theorem carry_swap (p q : ℕ) (a b : ℤ) (n : ℕ) :
    carry p q a b n = carry q p b a n := by
  unfold carry
  rw [add_comm]

/-- Arbitrary valid choices are handled, without first having to classify
all solutions as shifts by multiples of the conductors. -/
theorem real_change_of_valid_representatives
    (p q : ℕ) (a b t a' b' t' : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ))
    (hcrt' : (a' : ℝ) * (q : ℝ) + (b' : ℝ) * (p : ℝ) =
      1 + (t' : ℝ) * (p : ℝ) * (q : ℝ)) :
    (carry p q a' b' n : ℝ) - (carry p q a b n : ℝ) =
      ((a' : ℝ) - (a : ℝ)) * residueFraction p n +
        ((b' : ℝ) - (b : ℝ)) * residueFraction q n := by
  rw [real_decomposition p q a b t n hp hq hcrt,
    real_decomposition p q a' b' t' n hp hq hcrt']
  ring

theorem coefficients_shift (p q : ℕ) (a b t u v : ℤ)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    ((a + u * (p : ℤ) : ℤ) : ℝ) * (q : ℝ) +
      ((b + v * (q : ℤ) : ℤ) : ℝ) * (p : ℝ) =
        1 + ((t + u + v : ℤ) : ℝ) * (p : ℝ) * (q : ℝ) := by
  push_cast
  linear_combination hcrt

theorem carry_shift
    (p q : ℕ) (a b t u v : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    carry p q (a + u * (p : ℤ)) (b + v * (q : ℤ)) n =
      carry p q a b n + u * ((n % p : ℕ) : ℤ) + v * ((n % q : ℕ) : ℤ) := by
  rw [carry_eq_quotientCarry p q (a + u * (p : ℤ)) (b + v * (q : ℤ))
      (t + u + v) n hp hq (coefficients_shift p q a b t u v hcrt),
    carry_eq_quotientCarry p q a b t n hp hq hcrt]
  have hpZ : (p : ℤ) * ((n / p : ℕ) : ℤ) + ((n % p : ℕ) : ℤ) = (n : ℤ) := by
    exact_mod_cast Nat.div_add_mod n p
  have hqZ : (q : ℤ) * ((n / q : ℕ) : ℤ) + ((n % q : ℕ) : ℤ) = (n : ℤ) := by
    exact_mod_cast Nat.div_add_mod n q
  unfold quotientCarry
  linear_combination -u * hpZ - v * hqZ

theorem residueFraction_period_of_dvd (d L n : ℕ) (hd : d ∣ L) :
    residueFraction d (n + L) = residueFraction d n := by
  unfold residueFraction
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, add_zero, Nat.mod_mod]

/-- Periodicity needs no CRT coefficient condition. -/
theorem carry_period (p q : ℕ) (a b : ℤ) (n : ℕ) :
    carry p q a b (n + p * q) = carry p q a b n := by
  unfold carry
  rw [residueFraction_period_of_dvd p (p * q) n ⟨q, rfl⟩,
    residueFraction_period_of_dvd q (p * q) n ⟨p, Nat.mul_comm p q⟩]

@[simp] theorem carry_zero (p q : ℕ) (a b : ℤ) : carry p q a b 0 = 0 := by
  simp [carry, residueFraction]

theorem carry_jump
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    (carry p q a b (n + 1) : ℝ) - (carry p q a b n : ℝ) =
      (t : ℝ) - (a : ℝ) * divisorIndicator p (n + 1) -
        (b : ℝ) * divisorIndicator q (n + 1) + divisorIndicator (p * q) (n + 1) := by
  rw [real_quotient_formula p q a b t (n + 1) hp hq hcrt,
    real_quotient_formula p q a b t n hp hq hcrt,
    real_div_succ p n hp, real_div_succ q n hq,
    real_div_succ (p * q) n (Nat.mul_pos hp hq)]
  push_cast
  ring

/-- On the initial segment below both conductors the carry has drift `t`. -/
theorem carry_head
    (p q : ℕ) (a b t : ℤ) (n : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ))
    (hnp : n < p) (hnq : n < q) :
    carry p q a b n = t * (n : ℤ) := by
  have hpq : p ≤ p * q := by
    simpa using Nat.mul_le_mul_left p (show 1 ≤ q by omega)
  rw [carry_eq_quotientCarry p q a b t n hp hq hcrt]
  simp [quotientCarry, Nat.div_eq_of_lt hnp, Nat.div_eq_of_lt hnq,
    Nat.div_eq_of_lt (lt_of_lt_of_le hnp hpq)]

/-- Coprime conductors have integral representatives with zero drift. -/
theorem exists_coefficients_of_coprime (p q : ℕ) (hcop : Nat.Coprime p q) :
    ∃ a b t : ℤ, (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ) := by
  refine ⟨Nat.gcdB p q, Nat.gcdA p q, 0, ?_⟩
  have hz : (1 : ℤ) = (p : ℤ) * Nat.gcdA p q + (q : ℤ) * Nat.gcdB p q := by
    simpa [hcop.gcd_eq_one] using Nat.gcd_eq_gcd_ab p q
  have hr : (1 : ℝ) = (p : ℝ) * (Nat.gcdA p q : ℝ) +
      (q : ℝ) * (Nat.gcdB p q : ℝ) := by exact_mod_cast hz
  simpa [mul_comm, add_comm] using hr.symm

end RiemannResearch.RH.CRTCarryArithmetic
