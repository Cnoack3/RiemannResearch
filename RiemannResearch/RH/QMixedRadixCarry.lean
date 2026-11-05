/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CRTCarryArithmetic

/-! # Fractional parts, repeated prime factors and the missing radix digit

Source: user-provided example with conductors 3, 5 and 9. Ordinary division with
remainder identifies the exact extra digit for a repeated prime power. The
coprime prime-power blocks use the existing exact two-factor CRT formula. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTCarryArithmetic
open ArithmeticCumulative

/-- A valid signed reciprocal certificate reconstructs the composite atom
by taking the fractional part of the entire sum. -/
theorem residueFraction_product_fract (p q : ℕ) (a b t : ℤ) (n : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    residueFraction (p * q) n =
      Int.fract ((a : ℝ) * residueFraction p n + (b : ℝ) * residueFraction q n) := by
  simpa only [carry, Int.fract] using residue_eq_combination_sub_carry p q a b t n hp hq hcrt

/-- Repeated or noncoprime factors require the next quotient digit. -/
theorem residueFraction_product_digit (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    residueFraction (a * b) n =
      (residueFraction a n + (((n / a) % b : ℕ) : ℝ)) / (b : ℝ) := by
  have hq : (((n / a) % b : ℕ) : ℝ) + (b : ℝ) * ((n / (a * b) : ℕ) : ℝ) =
      ((n / a : ℕ) : ℝ) := by
    exact_mod_cast (show n / a % b + b * (n / (a * b)) = n / a by
      rw [← Nat.div_div_eq_div_mul]
      exact Nat.mod_add_div (n / a) b)
  rw [residueFraction_eq_div_sub_quotient (a * b) n (Nat.mul_pos ha hb),
    residueFraction_eq_div_sub_quotient a n ha, Nat.cast_mul]
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [← hq]
  field_simp [haR, hbR]
  <;> ring

/-- Concrete recovery from the correct two coprime blocks. -/
theorem residueFraction_135 (n : ℕ) :
    residueFraction 135 n = Int.fract (11 * residueFraction 27 n - 2 * residueFraction 5 n) := by
  have h := residueFraction_product_fract 27 5 11 (-2) 0 n (by decide) (by decide) (by norm_num)
  simpa [sub_eq_add_neg] using h

theorem residueFraction_45 (n : ℕ) :
    residueFraction 45 n = Int.fract (2 * residueFraction 9 n - residueFraction 5 n) := by
  have h := residueFraction_product_fract 9 5 2 (-1) 0 n (by decide) (by decide) (by norm_num)
  simpa [sub_eq_add_neg] using h

/-- The tuple of the proposed three residues cannot distinguish sites one and 46. -/
theorem residueFraction_135_not_function_of_3_5_9 :
    ¬ ∃ F : ℝ → ℝ → ℝ → ℝ, ∀ n : ℕ,
      F (residueFraction 3 n) (residueFraction 5 n) (residueFraction 9 n) =
        residueFraction 135 n := by
  rintro ⟨F, hF⟩
  have h1 := hF 1
  have h46 := hF 46
  norm_num [residueFraction] at h1 h46
  linarith only [h1, h46]

/-- Fractional parts may be taken inside an integer-weighted sum whenever
the fractional part is also taken outside the entire expression. -/
theorem fract_sum_integer_weights {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → ℝ) :
    Int.fract (∑ i ∈ s, (a i : ℝ) * x i) =
      Int.fract (∑ i ∈ s, (a i : ℝ) * Int.fract (x i)) := by
  apply Int.fract_eq_fract.mpr
  refine ⟨∑ i ∈ s, a i * ⌊x i⌋, ?_⟩
  rw [← Finset.sum_sub_distrib, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_mul, Int.fract]
  ring

end RiemannResearch.RH.CRTCarryArithmetic
