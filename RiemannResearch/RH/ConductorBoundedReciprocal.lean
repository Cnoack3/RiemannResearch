import RiemannResearch.RH.ArithmeticConductorCommonZeros
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Bounded reciprocal and exact geometric expansion of the actual conductor symbol

Source: RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md, Section 4.
These statements concern the existing actual entire factor
`conductorSymbol n s = n⁻¹ - exp (-s * log n)`.
The lower bound is uniform in the imaginary part and the series is proved
summable. The L² translation-operator realization is a separate obligation.

Verified continuation of the preserved 9 September 2026 candidate.
-/

noncomputable section

namespace RiemannResearch.RH.ArithmeticConductorCommonZeros

/-- Reverse triangle inequality for the actual conductor symbol. -/
theorem conductorSymbol_norm_lower_bound (n : ℕ) (s : ℂ) :
    Real.exp (-s.re * Real.log n) - (n : ℝ)⁻¹ ≤ ‖conductorSymbol n s‖ := by
  have h := norm_sub_norm_le (Complex.exp (-s * (Real.log n : ℂ))) ((n : ℂ)⁻¹)
  rw [norm_sub_rev] at h
  simpa only [conductorSymbol, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, norm_inv, Complex.norm_natCast] using h

/-- The explicit lower bound is strictly positive throughout `Re(s) < 1`. -/
theorem conductorSymbol_gap_pos (n : ℕ) (hn : 1 < n) (s : ℂ) (hs : s.re < 1) :
    0 < Real.exp (-s.re * Real.log n) - (n : ℝ)⁻¹ := by
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hnR
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have h : (n : ℝ)⁻¹ < Real.exp (-s.re * Real.log n) := calc
    (n : ℝ)⁻¹ = Real.exp (-Real.log n) := by
      rw [Real.exp_neg, Real.exp_log hn0]
    _ < Real.exp (-s.re * Real.log n) := Real.exp_lt_exp.mpr (by nlinarith)
  exact sub_pos.mpr h

/-- A bound depending only on the real part, including the critical line. -/
theorem conductorSymbol_inv_norm_bound (n : ℕ) (hn : 1 < n) (s : ℂ)
    (hs : s.re < 1) :
    ‖(conductorSymbol n s)⁻¹‖ ≤
      (Real.exp (-s.re * Real.log n) - (n : ℝ)⁻¹)⁻¹ := by
  rw [norm_inv]
  simpa only [one_div] using
    one_div_le_one_div_of_le (conductorSymbol_gap_pos n hn s hs)
      (conductorSymbol_norm_lower_bound n s)

/-- The ratio in the left-translation geometric expansion lies inside the disk. -/
theorem conductorSymbol_inverse_ratio_norm_lt_one (n : ℕ) (hn : 1 < n)
    (s : ℂ) (hs : s.re < 1) :
    ‖Complex.exp (s * (Real.log n : ℂ)) / (n : ℂ)‖ < 1 := by
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hnR
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hexp : Real.exp (s.re * Real.log n) < (n : ℝ) := calc
    Real.exp (s.re * Real.log n) < Real.exp (Real.log n) :=
      Real.exp_lt_exp.mpr (by nlinarith)
    _ = (n : ℝ) := Real.exp_log hn0
  simpa only [norm_div, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_natCast] using (div_lt_one hn0).mpr hexp

/-- Convergent geometric expansion with the exact reciprocal as its sum. -/
theorem conductorSymbol_reciprocal_hasSum (n : ℕ) (hn : 1 < n)
    (s : ℂ) (hs : s.re < 1) :
    HasSum (fun j : ℕ =>
      -((n : ℂ)⁻¹ ^ j * Complex.exp (s * (Real.log n : ℂ)) ^ (j + 1)))
      (conductorSymbol n s)⁻¹ := by
  let z : ℂ := Complex.exp (s * (Real.log n : ℂ))
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one hn))
  have hsymbol : conductorSymbol n s = (n : ℂ)⁻¹ - z⁻¹ := by
    simp only [conductorSymbol, neg_mul, Complex.exp_neg, z]
  have hfactor : 1 - z / (n : ℂ) = -z * conductorSymbol n s := by
    rw [hsymbol]
    field_simp [hnC, hz]
    <;> ring
  have hvalue : -z * (1 - z / (n : ℂ))⁻¹ = (conductorSymbol n s)⁻¹ := by
    rw [hfactor, mul_inv_rev]
    calc
      -z * ((conductorSymbol n s)⁻¹ * (-z)⁻¹) =
          (-z * (-z)⁻¹) * (conductorSymbol n s)⁻¹ := by ring
      _ = (conductorSymbol n s)⁻¹ := by simp [hz]
  have hsum :=
    (hasSum_geometric_of_norm_lt_one
      (conductorSymbol_inverse_ratio_norm_lt_one n hn s hs)).mul_left (-z)
  rw [hvalue] at hsum
  have heq : (fun j : ℕ => -z * (Complex.exp (s * (Real.log n : ℂ)) / (n : ℂ)) ^ j) =
      (fun j : ℕ => -((n : ℂ)⁻¹ ^ j * Complex.exp (s * (Real.log n : ℂ)) ^ (j + 1))) := by
    funext j
    dsimp only [z]
    rw [div_eq_mul_inv, mul_pow, pow_succ]
    ring
  rw [heq] at hsum
  exact hsum

/-- The scalar formula in Section 4, using exponential notation for `n^((j+1)s)`. -/
theorem conductorSymbol_reciprocal_hasSum_exp (n : ℕ) (hn : 1 < n)
    (s : ℂ) (hs : s.re < 1) :
    HasSum (fun j : ℕ => -((n : ℂ)⁻¹ ^ j *
      Complex.exp (((j : ℂ) + 1) * s * (Real.log n : ℂ))))
      (conductorSymbol n s)⁻¹ := by
  have heq : (fun j : ℕ => -((n : ℂ)⁻¹ ^ j * Complex.exp (s * (Real.log n : ℂ)) ^ (j + 1))) =
      (fun j : ℕ => -((n : ℂ)⁻¹ ^ j * Complex.exp (((j : ℂ) + 1) * s * (Real.log n : ℂ)))) := by
    funext j
    rw [← Complex.exp_nat_mul]
    congr 3
    push_cast
    ring
  rw [← heq]
  exact conductorSymbol_reciprocal_hasSum n hn s hs

end RiemannResearch.RH.ArithmeticConductorCommonZeros
