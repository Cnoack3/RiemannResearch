import RiemannResearch.RH.DyadicTentMellinCoefficients
import Mathlib.Analysis.PSeries

/-!
Logarithmically weighted absolute summability of the actual dyadic tent
Mellin coefficients. This is the analytic majorant needed for the signed
residue Fourier cutoffs; it does not assert the cutoff bound itself.

Source: continuation of the user-provided Fourier tent handoff. The proof
uses Mathlib's elementary logarithm bound and the integer p-series test.
-/

noncomputable section

namespace RiemannResearch.Analysis

/-- A logarithmic weight grows at most like the square root, with an
explicit constant valid for every argument at least one. -/
theorem one_add_log_two_add_le_rpow_half {a : ℝ} (ha : 1 ≤ a) :
    1 + Real.log (2 + a) ≤ (3 + Real.log 3) * a ^ (1 / 2 : ℝ) := by
  have ha0 : 0 < a := by linarith
  have hr : 1 ≤ a ^ (1 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) ha
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hlog : Real.log (2 + a) ≤ Real.log 3 + Real.log a := by
    calc
      Real.log (2 + a) ≤ Real.log (3 * a) :=
        Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 3 + Real.log a := Real.log_mul (by norm_num) ha0.ne'
  have hpow := Real.log_le_rpow_div ha0.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hk : 0 ≤ 1 + Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    linarith
  have hkr := mul_le_mul_of_nonneg_left hr hk
  calc
    1 + Real.log (2 + a) ≤ 1 + Real.log 3 + 2 * a ^ (1 / 2 : ℝ) := by
      linarith
    _ ≤ (1 + Real.log 3) * a ^ (1 / 2 : ℝ) + 2 * a ^ (1 / 2 : ℝ) := by
      linarith
    _ = (3 + Real.log 3) * a ^ (1 / 2 : ℝ) := by ring

/-- Any inverse-square integer-frequency row is absolutely summable after
multiplication by the logarithmic frequency weight. The zero mode is kept
as its own finite summand. -/
theorem summable_norm_mul_one_add_log_of_inv_sq
    {E : Type*} [NormedAddCommGroup E] (f : ℤ → E) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ h : ℤ, h ≠ 0 → ‖f h‖ ≤ C / (h : ℝ) ^ 2) :
    Summable (fun h : ℤ => ‖f h‖ * (1 + Real.log (2 + |(h : ℝ)|))) := by
  have hp := (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)).mul_left
    (C * (3 + Real.log 3))
  have hz := (hasSum_ite_eq (0 : ℤ) (‖f 0‖ * (1 + Real.log 2))).summable
  apply (hp.add hz).of_nonneg_of_le
  · intro h
    have hl : 0 ≤ Real.log (2 + |(h : ℝ)|) :=
      Real.log_nonneg (by have := abs_nonneg (h : ℝ); linarith)
    positivity
  · intro h
    by_cases hh : h = 0
    · subst h
      simp
    · have ha1 : (1 : ℝ) ≤ |(h : ℝ)| := by
        by_cases hpos : 0 ≤ h
        · rw [abs_of_nonneg (show (0 : ℝ) ≤ (h : ℝ) by exact_mod_cast hpos)]
          exact_mod_cast (show 1 ≤ h by omega)
        · rw [abs_of_neg (show (h : ℝ) < 0 by exact_mod_cast (show h < 0 by omega))]
          exact_mod_cast (show 1 ≤ -h by omega)
      have ha : 0 < |(h : ℝ)| := by linarith
      have hw : 0 ≤ 1 + Real.log (2 + |(h : ℝ)|) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + |(h : ℝ)|)
        linarith
      have hb := one_add_log_two_add_le_rpow_half ha1
      have heq : |(h : ℝ)| ^ (1 / 2 : ℝ) / |(h : ℝ)| ^ 2 =
          |(h : ℝ)| ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_sub_natCast ha.ne' (1 / 2 : ℝ) 2]
        norm_num
      simp only [hh, if_false, add_zero]
      calc
        ‖f h‖ * (1 + Real.log (2 + |(h : ℝ)|)) ≤
            (C / (h : ℝ) ^ 2) * (1 + Real.log (2 + |(h : ℝ)|)) :=
          mul_le_mul_of_nonneg_right (hf h hh) hw
        _ ≤ (C / (h : ℝ) ^ 2) *
            ((3 + Real.log 3) * |(h : ℝ)| ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hb (div_nonneg hC (sq_nonneg _))
        _ = C * (3 + Real.log 3) *
            (|(h : ℝ)| ^ (1 / 2 : ℝ) / |(h : ℝ)| ^ 2) := by
          rw [sq_abs]
          ring
        _ = C * (3 + Real.log 3) * |(h : ℝ)| ^ (-(3 / 2 : ℝ)) := by rw [heq]

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto

/-- The actual dyadic tent Mellin row absorbs a logarithmic arithmetic
cutoff majorant without any RH or signed-energy hypothesis. -/
theorem summable_norm_dyadicTentMellinCoefficient_mul_one_add_log (i : ℕ) :
    Summable (fun h : ℤ => ‖dyadicTentMellinCoefficient i h‖ *
      (1 + Real.log (2 + |(h : ℝ)|))) := by
  apply RiemannResearch.Analysis.summable_norm_mul_one_add_log_of_inv_sq
    (dyadicTentMellinCoefficient i)
    (4 * (2 * (i + 1) + 1 : ℝ) * Real.log 2 / (2 * Real.pi) ^ 2)
  · positivity
  · intro h hh
    exact norm_dyadicTentMellinCoefficient_le_inv_sq i hh

end RiemannResearch.RH.Pareto
