import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic noncancellation of the minimal-seed power-damping resonance

Source: user-provided argument, `RH_Minimal_Seeds_Continuation_20260916.md`,
Section 12, equations (12.5), (12.8)--(12.10). The citation supports the
expressions and the unequal-modulus proof.

This module proves the rational-symbol algebra and the nonzero candidate
residue, unconditionally. It does not assert Hilbert-space nonmembership.
That assertion additionally needs the actual infinite damped-packet Mellin
identity, its continuation, and the zeta-factor noncancellation. Those
analytic inputs are not hypotheses hidden in the declarations below.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Equation (12.5), with `x = 2^(1-s)`, `y = 3^(1-s)`,
`a = 2^(1-s-ε)` and `b = 3^(1-s-ε)`. -/
def minimalSeedDampingSymbol (x y a b : ℂ) : ℂ :=
  (1 - x) * (1 - b / 3) + a / 2 * (1 - y) +
    (a * b) / (3 * (1 - a * b)) * ((1 - x) + a * (1 - y))

/-- Polynomial numerator after clearing the geometric denominator. -/
def minimalSeedDampingNumerator (x y a b : ℂ) : ℂ :=
  3 * (1 - a * b) * ((1 - x) * (1 - b / 3) + a / 2 * (1 - y)) +
    a * b * ((1 - x) + a * (1 - y))

theorem minimalSeedDampingSymbol_clear_denominator (x y a b : ℂ)
    (hab : a * b ≠ 1) :
    3 * (1 - a * b) * minimalSeedDampingSymbol x y a b =
      minimalSeedDampingNumerator x y a b := by
  have hd : 1 - a * b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold minimalSeedDampingSymbol minimalSeedDampingNumerator
  field_simp [hd]
  <;> ring

/-- The cancellation at zero damping is exact, away from the geometric
denominator's zeros. -/
theorem minimalSeedDampingSymbol_undamped (a b : ℂ) (hab : a * b ≠ 1) :
    minimalSeedDampingSymbol a b a b = (1 - a / 2) * (1 - b / 3) := by
  have hd : 1 - a * b ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  unfold minimalSeedDampingSymbol
  field_simp [hd]
  <;> ring

/-- At a geometric resonance the cleared numerator reduces to the precise
two-term expression from (12.8). -/
theorem minimalSeedDampingNumerator_at_resonance (A B a b : ℂ)
    (hab : a * b = 1) :
    minimalSeedDampingNumerator (A * a) (B * b) a b =
      1 - B + (1 - A) * a := by
  unfold minimalSeedDampingNumerator
  simp only [hab, sub_self, mul_zero, zero_mul, zero_add, one_mul]
  calc
    (1 - A * a) + a * (1 - B * b) =
        1 - B * (a * b) + (1 - A) * a := by ring
    _ = 1 - B + (1 - A) * a := by rw [hab]; ring

/-- Quantitative reverse-triangle estimate for the actual resonance
numerator; its lower bound is strictly positive when `ε > 0`. -/
theorem powerDamping_resonance_numerator_norm_lower {ε : ℝ} (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ = 1) :
    (3 : ℝ) ^ ε - (2 : ℝ) ^ ε ≤
      ‖1 - (Complex.ofReal ((3 : ℝ) ^ ε)) + (1 - (Complex.ofReal ((2 : ℝ) ^ ε))) * a‖ := by
  have hA : 1 < (2 : ℝ) ^ ε := by
    simpa using Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) < 2) hε
  have hB : 1 < (3 : ℝ) ^ ε := by
    simpa using Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) < 3) hε
  have hnorm (v : ℝ) (hv : 1 < v) : ‖(1 : ℂ) - (v : ℂ)‖ = v - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hv)]
    ring
  have htri := norm_sub_le
    (1 - (Complex.ofReal ((3 : ℝ) ^ ε)) + (1 - (Complex.ofReal ((2 : ℝ) ^ ε))) * a)
    ((1 - (Complex.ofReal ((2 : ℝ) ^ ε))) * a)
  rw [add_sub_cancel_right, norm_mul, ha, mul_one, hnorm _ hB, hnorm _ hA] at htri
  linarith

/-- The unequal sizes of `3^ε-1` and `2^ε-1` rule out cancellation
for every unit complex phase. -/
theorem powerDamping_resonance_numerator_ne_zero {ε : ℝ} (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ = 1) :
    1 - (Complex.ofReal ((3 : ℝ) ^ ε)) + (1 - (Complex.ofReal ((2 : ℝ) ^ ε))) * a ≠ 0 := by
  intro h
  have hbound := powerDamping_resonance_numerator_norm_lower hε ha
  rw [h, norm_zero] at hbound
  have hAB : (2 : ℝ) ^ ε < (3 : ℝ) ^ ε :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hε
  linarith

/-- The cleared geometric numerator is nonzero at every positive-damping
unit-phase resonance. -/
theorem minimalSeedDampingNumerator_ne_zero_at_resonance {ε : ℝ} (hε : 0 < ε)
    {a b : ℂ} (ha : ‖a‖ = 1) (hab : a * b = 1) :
    minimalSeedDampingNumerator ((Complex.ofReal ((2 : ℝ) ^ ε)) * a)
      ((Complex.ofReal ((3 : ℝ) ^ ε)) * b) a b ≠ 0 := by
  rw [minimalSeedDampingNumerator_at_resonance _ _ _ _ hab]
  exact powerDamping_resonance_numerator_ne_zero hε ha

/-- The specific phase `exp(-i T log 2)`, where `T = 2π/log 6`. -/
def minimalSeedResonancePhase : ℂ :=
  Complex.exp (((-(2 * Real.pi / Real.log 6) * Real.log 2 : ℝ) : ℂ) * Complex.I)

theorem minimalSeedResonancePhase_norm : ‖minimalSeedResonancePhase‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- The explicit candidate residue (12.9). Identifying it with the residue
of the actual Mellin transform remains a separate analytic obligation. -/
def minimalSeedPowerDampingResidue (ε : ℝ) : ℂ :=
  (1 - (Complex.ofReal ((3 : ℝ) ^ ε)) +
    (1 - (Complex.ofReal ((2 : ℝ) ^ ε))) * minimalSeedResonancePhase) /
      ((3 : ℂ) * (Complex.ofReal (Real.log (6 : ℝ))))

/-- A quantitative bound for the explicit residue expression. -/
theorem minimalSeedPowerDampingResidue_norm_lower {ε : ℝ} (hε : 0 < ε) :
    ((3 : ℝ) ^ ε - (2 : ℝ) ^ ε) / (3 * Real.log 6) ≤
      ‖minimalSeedPowerDampingResidue ε‖ := by
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hd : ‖(3 : ℂ) * (Complex.ofReal (Real.log (6 : ℝ)))‖ = 3 * Real.log 6 := by
    have hl : ‖Complex.ofReal (Real.log (6 : ℝ))‖ = Real.log 6 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
    rw [norm_mul, hl]
    norm_num
  unfold minimalSeedPowerDampingResidue
  rw [norm_div, hd]
  exact div_le_div_of_nonneg_right
    (powerDamping_resonance_numerator_norm_lower hε minimalSeedResonancePhase_norm)
    (by positivity)

theorem minimalSeedPowerDampingResidue_ne_zero {ε : ℝ} (hε : 0 < ε) :
    minimalSeedPowerDampingResidue ε ≠ 0 := by
  apply div_ne_zero
  · exact powerDamping_resonance_numerator_ne_zero hε minimalSeedResonancePhase_norm
  · have hlog : (Real.log 6 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    exact_mod_cast mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hlog

end
end RiemannResearch.RH.Pareto
