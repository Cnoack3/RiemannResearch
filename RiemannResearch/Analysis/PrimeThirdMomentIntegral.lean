import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact third logarithmic tail integral

Source: `Zeta_Zero_Harmonic_Analysis_20261011.md`, §11, equation (52).
This is a pure real improper-integral identity, with no zero-density,
probability, or RH hypotheses.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace RiemannResearch.Analysis.PrimeThirdMomentIntegral

def cubicDensity (t : ℝ) : ℝ := Real.log t ^ 3 / (t * Real.sqrt t)

def cubicPrimitive (t : ℝ) : ℝ :=
  -(2 * Real.log t ^ 3 + 12 * Real.log t ^ 2 + 48 * Real.log t + 96) /
    Real.sqrt t

/-- Exact antiderivative, valid throughout the positive half-line. -/
theorem cubicPrimitive_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt cubicPrimitive (cubicDensity t) t := by
  have hlog := Real.hasDerivAt_log ht.ne'
  have hsqrt := Real.sqrt_pos.mpr ht
  have hp : HasDerivAt
      (fun x : ℝ => 2 * Real.log x ^ 3 + 12 * Real.log x ^ 2 +
        48 * Real.log x + 96)
      ((6 * Real.log t ^ 2 + 24 * Real.log t + 48) / t) t := by
    convert! ((((hlog.pow 3).const_mul 2).add
      ((hlog.pow 2).const_mul 12)).add (hlog.const_mul 48)).add_const 96 using 1
    norm_num
    ring
  have h := (hp.div (Real.hasDerivAt_sqrt ht.ne') hsqrt.ne').neg
  convert! h using 1
  · ext x
    simp only [cubicPrimitive, Pi.neg_apply, Pi.div_apply, neg_div]
  · unfold cubicDensity
    simp only [Real.sq_sqrt ht.le]
    field_simp [ht.ne', hsqrt.ne']
    rw [Real.sq_sqrt ht.le]
    ring

/-- Each logarithmic polynomial term decays after division by the square root. -/
theorem log_pow_div_sqrt_tendsto (k : ℕ) :
    Tendsto (fun t : ℝ => Real.log t ^ k / Real.sqrt t) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 2)
    (k : ℝ) (by norm_num)).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow] using h

theorem cubicPrimitive_tendsto_zero : Tendsto cubicPrimitive atTop (𝓝 0) := by
  have h3 := (log_pow_div_sqrt_tendsto 3).const_mul 2
  have h2 := (log_pow_div_sqrt_tendsto 2).const_mul 12
  have h1 := (log_pow_div_sqrt_tendsto 1).const_mul 48
  have h0 := (log_pow_div_sqrt_tendsto 0).const_mul 96
  have h := ((h3.add h2).add h1).add h0
  convert h.neg using 1
  · ext t
    simp only [cubicPrimitive, pow_one, pow_zero, add_div]
    ring
  · norm_num

/-- Integrability also holds below one, where the odd logarithm is negative. -/
theorem cubicDensity_integrableOn_Ioi {P : ℝ} (hP : 0 < P) :
    IntegrableOn cubicDensity (Ioi P) := by
  let A : ℝ := max P 1
  have hA : 1 ≤ A := le_max_right _ _
  have htail : IntegrableOn cubicDensity (Ioi A) := by
    apply integrableOn_Ioi_deriv_of_nonneg'
      (g := cubicPrimitive) (l := (0 : ℝ))
    · intro t ht
      exact cubicPrimitive_hasDerivAt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (hA.trans ht))
    · intro t ht
      unfold cubicDensity
      have ht1 : 1 ≤ t := hA.trans ht.le
      have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
      exact div_nonneg (pow_nonneg (Real.log_nonneg ht1) 3)
        (mul_nonneg ht0 (Real.sqrt_nonneg _))
    · exact cubicPrimitive_tendsto_zero
  have hcompact : IntegrableOn cubicDensity (Icc P A) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have htpos : 0 < t := hP.trans_le ht.1
    have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
    exact (((Real.continuousAt_log htpos.ne').pow 3).div
      (continuousAt_id.mul Real.continuous_sqrt.continuousAt)
      (mul_ne_zero htpos.ne' hspos.ne')).continuousWithinAt
  apply (hcompact.union htail).mono_set
  intro t ht
  by_cases htA : t ≤ A
  · exact Or.inl ⟨ht.le, htA⟩
  · exact Or.inr (lt_of_not_ge htA)

/-- Exact improper integral in reciprocal-square-root notation. -/
theorem integral_cubicDensity_Ioi {P : ℝ} (hP : 0 < P) :
    (∫ t in Ioi P, cubicDensity t) =
      (2 * Real.log P ^ 3 + 12 * Real.log P ^ 2 + 48 * Real.log P + 96) /
        Real.sqrt P := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => cubicPrimitive_hasDerivAt (hP.trans_le ht))
    (cubicDensity_integrableOn_Ioi hP) cubicPrimitive_tendsto_zero
  simpa only [cubicPrimitive, zero_sub, neg_div, neg_neg] using h

/-- Equation (52) with the paper's real-power integrand. -/
theorem integral_log_cube_rpow_Ioi {P : ℝ} (hP : 0 < P) :
    (∫ t in Ioi P, Real.log t ^ 3 * t ^ (-(3 : ℝ) / 2)) =
      (2 * Real.log P ^ 3 + 12 * Real.log P ^ 2 + 48 * Real.log P + 96) /
        Real.sqrt P := by
  calc
    _ = ∫ t in Ioi P, cubicDensity t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have htpos : 0 < t := hP.trans ht
      unfold cubicDensity
      dsimp only
      rw [show -(3 : ℝ) / 2 = -((1 : ℝ) + 1 / 2) by norm_num,
        Real.rpow_neg htpos.le, Real.rpow_add htpos,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
      ring
    _ = _ := integral_cubicDensity_Ioi hP

end RiemannResearch.Analysis.PrimeThirdMomentIntegral
