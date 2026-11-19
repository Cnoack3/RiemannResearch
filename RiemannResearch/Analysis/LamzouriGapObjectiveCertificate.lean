/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelPolynomialPrimitive
import RiemannResearch.Analysis.GapKernelObjective
import RiemannResearch.Analysis.LamzouriGapKernel

/-!
# The small-gap integral at the certified threshold

All finite evaluations use integer coefficients and rational arithmetic.
The real integral is controlled by its polynomial primitive and an upper
bound for the reciprocal exponential. The final small-gap implication
from Lamzouri's deletion estimate is proved in the companion paper note.
-/

namespace RiemannResearch.Analysis.LamzouriGapKernel
open GapKernelPolynomial GapKernelObjective MeasureTheory

def radius : ℚ := 32543467 / 40000000
def cutoff : ℚ := 28571 / 50000
def gap : ℚ := 784981 / 1000000
private def p₀ := ratValue inputPolynomial 0
def q₀ := ratValue fourierPolynomial 0
private def H := primitiveFrom 0 inputPolynomial
private def h₀ := ratValue H 0
private def h₁ := ratValue H (radius^2)

theorem cutoff_range : (1/2 : ℚ) < cutoff ∧ cutoff < 4/7 := by norm_num [cutoff]

/-- The Fourier argument lies in the certified sign ray at the gap. -/
theorem fourier_radius : (3 : ℝ) ≤
    Real.pi * (((cutoff : ℝ) * Real.sqrt Real.pi / radius) * gap)^2 := by
  have hπ : (314159265358979323846/100000000000000000000 : ℝ) < Real.pi :=
    lt_of_le_of_lt (by norm_num) Real.pi_gt_d20
  have h : (3 : ℝ) * (radius : ℝ)^2 <
      ((314159265358979323846/100000000000000000000 : ℝ) * (cutoff : ℝ) * gap)^2 := by
    norm_num [radius, cutoff, gap]
  have hcg : 0 < (cutoff : ℝ) * gap := by norm_num [cutoff, gap]
  have hsq := mul_self_le_mul_self (by norm_num [cutoff,gap] :
    0 ≤ (314159265358979323846/100000000000000000000 : ℝ) * ((cutoff : ℝ)*gap))
    (mul_le_mul_of_nonneg_right hπ.le hcg.le)
  have hr : (0 : ℝ) < radius := by norm_num [radius]
  rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  field_simp [hr.ne']
  nlinarith only [h, hsq]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- The exact degree-83 arithmetic computes large integer Laguerre coefficients.
private theorem numerical_input :
    0 < q₀ ∧ 0 ≤ h₁ ∧ 0 < expLower (radius^2) 13 ∧
    (177245385090551603 / 100000000000000000 : ℚ) * q₀ <
      (radius/cutoff)*p₀ + (cutoff/radius)*(h₀-h₁/expLower (radius^2) 13) := by
  decide +kernel

noncomputable def physicalTest (x : ℝ) :=
  test radius cutoff q₀ (value inputPolynomial) x

/-- Lamzouri's normalized integral is strictly greater than one. -/
theorem certifiedObjective : (1 : ℝ) < physicalTest 0 +
    2 * (∫ x in (0 : ℝ)..(cutoff : ℝ), x * physicalTest x) := by
  obtain ⟨hq, hh, hs, hc⟩ := numerical_input
  have hr : 0 < radius := by norm_num [radius]
  have hθ : 0 < cutoff := by norm_num [cutoff]
  have hd := objective_gt_one hr hθ hq hh hs hc
  have hP : Continuous (value inputPolynomial) :=
    continuous_iff_continuousAt.mpr fun x => (value_hasDerivAt _ x).continuousAt
  unfold physicalTest
  rw [functional_eq (by exact_mod_cast hr) (by exact_mod_cast hθ)
    (by exact_mod_cast hq) hP (primitive_hasDerivAt inputPolynomial)]
  simpa only [p₀, h₀, h₁, H, cast_ratValue, Rat.cast_zero, Rat.cast_pow] using hd

end RiemannResearch.Analysis.LamzouriGapKernel
