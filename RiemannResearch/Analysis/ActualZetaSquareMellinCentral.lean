/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZetaSquareMellinTail
import RiemannResearch.Analysis.SymmetricZetaRatio
import RiemannResearch.Analysis.ZetaAbsoluteConvergenceBounds
/-!
# The actual zeta-square Mellin kernel in the central region

The unconditional functional-equation estimate gives growth U^(3/4)
for zeta on Re s = -1/4 when U <= t <= 2U and |v| <= U/2.
The actual kernel bound retains both |Gamma(-3/4+iv)| and Y^(-3/4),
for every real Y > 0.

This is a pointwise analytic estimate. The sharp mean-square remainder
still needs the exact contour identity and weighted divisor head/tail
estimates after applying the functional equation.
Source for the contour setting: Chourasiya--Simonic, Section 5.1,
https://arxiv.org/html/2507.15184v2
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis
open SymmetricZetaRatio

/-- The actual zeta factor on the left contour has its functional-equation
growth exponent, uniformly throughout the central dyadic region. -/
theorem norm_riemannZeta_neg_quarter_central_le {U t v : ℝ}
    (hU : 2 ≤ U) (ht : t ∈ Set.Icc U (2 * U)) (hv : |v| ≤ U / 2) :
    ‖riemannZeta ((-1 / 4 : ℂ) + I * ((t + v : ℝ) : ℂ))‖ ≤
      (10 * Real.pi ^ (-3 / 4 : ℝ) * Real.exp 5 * (5 / 4 : ℝ) ^ (3 / 4 : ℝ)) *
        U ^ (3 / 4 : ℝ) := by
  have htv : 0 < t + v := by
    have := (abs_le.mp hv).1
    linarith [ht.1]
  have hs : (((-1 / 4 : ℂ) + I * ((t + v : ℝ) : ℂ))).im ≠ 0 := by
    simpa using ne_of_gt htv
  have hz : ‖riemannZeta (1 - ((-1 / 4 : ℂ) + I * ((t + v : ℝ) : ℂ)))‖ ≤ 5 := by
    have hh := norm_riemannZeta_le_integral_test
      (s := 1 - ((-1 / 4 : ℂ) + I * ((t + v : ℝ) : ℂ))) (by norm_num)
    norm_num at hh ⊢
    exact hh
  rw [Zeta23.XiPrime.Hardy.zeta_eq_chiFE_mul hs, norm_mul]
  have hh := mul_le_mul (norm_chiFE_neg_quarter_central_le hU ht hv) hz
    (norm_nonneg _) (by positivity)
  nlinarith [hh]

/-- An explicit bound for the actual original Mellin kernel in the central
region. The Gamma factor and the real smoothing-scale power are retained. -/
theorem norm_zetaSquareMellinKernel_left_central_le {U Y t v : ℝ}
    (hU : 2 ≤ U) (hY : 0 < Y) (ht : t ∈ Set.Icc U (2 * U)) (hv : |v| ≤ U / 2) :
    ‖zetaSquareMellinKernel Y t ((-3 / 4 : ℂ) + I * v)‖ ≤
      (‖Gamma ((-3 / 4 : ℂ) + I * v)‖ * Y ^ (-3 / 4 : ℝ)) *
        ((10 * Real.pi ^ (-3 / 4 : ℝ) * Real.exp 5 * (5 / 4 : ℝ) ^ (3 / 4 : ℝ)) *
          U ^ (3 / 4 : ℝ)) ^ 2 := by
  have he : (1 / 2 : ℂ) + I * t + ((-3 / 4 : ℂ) + I * v) =
      (-1 / 4 : ℂ) + I * ((t + v : ℝ) : ℂ) := by
    push_cast
    ring
  have hy : ‖(Y : ℂ) ^ ((-3 / 4 : ℂ) + I * v)‖ = Y ^ (-3 / 4 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    norm_num
  rw [zetaSquareMellinKernel, norm_mul, norm_mul, norm_pow, he, hy]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_riemannZeta_neg_quarter_central_le hU ht hv) 2)
    (by positivity)

end RiemannResearch.Analysis
