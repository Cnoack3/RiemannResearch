/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GammaRatioVertical
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Defs
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.Hardy.Basic
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symmetric shifted-zeta bounds from the functional equation

The exact norm identity is retained before estimating its Gamma factor.
The multiplicative bound is unconditional and remains valid at zeros:

`‖ζ(1/2-ε+it)‖ ≤ exp(20ε/t²) * (|t|/(2π))^ε * ‖ζ(1/2+ε+it)‖`

for `0 ≤ ε < 1/2` and `1 ≤ |t|`. A quotient corollary explicitly assumes
its denominator is nonzero. Only the stated high-frequency range is covered.

Source: Báez-Duarte, *A strengthening of the Nyman-Beurling criterion for
the Riemann Hypothesis, 2*, Lemma 2.2, https://arxiv.org/abs/math/0205003,
supports the symmetric functional-equation strategy. The explicit error
factor is obtained from the repository's proved vertical digamma estimate.
These bounds do not prove the fixed-damping Möbius cutoff L² limit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex
open scoped ComplexConjugate

namespace RiemannResearch.Analysis.SymmetricZetaRatio
open GammaRatioVertical

/-- Exact norm of the functional-equation multiplier on symmetric lines. -/
theorem norm_chiFE_symmetric (ε t : ℝ) :
    ‖Zeta23.XiPrime.chiFE (((1 / 2 - ε : ℝ) : ℂ) + I * t)‖ =
      Real.pi ^ (-ε) *
        ‖Complex.Gamma (((1 / 4 + ε / 2 : ℝ) : ℂ) + I * (t / 2)) /
          Complex.Gamma (((1 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2))‖ := by
  let s : ℂ := ((1 / 2 - ε : ℝ) : ℂ) + I * t
  have hnum : (1 - s) / 2 =
      conj (((1 / 4 + ε / 2 : ℝ) : ℂ) + I * (t / 2)) := by
    apply Complex.ext <;> simp [s, map_ofNat] <;> ring
  have hden : s / 2 =
      (((1 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2)) := by
    apply Complex.ext <;> simp [s] <;> ring
  have hpn : (-(1 - s) / 2).re = -(1 / 4 + ε / 2) := by
    simp [s]
    ring
  have hpd : (-s / 2).re = -(1 / 4 - ε / 2) := by
    simp [s]
    ring
  have hn : ‖Complex.Gammaℝ (1 - s)‖ =
      Real.pi ^ (-(1 / 4 + ε / 2)) *
        ‖Complex.Gamma (((1 / 4 + ε / 2 : ℝ) : ℂ) + I * (t / 2))‖ := by
    rw [Complex.Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hpn,
      hnum, Complex.Gamma_conj, norm_conj]
  have hd : ‖Complex.Gammaℝ s‖ =
      Real.pi ^ (-(1 / 4 - ε / 2)) *
        ‖Complex.Gamma (((1 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2))‖ := by
    rw [Complex.Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hpd, hden]
  change ‖Zeta23.XiPrime.chiFE s‖ = _
  rw [Zeta23.XiPrime.Hardy.chiFE_def, norm_div, hn, hd,
    norm_div, mul_div_mul_comm, ← Real.rpow_sub Real.pi_pos]
  congr 2
  ring

/-- Exact symmetric functional-equation norm identity. At zeros it retains
both zero factors and requires no division by zeta. -/
theorem norm_zeta_symmetric_eq (ε : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖riemannZeta (((1 / 2 - ε : ℝ) : ℂ) + I * t)‖ =
      (Real.pi ^ (-ε) *
        ‖Complex.Gamma (((1 / 4 + ε / 2 : ℝ) : ℂ) + I * (t / 2)) /
          Complex.Gamma (((1 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2))‖) *
      ‖riemannZeta (((1 / 2 + ε : ℝ) : ℂ) + I * t)‖ := by
  have hs : ((((1 / 2 - ε : ℝ) : ℂ) + I * t)).im ≠ 0 := by simpa using ht
  have hR : (((1 / 2 + ε : ℝ) : ℂ) + I * t) ≠ 1 := by
    intro hh
    apply ht
    have hi := congrArg Complex.im hh
    simpa using hi
  have hreflect : 1 - (((1 / 2 - ε : ℝ) : ℂ) + I * t) =
      conj (((1 / 2 + ε : ℝ) : ℂ) + I * t) := by
    apply Complex.ext <;> simp <;> ring
  rw [Zeta23.XiPrime.Hardy.zeta_eq_chiFE_mul hs, norm_mul,
    hreflect, Zeta23.riemannZeta_conj hR, norm_conj, norm_chiFE_symmetric]

/-- The explicit high-frequency symmetric zeta inequality, including at
zeros, without RH or a nonvanishing hypothesis. -/
theorem norm_zeta_symmetric_le {ε t : ℝ} (hε : 0 ≤ ε)
    (hεhalf : ε < 1 / 2) (ht : 1 ≤ |t|) :
    ‖riemannZeta (((1 / 2 - ε : ℝ) : ℂ) + I * t)‖ ≤
      (Real.exp (20 * ε / t ^ 2) * (|t| / (2 * Real.pi)) ^ ε) *
        ‖riemannZeta (((1 / 2 + ε : ℝ) : ℂ) + I * t)‖ := by
  have ht0 : t ≠ 0 := by
    intro hh
    norm_num [hh] at ht
  rw [norm_zeta_symmetric_eq ε ht0]
  have hg := norm_Gamma_symmetric_ratio_le hε hεhalf ht
  have hrpow : Real.pi ^ (-ε) * (|t| / 2) ^ ε =
      (|t| / (2 * Real.pi)) ^ ε := by
    calc
      _ = (|t| / 2) ^ ε / Real.pi ^ ε := by
        rw [Real.rpow_neg Real.pi_pos.le]
        ring
      _ = ((|t| / 2) / Real.pi) ^ ε :=
        (Real.div_rpow (by positivity) Real.pi_pos.le ε).symm
      _ = (|t| / (2 * Real.pi)) ^ ε := by
        congr 1
        ring
  calc
    _ ≤ (Real.pi ^ (-ε) *
        (Real.exp (20 * ε / t ^ 2) * (|t| / 2) ^ ε)) *
        ‖riemannZeta (((1 / 2 + ε : ℝ) : ℂ) + I * t)‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg Real.pi_pos.le _))
        (norm_nonneg _)
    _ = (Real.exp (20 * ε / t ^ 2) * (|t| / (2 * Real.pi)) ^ ε) *
        ‖riemannZeta (((1 / 2 + ε : ℝ) : ℂ) + I * t)‖ := by
      rw [mul_left_comm (Real.pi ^ (-ε)) (Real.exp _) _, hrpow]

/-- Quotient version of the multiplicative estimate, with its exact
nonvanishing condition displayed. -/
theorem norm_zeta_symmetric_ratio_le {ε t : ℝ} (hε : 0 ≤ ε)
    (hεhalf : ε < 1 / 2) (ht : 1 ≤ |t|)
    (hz : riemannZeta (((1 / 2 + ε : ℝ) : ℂ) + I * t) ≠ 0) :
    ‖riemannZeta (((1 / 2 - ε : ℝ) : ℂ) + I * t) /
        riemannZeta (((1 / 2 + ε : ℝ) : ℂ) + I * t)‖ ≤
      Real.exp (20 * ε / t ^ 2) * (|t| / (2 * Real.pi)) ^ ε := by
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hz)]
  exact norm_zeta_symmetric_le hε hεhalf ht

end RiemannResearch.Analysis.SymmetricZetaRatio
