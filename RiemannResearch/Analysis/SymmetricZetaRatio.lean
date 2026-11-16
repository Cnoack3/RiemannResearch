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

open GammaRatioVertical
theorem norm_chiFE_symmetric_le_of_abs_lt {ε t : ℝ}
    (hε : |ε| < 1 / 2) (ht : 1 ≤ |t|) :
    ‖Zeta23.XiPrime.chiFE (((1 / 2 - ε : ℝ) : ℂ) + I * t)‖ ≤
      Real.pi ^ (-ε) * (Real.exp (20 * |ε| / t ^ 2) * (|t| / 2) ^ ε) := by
  rw [norm_chiFE_symmetric]
  exact mul_le_mul_of_nonneg_left
    (norm_Gamma_symmetric_ratio_le_of_abs_lt hε ht) (Real.rpow_nonneg Real.pi_pos.le _)

/-- One Gamma recurrence extends the bound across the line Re s = 0.
This includes the entire left contour range -1 ≤ Re s ≤ 0. -/
theorem norm_chiFE_symmetric_le_of_half_le {ε t : ℝ}
    (hε : 1 / 2 ≤ ε) (hε3 : ε ≤ 3 / 2) (ht : 1 ≤ |t|) :
    ‖Zeta23.XiPrime.chiFE (((1 / 2 - ε : ℝ) : ℂ) + I * t)‖ ≤
      2 * Real.pi ^ (-ε) * Real.exp (20 * |ε - 1| / t ^ 2) *
        (|t| / 2) ^ ε := by
  let z : ℂ := (((1 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2))
  let b : ℂ := (((1 / 4 + ε / 2 : ℝ) : ℂ) + I * (t / 2))
  have htpos : 0 < |t| := by linarith
  have htne : t ≠ 0 := abs_pos.mp htpos
  have hz : z ≠ 0 := by
    intro hh
    have hi := congrArg Complex.im hh
    simp [z] at hi
    exact htne hi
  have he : z + 1 = (((5 / 4 - ε / 2 : ℝ) : ℂ) + I * (t / 2)) := by
    dsimp [z]
    push_cast
    ring
  have hq : Gamma b / Gamma z = z * (Gamma b / Gamma (z+1)) := by
    rw [Gamma_add_one z hz, ← mul_div_assoc, mul_div_mul_left _ _ hz]
  have ht' : (1 / 2 : ℝ) ≤ |t / 2| := by
    rw [abs_div, abs_two]
    linarith
  have hb := norm_Gamma_ratio_le_of_pos
    (a := 5 / 4 - ε / 2) (b := 1 / 4 + ε / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) ht'
  have hd : (1 / 4 + ε / 2 : ℝ) - (5 / 4 - ε / 2) = ε - 1 := by ring
  have hf : 5 * |ε-1| / (t / 2)^2 = 20 * |ε-1| / t^2 := by ring
  have hb' : ‖Gamma b / Gamma (z+1)‖ ≤
      Real.exp (20 * |ε-1| / t^2) * (|t| / 2) ^ (ε-1) := by
    simpa only [he, b, hd, hf, abs_div, abs_two, Complex.ofReal_div,
      Complex.ofReal_ofNat] using hb
  have hn : ‖z‖ ≤ |t| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    have ha : |1 / 4 - ε / 2| ≤ 1 / 2 := by
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    simp only [z, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, mul_zero, sub_zero, add_zero, zero_add, Complex.div_ofNat_re,
      Complex.div_ofNat_im, zero_div, abs_div, abs_two]
    linarith
  have hp : |t| * (|t| / 2) ^ (ε - 1) = 2 * (|t| / 2) ^ ε := by
    calc
      _ = 2 * ((|t| / 2) ^ (1 : ℝ) * (|t| / 2) ^ (ε - 1)) := by
        rw [Real.rpow_one]
        ring
      _ = 2 * (|t| / 2) ^ (1 + (ε - 1)) := by
        rw [Real.rpow_add (by positivity : 0 < |t| / 2)]
      _ = _ := by congr 2; ring
  rw [norm_chiFE_symmetric]
  change Real.pi ^ (-ε) * ‖Gamma b / Gamma z‖ ≤ _
  rw [hq, norm_mul]
  calc
    _ ≤ Real.pi ^ (-ε) * (|t| *
        (Real.exp (20 * |ε-1| / t^2) * (|t| / 2) ^ (ε-1))) := by
      gcongr
    _ = (Real.pi ^ (-ε) * Real.exp (20 * |ε-1| / t^2)) *
        (|t| * (|t| / 2) ^ (ε-1)) := by ring
    _ = _ := by rw [hp]; ring

theorem norm_chiFE_neg_quarter_le {t : ℝ} (ht : 1 ≤ |t|) :
    ‖Zeta23.XiPrime.chiFE ((-1 / 4 : ℂ) + I * t)‖ ≤
      2 * Real.pi ^ (-3 / 4 : ℝ) * Real.exp (5 / t ^ 2) *
        (|t| / 2) ^ (3 / 4 : ℝ) := by
  have h := norm_chiFE_symmetric_le_of_half_le
    (ε := 3 / 4) (by norm_num) (by norm_num) ht
  norm_num at h ⊢
  exact h

theorem norm_chiFE_three_quarters_le {t : ℝ} (ht : 1 ≤ |t|) :
    ‖Zeta23.XiPrime.chiFE ((3 / 4 : ℂ) + I * t)‖ ≤
      Real.pi ^ (1 / 4 : ℝ) * (Real.exp (5 / t ^ 2) *
        (|t| / 2) ^ (-1 / 4 : ℝ)) := by
  have h := norm_chiFE_symmetric_le_of_abs_lt (ε := -1 / 4) (by norm_num) ht
  norm_num at h ⊢
  exact h



private theorem central_height_abs_bounds {U t v : ℝ}
    (hU : 2 ≤ U) (ht : t ∈ Set.Icc U (2*U)) (hv : |v| ≤ U/2) :
    U/2 ≤ |t+v| ∧ |t+v| ≤ 5*U/2 := by
  have hvlo := (abs_le.mp hv).1
  have ht0 : 0 ≤ t := by linarith [ht.1]
  constructor
  · exact (show U/2 ≤ t+v by linarith [ht.1]).trans (le_abs_self _)
  · have hh := abs_add_le t v
    rw [abs_of_nonneg ht0] at hh
    linarith [ht.2]

private theorem exp_five_div_sq_le {t : ℝ} (ht : 1 ≤ |t|) :
    Real.exp (5/t^2) ≤ Real.exp 5 := by
  have htpos : 0 < |t| := by linarith
  have ht2 : (1 : ℝ) ≤ t^2 := by
    simpa only [one_pow, sq_abs] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht 2
  apply Real.exp_le_exp.mpr
  exact (div_le_iff₀ (sq_pos_of_ne_zero (abs_pos.mp htpos))).2 (by nlinarith)

/-- The left functional-equation factor, uniform throughout the central
dyadic contour. -/
theorem norm_chiFE_neg_quarter_central_le {U t v : ℝ}
    (hU : 2 ≤ U) (ht : t ∈ Set.Icc U (2*U)) (hv : |v| ≤ U/2) :
    ‖Zeta23.XiPrime.chiFE ((-1/4 : ℂ) + I * ((t + v : ℝ) : ℂ))‖ ≤
      (2 * Real.pi ^ (-3/4 : ℝ) * Real.exp 5 * (5/4 : ℝ) ^ (3/4 : ℝ)) *
        U ^ (3/4 : ℝ) := by
  obtain ⟨hl, hu⟩ := central_height_abs_bounds hU ht hv
  have hw : 1 ≤ |t+v| := by linarith
  calc
    _ ≤ 2 * Real.pi ^ (-3/4 : ℝ) * Real.exp (5/(t+v)^2) *
        (|t+v|/2) ^ (3/4 : ℝ) := norm_chiFE_neg_quarter_le hw
    _ ≤ 2 * Real.pi ^ (-3/4 : ℝ) * Real.exp 5 *
        ((5/4 : ℝ)*U) ^ (3/4 : ℝ) := by
      gcongr
      · exact Real.exp_le_exp.mp (exp_five_div_sq_le hw)
      · linarith
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5/4) (by linarith : 0 ≤ U)]
      ring

/-- The right contour gains a negative quarter power of the height. -/
theorem norm_chiFE_three_quarters_central_le {U t v : ℝ}
    (hU : 2 ≤ U) (ht : t ∈ Set.Icc U (2*U)) (hv : |v| ≤ U/2) :
    ‖Zeta23.XiPrime.chiFE ((3/4 : ℂ) + I * ((t + v : ℝ) : ℂ))‖ ≤
      (Real.pi ^ (1/4 : ℝ) * Real.exp 5 * (1/4 : ℝ) ^ (-1/4 : ℝ)) *
        U ^ (-1/4 : ℝ) := by
  obtain ⟨hl, hu⟩ := central_height_abs_bounds hU ht hv
  have hw : 1 ≤ |t+v| := by linarith
  have hp : (|t+v|/2) ^ (-1/4 : ℝ) ≤ ((1/4 : ℝ)*U) ^ (-1/4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (1/4 : ℝ)*U)
      (by linarith) (by norm_num)
  calc
    _ ≤ Real.pi ^ (1/4 : ℝ) *
        (Real.exp (5/(t+v)^2) * (|t+v|/2) ^ (-1/4 : ℝ)) :=
      norm_chiFE_three_quarters_le hw
    _ ≤ Real.pi ^ (1/4 : ℝ) *
        (Real.exp 5 * ((1/4 : ℝ)*U) ^ (-1/4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (exp_five_div_sq_le hw) hp
          (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
        (Real.rpow_nonneg Real.pi_pos.le _)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/4) (by linarith : 0 ≤ U)]
      ring

end RiemannResearch.Analysis.SymmetricZetaRatio
