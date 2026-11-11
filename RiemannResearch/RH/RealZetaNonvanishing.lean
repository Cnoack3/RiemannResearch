/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinNormalizedResidue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Real-axis zeta nonvanishing from the actual normalized residue series

Source: the classical positivity argument requested in
`PrimePowerTargetsResearch20261020.md`, Section 2. The checked first Mellin
difference series of g_2 is nonnegative on the positive real axis and has a
strictly positive first term. This supplies real-axis nonvanishing without
assuming RH or a closure statement. The totalized value at the pole is
irrelevant here and is excluded explicitly.
-/

noncomputable section
namespace RiemannResearch.RH
open Pareto ArithmeticCumulative RiemannResearch.Analysis.Cesaro

private theorem real_mellinFirst_term (σ : ℝ) (n : ℕ) :
    (mellinFirst (σ : ℂ) n * (residueFraction 2 n : ℂ)).re =
      ((n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ)) * residueFraction 2 n := by
  have he : mellinFirst (σ : ℂ) n =
      (((n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    simp only [mellinFirst, Complex.ofReal_sub, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_natCast, Complex.ofReal_neg]
  rw [he, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The actual normalized conductor product has strictly positive real part
on the positive real axis away from the pole. This retains the sign needed
for the zeta-kernel continuation obstruction. -/
theorem riemannZeta_ofReal_conductor_re_pos (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    0 < (((1 / (2 : ℂ) - (2 : ℂ) ^ (-(σ : ℂ))) * riemannZeta (σ : ℂ))).re := by
  have hσC1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1
  have hsumC := residueFraction_first_hasSum_zeta 2 (by norm_num)
    (σ : ℂ) hσ hσC1
  have hsum := Complex.reCLM.hasSum hsumC
  change HasSum (fun k : ℕ =>
    (mellinFirst (σ : ℂ) (k + 1) * (residueFraction 2 (k + 1) : ℂ)).re)
    (((1 / (2 : ℂ) - (2 : ℂ) ^ (-(σ : ℂ))) * riemannZeta (σ : ℂ))).re at hsum
  simp only [real_mellinFirst_term] at hsum
  have hnonneg (k : ℕ) :
      0 ≤ (((k + 1 : ℕ) : ℝ) ^ (-σ) -
        ((k + 1 + 1 : ℕ) : ℝ) ^ (-σ)) * residueFraction 2 (k + 1) := by
    apply mul_nonneg
    · apply sub_nonneg.mpr
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast Nat.le_succ (k + 1)
      · linarith
    · unfold residueFraction
      positivity
  have hfirst : 0 < (((0 + 1 : ℕ) : ℝ) ^ (-σ) -
        ((0 + 1 + 1 : ℕ) : ℝ) ^ (-σ)) * residueFraction 2 (0 + 1) := by
    apply mul_pos
    · apply sub_pos.mpr
      exact Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by linarith)
    · norm_num [residueFraction]
  have hp := hsum.summable.tsum_pos hnonneg 0 hfirst
  rw [hsum.tsum_eq] at hp
  exact hp

/-- No positive real number away from the pole is a zeta zero. -/
theorem riemannZeta_ofReal_ne_zero (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  have hp := riemannZeta_ofReal_conductor_re_pos σ hσ hσ1
  simp only [hz, mul_zero, Complex.zero_re] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- The continued zeta value has strictly negative real part on (0,1).
In particular this proves the negative diagonal obstruction in Section 5
of the user-provided V_vector_space_RH.pdf without an RH premise. -/
theorem riemannZeta_ofReal_re_neg (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hp := riemannZeta_ofReal_conductor_re_pos σ hσ (ne_of_lt hσ1)
  have he : (1 / (2 : ℂ) - (2 : ℂ) ^ (-(σ : ℂ))) =
      (((1 / 2 : ℝ) - (2 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  have hpow : (1 / 2 : ℝ) < (2 : ℝ) ^ (-σ) := by
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  nlinarith

end RiemannResearch.RH
