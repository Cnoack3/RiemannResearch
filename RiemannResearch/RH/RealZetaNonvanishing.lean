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

/-- No positive real number away from the pole is a zeta zero. -/
theorem riemannZeta_ofReal_ne_zero (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro hz
  have hσC1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1
  have hsumC := residueFraction_first_hasSum_zeta 2 (by norm_num)
    (σ : ℂ) hσ hσC1
  rw [hz, mul_zero] at hsumC
  have hsum := Complex.reCLM.hasSum hsumC
  change HasSum (fun k : ℕ =>
    (mellinFirst (σ : ℂ) (k + 1) * (residueFraction 2 (k + 1) : ℂ)).re) 0 at hsum
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
  exact (lt_irrefl (0 : ℝ)) hp

end RiemannResearch.RH
