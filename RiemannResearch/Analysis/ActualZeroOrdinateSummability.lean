/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.ZeroSummability

/-!
# Summability of the actual positive zero ordinates

The inverse-square summability theorem is separated from the finite zero-sum
and reflection identities so their consumers need only the finite foundation.
Source: the existing reciprocal-ordinate theorem in `ActualZeroOrdinate`,
using the vendored unconditional zero-sum bound. Its statement and proof are
unchanged.
-/

noncomputable section
open Filter MeasureTheory Complex Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Multiplicity-weighted square-summable inverse ordinates. -/
theorem reciprocal_ordinate_summable :
    Summable (fun ρ : PositiveZero => (zeroMult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2)) := by
  let includeZero : PositiveZero → (zetaZeros zetaSeam).carrier :=
    fun ρ => ⟨ρ.1, positive_zero_in_strip ρ.2.1 ρ.2.2⟩
  have hinj : Function.Injective includeZero := by
    intro ρ σ h
    exact Subtype.ext (congrArg (fun z : (zetaZeros zetaSeam).carrier => (z : ℂ)) h)
  have hs := ((Zeta23.WeilEF.zero_sum_inv_sq zetaSeam).mul_left (5 / 4 : ℝ)).comp_injective hinj
  apply Summable.of_nonneg_of_le (fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)) _ hs
  intro ρ
  change (zeroMult ρ.1 : ℝ) / (1 + ρ.1.im ^ 2) ≤
    (5 / 4 : ℝ) * ((zeroMult ρ.1 : ℝ) / (1 + normSq (gammaOf ρ.1)))
  have hstrip := positive_zero_in_strip ρ.2.1 ρ.2.2
  have hd : (1 / 2 - ρ.1.re) ^ 2 ≤ 1 / 4 := by
    nlinarith [hstrip.2.1, hstrip.2.2, sq_nonneg (ρ.1.re - 1 / 2)]
  have hden : 1 + normSq (gammaOf ρ.1) ≤ (5 / 4 : ℝ) * (1 + ρ.1.im ^ 2) := by
    rw [normSq_apply, Zeta23.WeilEF.gammaOf_re, Zeta23.WeilEF.gammaOf_im]
    nlinarith [sq_nonneg ρ.1.im]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity)
    (by linarith [normSq_nonneg (gammaOf ρ.1)])).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg (zeroMult ρ.1) :
    (0 : ℝ) ≤ (zeroMult ρ.1 : ℝ))]

end RiemannResearch.Analysis.ActualZeroOrdinate
