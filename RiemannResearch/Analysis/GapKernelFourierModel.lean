/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelPolynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Normalization and separation of the Gaussian Fourier-side model

The companion Fourier certificate identifies this real model with the
cosine transform. The finite polynomial signs and the scale inequality
give the exact unit diagonal and the required strict off-diagonal sign.
-/

namespace RiemannResearch.Analysis.GapKernelPolynomial

noncomputable def fourierModel (s : ℝ) (q : List ℤ) (u : ℝ) : ℝ :=
  Real.exp (-(Real.pi * (s*u)^2)) * value q (Real.pi * (s*u)^2) / value q 0

theorem fourierModel_zero {s : ℝ} {q : List ℤ} (hq : 0 < value q 0) :
    fourierModel s q 0 = 1 := by simp [fourierModel, hq.ne']

theorem fourierModel_neg_of_separation {s gapLimit t u : ℝ} {q : List ℤ}
    (hq : 0 < value q 0) (hgap : 0 ≤ gapLimit)
    (htail : ∀ y, t ≤ y → value q y < 0)
    (hedge : t ≤ Real.pi * (s*gapLimit)^2) (hu : gapLimit ≤ |u|) :
    fourierModel s q u < 0 := by
  have hsquare : gapLimit^2 ≤ u^2 := by
    calc
      _ ≤ |u|^2 := pow_le_pow_left₀ hgap hu 2
      _ = _ := sq_abs u
  have hscaled : Real.pi * (s*gapLimit)^2 ≤ Real.pi * (s*u)^2 := by
    simpa only [mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_left hsquare (mul_nonneg Real.pi_pos.le (sq_nonneg s))
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (Real.exp_pos _) (htail _ (hedge.trans hscaled))) hq

end RiemannResearch.Analysis.GapKernelPolynomial
