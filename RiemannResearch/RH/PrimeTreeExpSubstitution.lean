/-
Copyright (c) 2026 Mathlib and RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib and RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Full-ray exponential change of variables
These exponential specializations of the one-dimensional change of variables theorem
are included in later Mathlib versions in `MeasureTheory.Integral.IntegralEqImproper`.
They pass from the sheet's positive Mellin variable to its full logarithmic variable. -/
noncomputable section
open Set MeasureTheory Real
namespace RiemannResearch.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_comp_exp_full (g : ℝ → E) :
    ∫ x, exp x • g (exp x) = ∫ y in Ioi 0, g y := by
  symm
  rw [← range_exp, ← image_univ]
  simpa [abs_of_pos (exp_pos _)] using integral_image_eq_integral_abs_deriv_smul .univ
    (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

theorem integrable_comp_exp_full (g : ℝ → E) :
    Integrable (fun x => exp x • g (exp x)) ↔ IntegrableOn g (Ioi 0) := by
  rw [← integrableOn_univ, ← range_exp, ← image_univ]
  symm
  simpa [abs_of_pos (exp_pos _)] using integrableOn_image_iff_integrableOn_abs_deriv_smul
    .univ (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

end RiemannResearch.Analysis
