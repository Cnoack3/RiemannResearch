/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.GapKernelPolynomialPrimitive
import RiemannResearch.Analysis.GapKernelObjective

/-! # Rational evaluation of Gaussian-polynomial gap objectives -/

noncomputable section
namespace RiemannResearch.Analysis.GapKernelObjective
open GapKernelPolynomial MeasureTheory

/-- A rational polynomial certificate suffices for the strict
real-valued Lamzouri objective, uniformly in the polynomial degree. -/
theorem polynomial_objective_gt_one (P : List ℤ) {r θ q : ℚ} (n : ℕ)
    (hr : 0 < r) (hθ : 0 < θ) (hq : 0 < q)
    (hH : 0 ≤ ratValue (primitiveFrom 0 P) (r^2)) (hE : 0 < expLower (r^2) n)
    (hnum : (177245385090551603 / 100000000000000000 : ℚ) * q <
      (r/θ)*ratValue P 0 + (θ/r)*(ratValue (primitiveFrom 0 P) 0 -
        ratValue (primitiveFrom 0 P) (r^2) / expLower (r^2) n)) :
    1 < test r θ q (value P) 0 + 2 * ∫ x in (0:ℝ)..(θ:ℝ), x * test r θ q (value P) x := by
  have hd := objective_gt_one hr hθ hq hH hE hnum
  have hP : Continuous (value P) :=
    continuous_iff_continuousAt.mpr fun x => (value_hasDerivAt _ x).continuousAt
  rw [functional_eq (by exact_mod_cast hr) (by exact_mod_cast hθ) (by exact_mod_cast hq)
    hP (primitive_hasDerivAt P)]
  simpa only [cast_ratValue, Rat.cast_zero, Rat.cast_pow] using hd

end RiemannResearch.Analysis.GapKernelObjective
