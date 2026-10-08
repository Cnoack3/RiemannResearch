/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCoreAlgebraicity
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Algebraicity transfer for the finite constrained physical minimum

An algebraic nonzero inverse charge makes the exact constrained minimum
`1 + 4 * π / C` algebraic if and only if π is algebraic.  Thus a proof of
π's transcendence transfers to this minimum without any algebraicity
assumption on logarithms.  The transcendence corollaries below explicitly
retain that premise: this file supplies no proof of π's transcendence and
no statement about the arithmetic limit of inverse charges.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.ArithmeticMinimumTranscendence
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.PhysicalPacketCore
open RiemannResearch.RH.Pareto.ArithmeticCoreAlgebraicity

/-- A nonzero algebraic charge cannot change algebraicity of the parameter. -/
theorem isAlgebraic_affine_quotient_iff (x C : ℝ)
    (hC : IsAlgebraic ℚ C) (hC0 : C ≠ 0) :
    IsAlgebraic ℚ (1 + 4 * x / C) ↔ IsAlgebraic ℚ x := by
  have hfour : IsAlgebraic ℚ (4 : ℝ) := isAlgebraic_natCast 4
  constructor
  · intro hE
    have h := ((hE.sub (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ))).mul hC).mul
      hfour.inv
    convert! h using 1
    field_simp [hC0] <;> ring
  · intro hx
    simpa only [div_eq_mul_inv] using
      (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ)).add ((hfour.mul hx).mul hC.inv)

/-- The same transfer phrased as transcendence, with no premise on π. -/
theorem transcendental_affine_quotient_iff (x C : ℝ)
    (hC : IsAlgebraic ℚ C) (hC0 : C ≠ 0) :
    Transcendental ℚ (1 + 4 * x / C) ↔ Transcendental ℚ x := by
  exact not_congr (isAlgebraic_affine_quotient_iff x C hC hC0)

/-- The literal optimized Pareto error inherits exactly π's algebraicity status. -/
theorem constrainedOptimizer_error_isAlgebraic_iff (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    IsAlgebraic ℚ (paretoError (synthesis s (constrainedOptimizer s))) ↔
      IsAlgebraic ℚ Real.pi := by
  rw [constrainedOptimizer_error s hs hodd]
  exact isAlgebraic_affine_quotient_iff _ _ (inverseCharge_algebraic s hs)
    (ne_of_lt (inverseCharge_neg s hs hodd))

/-- Conditional only on an independently supplied transcendence theorem for π. -/
theorem constrainedOptimizer_error_transcendental (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (hpi : Transcendental ℚ Real.pi) :
    Transcendental ℚ (paretoError (synthesis s (constrainedOptimizer s))) := by
  intro hE
  exact hpi ((constrainedOptimizer_error_isAlgebraic_iff s hs hodd).mp hE)

end RiemannResearch.RH.Pareto.ArithmeticMinimumTranscendence
