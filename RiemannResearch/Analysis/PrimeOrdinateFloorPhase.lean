/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimeOrdinateTwist
import RiemannResearch.Analysis.AtomSpanReweighting
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Normalized floors and exact prime-logarithm phases

Source: user suggestion to use integer parts of zeta-zero ordinates times
prime logarithms, 14 October 2026. For the unit-circle phase the period is
2 pi. The integer part cancels exactly, leaving the fractional part of
gamma log(p)/(2 pi). Nonzero complex phase weights preserve every fixed
dictionary span, even for arbitrary primewise ordinate assignments.
These identities supply neither zero equidistribution nor a legal tail bound.
-/

noncomputable section
namespace RiemannResearch.Analysis.PrimeOrdinateTwist

/-- The integer part cancels exactly from the unit-circle phase. -/
theorem phase_eq_fract (x : ℝ) :
    Complex.exp (-Complex.I * (2 * Real.pi * x : ℝ)) =
      Complex.exp (-Complex.I * (2 * Real.pi * Int.fract x : ℝ)) := by
  have hsplit : (-Complex.I * (2 * Real.pi * x : ℝ) : ℂ) =
      -Complex.I * (2 * Real.pi * Int.fract x : ℝ) +
        (-(Int.floor x) : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    simp only [Int.fract]
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Applied to a prime logarithm, the relevant floor uses the period 2 pi. -/
theorem primePhase_eq_fract (γ : ℕ → ℝ) (p : ℕ) :
    primePhase γ p = Complex.exp
      (-Complex.I * (2 * Real.pi * Int.fract (γ p * Real.log p / (2 * Real.pi)) : ℝ)) := by
  have hd : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hmul : 2 * Real.pi * (γ p * Real.log p / (2 * Real.pi)) =
      γ p * Real.log p := by field_simp [hd]
  simpa only [hmul, primePhase] using
    phase_eq_fract (γ p * Real.log p / (2 * Real.pi))

end RiemannResearch.Analysis.PrimeOrdinateTwist

namespace RiemannResearch.Analysis.PrimeOrdinateTwist

/-- Even arbitrary primewise ordinate assignments only reweight a fixed complex dictionary. -/
theorem primePhase_span_eq {H ι : Type*} [AddCommGroup H] [Module ℂ H]
    (v : ι → H) (d : ι → ℕ) (γ : ℕ → ℝ) :
    Submodule.span ℂ (Set.range (fun i => primePhase γ (d i) • v i)) =
      Submodule.span ℂ (Set.range v) :=
  RiemannResearch.Analysis.AtomSpanReweighting.span_range_smul_eq v
    (fun i => primePhase γ (d i)) (fun i => Complex.exp_ne_zero _)

end RiemannResearch.Analysis.PrimeOrdinateTwist
