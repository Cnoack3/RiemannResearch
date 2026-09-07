import RiemannResearch.Analysis.WeightedAbelDiscrepancy
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Exact prime-power and pole-density cancellation

Source: user-provided argument, `RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`
§3. The statement and partial-summation strategy are taken from that argument.
All arithmetic weights are the actual von Mangoldt weights Λ(n)/sqrt(n).
The formula uses x=exp(t) coordinates and keeps the upper boundary.
-/

open scoped BigOperators
open MeasureTheory Set
namespace RiemannResearch.RH

/-- Full prime-power coefficient, using Mathlib's actual von Mangoldt function. -/
noncomputable def vonMangoldtHalfWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- Exact prime-power discrepancy against the pole-density primitive. -/
noncomputable def vonMangoldtHalfDiscrepancy (x : ℝ) : ℝ :=
  Analysis.abelCounting vonMangoldtHalfWeight x - 2 * (Real.sqrt x - 1)

/-- Exact finite prime-power term evaluated on a logarithmic correlation profile. -/
noncomputable def primePowerHalfCutoff (C : ℝ → ℝ) (b : ℝ) : ℝ :=
  -2 * ∑ n ∈ Finset.Icc 0 ⌊b⌋₊, vonMangoldtHalfWeight n * C (Real.log n)

/-- Derivative of the exact continuous density primitive. -/
theorem hasDerivAt_halfDensityPrimitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => 2 * (Real.sqrt y - 1)) (1 / Real.sqrt x) x := by
  have h := ((Real.hasDerivAt_sqrt hx.ne').sub_const 1).const_mul 2
  convert h using 1 <;> first | rfl | ring

/-- Exact arithmetic partial summation with all prime powers retained.
No prime estimate is assumed. The diagonal continuous density is subtracted
only after the prime-power counting function has been kept exactly. -/
theorem primePowerHalfCutoff_exact_discrepancy (C : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b)
    (hd : ∀ x ∈ Icc 1 b, DifferentiableAt ℝ (fun x => C (Real.log x)) x)
    (hcd : ContinuousOn (deriv (fun x => C (Real.log x))) (Icc 1 b)) :
    primePowerHalfCutoff C b =
      -2 * C (Real.log b) * vonMangoldtHalfDiscrepancy b
      -2 * (∫ x in Ioc 1 b, C (Real.log x) / Real.sqrt x)
      +2 * ∫ x in Ioc 1 b,
        deriv (fun x => C (Real.log x)) x * vonMangoldtHalfDiscrepancy x := by
  have hw : vonMangoldtHalfWeight 0 = 0 := by simp [vonMangoldtHalfWeight]
  have hF : ∀ x ∈ Icc 1 b,
      HasDerivAt (fun y => 2 * (Real.sqrt y - 1)) (1 / Real.sqrt x) x := by
    intro x hx
    exact hasDerivAt_halfDensityPrimitive (by linarith [hx.1])
  have hF' : ContinuousOn (fun x => 1 / Real.sqrt x) (Icc 1 b) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      (by intro x hx; exact Real.sqrt_ne_zero'.mpr (by linarith [hx.1]))
  have h := Analysis.weighted_abel_discrepancy vonMangoldtHalfWeight hw
    (fun x => C (Real.log x)) (fun x => 2 * (Real.sqrt x - 1))
    (fun x => 1 / Real.sqrt x) hb hd hcd hF hF'
  simpa only [primePowerHalfCutoff, vonMangoldtHalfDiscrepancy,
    Real.sqrt_one, sub_self, mul_zero, sub_zero, mul_one_div] using h

/-- Exact cancellation of the full prime-power term and the principal pole
density, including the upper discrepancy boundary. This is a signed identity,
not an estimate of the remaining discrepancy pairing. -/
theorem primePowerHalfCutoff_add_density (C : ℝ → ℝ) {b : ℝ} (hb : 1 ≤ b)
    (hd : ∀ x ∈ Icc 1 b, DifferentiableAt ℝ (fun x => C (Real.log x)) x)
    (hcd : ContinuousOn (deriv (fun x => C (Real.log x))) (Icc 1 b)) :
    primePowerHalfCutoff C b + 2 * (∫ x in Ioc 1 b, C (Real.log x) / Real.sqrt x) =
      -2 * C (Real.log b) * vonMangoldtHalfDiscrepancy b
      +2 * ∫ x in Ioc 1 b,
        deriv (fun x => C (Real.log x)) x * vonMangoldtHalfDiscrepancy x := by
  rw [primePowerHalfCutoff_exact_discrepancy C hb hd hcd]
  ring

end RiemannResearch.RH
