import RiemannResearch.RH.DigammaAsymptotic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Complete fractional-part square-norm constant

The explicit cell square integral has coefficient
`2 - 1/(n+2) - 2*(n+1)*(log(n+2)-log(n+1))` for the cell starting at `n+1`.
Its complete sum is proved using the actual harmonic and Stirling limits,
with all finite factorial and endpoint terms retained.

Source for the underlying classical Stirling statement: NIST DLMF 5.11.1,
https://dlmf.nist.gov/5.11.E1. The coefficient telescoping is elementary;
the named constant is derived from Mathlib's proved Stirling limit.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.StepCorrectionNorm

theorem rawResidueCellEnergy_eq_trapezoidal (n : ℕ) :
    2 - 1 / ((n : ℝ) + 2) -
        2 * ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) =
      2 * ((n : ℝ) + 1) * DigammaAsymptotic.cellError ((n : ℝ) + 1) := by
  have h₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [DigammaAsymptotic.cellError]
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  field_simp [h₁, h₂]
  <;> ring

theorem rawResidueCellEnergy_sum_range (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (2 - 1 / ((n : ℝ) + 2) -
        2 * ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)))) =
      2 * ((N : ℝ) + 1) - (harmonic (N + 1) : ℝ) -
        2 * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) +
        2 * Real.log (((N + 1).factorial : ℕ) : ℝ) - 1 := by
  induction N with
  | zero => norm_num [harmonic_succ]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ (N + 1),
      Nat.factorial_succ (N + 1)]
    have hf : (((N + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
      Nat.cast_one, Nat.cast_mul, Nat.cast_succ]
    simp only [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    rw [Real.log_mul (by positivity) hf]
    ring_nf

theorem rawResidueCellEnergy_sum_range_eq_stirling (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (2 - 1 / ((n : ℝ) + 2) -
        2 * ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)))) =
      2 * Real.log (Stirling.stirlingSeq (N + 1)) + Real.log 2 -
        ((harmonic (N + 1) : ℝ) - Real.log (((N + 1 : ℕ) : ℝ))) - 1 := by
  rw [rawResidueCellEnergy_sum_range, Stirling.log_stirlingSeq_formula]
  have hn : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Real.log_mul (by norm_num) hn,
    Real.log_div hn (Real.exp_ne_zero 1), Real.log_exp]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem hasSum_rawResidueCellEnergy :
    HasSum (fun n : ℕ =>
      (2 - 1 / ((n : ℝ) + 2) -
        2 * ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1))))
      (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant - 1) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by
    rw [rawResidueCellEnergy_eq_trapezoidal]
    exact mul_nonneg (by positivity)
      (DigammaAsymptotic.cellError_nonneg (by positivity))) _).mpr
  have hs := (Real.continuousAt_log
    (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))).tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
  have hh := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hlimit := (((hs.const_mul 2).add_const (Real.log 2)).sub hh).sub_const 1
  convert hlimit using 1
  · funext N
    exact rawResidueCellEnergy_sum_range_eq_stirling N
  · rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring

end RiemannResearch.RH.StepCorrectionNorm
