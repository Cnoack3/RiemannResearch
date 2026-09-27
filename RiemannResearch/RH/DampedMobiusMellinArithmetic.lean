import RiemannResearch.RH.DampedDivisorLSeries
import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Arithmetic Mellin identity for the actual centered damped Möbius prefix

Source: J.-F. Burnol, arXiv:math/0202166, Lemma 4.3 (the arithmetic Mellin
identification). The proof here uses Mathlib's Dirichlet convolution and Abel
summation. The centering constant is arbitrary, and every result is restricted
to the unconditional half-plane `1 < Re(s)`.

The final declaration applies to an actual `ThresholdHilbert` element whose
coordinates are the centered arithmetic prefix. Existence of such an element
for damping tending to zero is not established here.
-/

open scoped BigOperators
open Filter MeasureTheory Set

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Positive integer partial sums of the genuine divisor coefficients are
exactly the previously defined floor-convolution prefix. -/
theorem dampedDivisorCoefficient_sum_Icc (ε : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, dampedDivisorCoefficient ε n) =
      dampedMobiusPrefix ε N := by
  rw [dampedMobiusPrefix_eq_sum_divisors]
  change (∑ n ∈ Finset.Icc 1 N, dampedDivisorCoefficient ε n) =
    ∑ n ∈ Finset.range (N + 1), dampedDivisorCoefficient ε n
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  simp

/-- The centered coefficient partial sum retains the full floor correction. -/
theorem centeredDampedDivisorCoefficient_sum_Icc (ε C : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)) =
      ((dampedMobiusPrefix ε N - (N : ℝ) * C : ℝ) : ℂ) := by
  have hreal : (∑ n ∈ Finset.Icc 1 N, (dampedDivisorCoefficient ε n - C)) =
      dampedMobiusPrefix ε N - (N : ℝ) * C := by
    rw [Finset.sum_sub_distrib, dampedDivisorCoefficient_sum_Icc]
    simp
  exact_mod_cast hreal

/-- The Euler-product bounds give a linear bound on the sum of absolute
centered coefficients, with explicit constant `1 + ‖C‖`. -/
theorem centeredDampedDivisorCoefficient_sum_norm_isBigO
    {ε : ℝ} (hε : 0 ≤ ε) (C : ℝ) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      ‖((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)‖) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 : ℝ)) := by
  have hterm (n : ℕ) :
      ‖((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)‖ ≤ 1 + ‖(C : ℂ)‖ := by
    have ha : ‖(dampedDivisorCoefficient ε n : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (dampedDivisorCoefficient_nonneg hε n)] using
        dampedDivisorCoefficient_le_one hε n
    rw [Complex.ofReal_sub]
    exact (norm_sub_le _ _).trans (add_le_add ha le_rfl)
  refine Asymptotics.IsBigO.of_bound (1 + ‖(C : ℂ)‖) ?_
  filter_upwards [] with N
  calc
    ‖∑ n ∈ Finset.Icc 1 N, ‖((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)‖‖ =
        ∑ n ∈ Finset.Icc 1 N, ‖((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)‖ :=
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 + ‖(C : ℂ)‖) :=
      Finset.sum_le_sum fun n _ => hterm n
    _ = (1 + ‖(C : ℂ)‖) * ‖(N : ℝ) ^ (1 : ℝ)‖ := by
      simp [Real.rpow_one, mul_comm]
      ring

/-- Exact Mellin identity in the unconditional half-plane, with an arbitrary
real centering constant and the full arithmetic floor prefix. -/
theorem dampedMobiusPrefix_centered_mellin {ε : ℝ} (hε : 0 ≤ ε)
    (C : ℝ) {s : ℂ} (hs : 1 < s.re) :
    s * (∫ x in Ioi (1 : ℝ),
      ((dampedMobiusPrefix ε ⌊x⌋₊ - (⌊x⌋₊ : ℝ) * C : ℝ) : ℂ) *
        (x : ℂ) ^ (-(s + 1))) =
      riemannZeta s / riemannZeta (s + (ε : ℂ)) - (C : ℂ) * riemannZeta s := by
  have hshift : 1 < (s + (ε : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hc : LSeriesHasSum (fun _n : ℕ => (C : ℂ)) s
      ((C : ℂ) * riemannZeta s) := by
    have hconst : (C : ℂ) • (1 : ℕ → ℂ) = fun _n : ℕ => (C : ℂ) := by
      funext n
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [← hconst]
    exact (LSeriesHasSum_one hs).smul (C : ℂ)
  have hsum : LSeriesHasSum
      (fun n => ((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)) s
      (riemannZeta s / riemannZeta (s + (ε : ℂ)) - (C : ℂ) * riemannZeta s) := by
    have hcoeff : (fun n => ((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)) =
        (fun n => (dampedDivisorCoefficient ε n : ℂ)) - (fun _n : ℕ => (C : ℂ)) := by
      funext n
      simp only [Pi.sub_apply, Complex.ofReal_sub]
    rw [hcoeff]
    exact (dampedDivisorCoefficient_LSeriesHasSum hs hshift).sub hc
  have hformula := LSeries_eq_mul_integral'
    (fun n => ((dampedDivisorCoefficient ε n - C : ℝ) : ℂ))
    (by norm_num : (0 : ℝ) ≤ 1) hs
    (centeredDampedDivisorCoefficient_sum_norm_isBigO hε C)
  have heq : LSeries (fun n => ((dampedDivisorCoefficient ε n - C : ℝ) : ℂ)) s =
      riemannZeta s / riemannZeta (s + (ε : ℂ)) - (C : ℂ) * riemannZeta s :=
    hsum.LSeries_eq
  rw [heq] at hformula
  simpa only [centeredDampedDivisorCoefficient_sum_Icc] using hformula.symm

/-- The arithmetic identity is now tied to the actual continuous Mellin
functional of an actual finite-energy Pareto vector. -/
theorem paretoMellin_of_centered_dampedMobiusPrefix
    (f : ThresholdHilbert) {ε : ℝ} (hε : 0 ≤ ε) (C : ℝ)
    (hcoordinates : ∀ n : ℕ,
      hilbertSequence f n = dampedMobiusPrefix ε n - (n : ℝ) * C)
    {s : ℂ} (hs : 1 < s.re) :
    s * paretoMellin f s =
      riemannZeta s / riemannZeta (s + (ε : ℂ)) - (C : ℂ) * riemannZeta s := by
  rw [paretoMellin_eq_step_integral]
  simp_rw [hcoordinates, show (-s - 1 : ℂ) = -(s + 1) by ring]
  exact dampedMobiusPrefix_centered_mellin hε C hs

end
end RiemannResearch.RH.Pareto
