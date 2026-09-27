import RiemannResearch.RH.DampedMobiusCoefficients
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Dirichlet series of the actual damped divisor coefficients

Source: J.-F. Burnol, "On an analytic estimate in the theory of the Riemann
Zeta function and a theorem of Báez-Duarte", arXiv:math/0202166, Lemma 4.3.
The source supports the zeta quotient and the arithmetic step of the Mellin
argument. This module establishes that quotient directly by absolutely
convergent Dirichlet convolution, using the repository's actual coefficients.

This does not assert continuation under finite Pareto energy, or that such
energy is finite for small positive damping.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Real power damping shifts the Dirichlet variable exactly. -/
theorem dampedMobiusWeight_LSeries_term (ε : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun k => (dampedMobiusWeight ε k : ℂ)) s n =
      (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ (s + (ε : ℂ)) := by
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn]
    unfold dampedMobiusWeight
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rw [Complex.cpow_neg, Complex.cpow_add s (ε : ℂ)
      (by exact_mod_cast hn : (n : ℂ) ≠ 0)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The actual real damped Möbius coefficients have the reciprocal-zeta
Dirichlet series in the shifted half-plane of absolute convergence. -/
theorem dampedMobiusWeight_LSeriesHasSum {ε : ℝ} {s : ℂ}
    (hs : 1 < (s + (ε : ℂ)).re) :
    LSeriesHasSum (fun n => (dampedMobiusWeight ε n : ℂ)) s
      (riemannZeta (s + (ε : ℂ)))⁻¹ := by
  change HasSum (LSeries.term (fun n => (dampedMobiusWeight ε n : ℂ)) s) _
  have hterm : LSeries.term (fun n => (dampedMobiusWeight ε n : ℂ)) s =
      fun n => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ (s + (ε : ℂ)) := by
    funext n
    exact dampedMobiusWeight_LSeries_term ε s n
  rw [hterm]
  have hinv : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ))
      (s + (ε : ℂ)) = (riemannZeta (s + (ε : ℂ)))⁻¹ := by
    have hmul := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at hmul
    exact eq_inv_of_mul_eq_one_right hmul
  have hsum := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  rw [hinv] at hsum
  change HasSum (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ))
    (s + (ε : ℂ))) _ at hsum
  convert hsum using 1
  funext n
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · exact (LSeries.term_of_ne_zero hn
      (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + (ε : ℂ))).symm

/-- The coefficient already defined in `DampedMobiusCoefficients` is the
Dirichlet convolution of the damped Möbius weight with the constant sequence. -/
theorem dampedDivisorCoefficient_eq_convolution (ε : ℝ) :
    LSeries.convolution (fun n => (dampedMobiusWeight ε n : ℂ)) 1 =
      fun n => (dampedDivisorCoefficient ε n : ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  simp only [Pi.one_apply, mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun k _ => (dampedMobiusWeight ε k : ℂ))]
  simp [dampedDivisorCoefficient]

/-- Exact quotient identity on the common domain of absolute convergence.
This also allows negative damping when `Re(s + ε) > 1`. -/
theorem dampedDivisorCoefficient_LSeriesHasSum {ε : ℝ} {s : ℂ}
    (hs : 1 < s.re) (hshift : 1 < (s + (ε : ℂ)).re) :
    LSeriesHasSum (fun n => (dampedDivisorCoefficient ε n : ℂ)) s
      (riemannZeta s / riemannZeta (s + (ε : ℂ))) := by
  have h := (dampedMobiusWeight_LSeriesHasSum hshift).convolution
    (LSeriesHasSum_one hs)
  simpa only [dampedDivisorCoefficient_eq_convolution,
    div_eq_mul_inv, mul_comm] using h

/-- Evaluation of the actual coefficient Dirichlet series, including zero
damping. No RH, PNT, or finite-energy hypothesis is used. -/
theorem dampedDivisorCoefficient_LSeries {ε : ℝ} (hε : 0 ≤ ε)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (dampedDivisorCoefficient ε n : ℂ)) s =
      riemannZeta s / riemannZeta (s + (ε : ℂ)) := by
  have hshift : 1 < (s + (ε : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  exact (dampedDivisorCoefficient_LSeriesHasSum hs hshift).LSeries_eq

end
end RiemannResearch.RH.Pareto
