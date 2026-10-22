import RiemannResearch.RH.DyadicResidueFourierBridge
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Exact damped Mobius Fourier symbols

Source: continuation of the user-provided
FourierResidueBridgeVerification20260911(1).md, September 11, 2026.
Mathlib.NumberTheory.LSeries.Dirichlet supplies the Mobius Dirichlet inversion
in the half-plane of absolute convergence. The actual positive integer phases
then give the signed nonzero residue-symbol sum. No Mertens or RH input is used.
-/

namespace ArithmeticFunction
open scoped BigOperators
noncomputable section

theorem moebius_dirichlet_hasSum_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ)^s)
      (riemannZeta s)⁻¹ := by
  have hsum := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).hasSum
  have he : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = (riemannZeta s)⁻¹ := by
    have hm := LSeries_one_mul_Lseries_moebius hs
    rw [LSeries_one_eq_riemannZeta hs] at hm
    exact eq_inv_of_mul_eq_one_right hm
  change HasSum (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s) _ at hsum
  rw [show (∑' n, LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n) =
      (riemannZeta s)⁻¹ from he] at hsum
  convert hsum using 1
  funext n
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · exact (LSeries.term_of_ne_zero hn (fun n => (ArithmeticFunction.moebius n : ℂ)) s).symm

theorem moebius_dirichlet_succ_hasSum_inv_zeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (ArithmeticFunction.moebius (n+1) : ℂ) / ((n+1 : ℕ) : ℂ)^s)
      (riemannZeta s)⁻¹ := by
  apply (hasSum_nat_add_iff (f := fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) / (n : ℂ)^s) 1).mpr
  simpa using moebius_dirichlet_hasSum_inv_zeta hs

end
end ArithmeticFunction

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Exact real damping and actual integer phase identify the complex Dirichlet term. -/
theorem dampedMobius_phase_eq_cpow_term (ε : ℝ) (h : ℤ) (n : ℕ) (hn : 0 < n) :
    (((ArithmeticFunction.moebius n : ℝ) / (n : ℝ)^(1+ε) : ℝ) : ℂ) *
      dyadicIntegerFourierPhase h n =
    (ArithmeticFunction.moebius n : ℂ) /
      (n : ℂ) ^ (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h : ℂ)) := by
  rw [dyadicIntegerFourierPhase_eq_cpow h n hn]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rw [Complex.cpow_sub _ _ (by exact_mod_cast hn.ne')]
  simp only [div_div_eq_mul_div]
  ring

theorem dampedMobius_phase_hasSum_inv_zeta {ε : ℝ} (hε : 0 < ε) (h : ℤ) :
    HasSum (fun n : ℕ =>
      (((ArithmeticFunction.moebius (n+1) : ℝ) / (n+1 : ℝ)^(1+ε) : ℝ) : ℂ) *
        dyadicIntegerFourierPhase h (n+1))
      (riemannZeta (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h : ℂ)))⁻¹ := by
  have hs : 1 < (1 + (ε : ℂ) - Complex.I * (dyadicLogFrequency h : ℂ)).re := by
    simpa using hε
  convert ArithmeticFunction.moebius_dirichlet_succ_hasSum_inv_zeta hs using 1
  funext n
  simpa only [Nat.cast_add, Nat.cast_one] using
    dampedMobius_phase_eq_cpow_term ε h (n+1) (by omega)

theorem dampedMobius_hasSum_inv_zeta {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ =>
      (((ArithmeticFunction.moebius (n+1) : ℝ) / (n+1 : ℝ)^(1+ε) : ℝ) : ℂ))
      (riemannZeta (1 + (ε : ℂ)))⁻¹ := by
  have hs : 1 < (1 + (ε : ℂ)).re := by simpa using hε
  convert ArithmeticFunction.moebius_dirichlet_succ_hasSum_inv_zeta hs using 1
  funext n
  push_cast
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl

theorem dampedMobius_residueSymbol_hasSum {ε : ℝ} (hε : 0 < ε)
    (h : ℤ) (hh : h ≠ 0) :
    HasSum (fun n : ℕ =>
      (((ArithmeticFunction.moebius (n+1) : ℝ) / (n+1 : ℝ)^(1+ε) : ℝ) : ℂ) *
        dyadicResidueFourierSymbol (n+1) h)
      (((riemannZeta (1+(ε : ℂ)))⁻¹ -
        (riemannZeta (1+(ε : ℂ)-Complex.I*(dyadicLogFrequency h : ℂ)))⁻¹) *
        riemannZeta (1-Complex.I*(dyadicLogFrequency h : ℂ))) := by
  convert ((dampedMobius_hasSum_inv_zeta hε).sub
    (dampedMobius_phase_hasSum_inv_zeta hε h)).mul_right
      (riemannZeta (1-Complex.I*(dyadicLogFrequency h : ℂ))) using 1
  all_goals first | rfl | (funext n; simp only [dyadicResidueFourierSymbol, if_neg hh]; ring)
end
end RiemannResearch.RH.Pareto
