import RiemannResearch.RH.ParetoProgressionTaylor
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Identifying all positive Pareto p-series coefficients with actual zeta values

The Taylor and digamma coefficient `positivePSeries k` is the convergent real
series over positive integers. This module identifies it with Mathlib's
analytic Riemann zeta function for every natural `k > 1`, including odd k.
-/

namespace RiemannResearch.RH.Pareto

noncomputable section

/-- Every convergent positive p-series is strictly positive. -/
theorem positivePSeries_pos (k : ℕ) (hk : 2 ≤ k) : 0 < positivePSeries k := by
  exact (positivePSeries_summable k hk).tsum_pos
    (fun n => by positivity) 0 (by simp)

theorem positivePSeries_coe_eq_zeta (k : ℕ) (hk : 1 < k) :
    (positivePSeries k : ℂ) = riemannZeta (k : ℂ) := by
  unfold positivePSeries
  rw [Complex.ofReal_tsum,
    zeta_eq_tsum_one_div_nat_add_one_cpow (by exact_mod_cast hk : 1 < (k : ℂ).re)]
  apply tsum_congr
  intro j
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.cpow_natCast]

/-- Every small-argument digamma coefficient is an actual Riemann zeta value. -/
theorem positivePSeries_eq_zeta_re (k : ℕ) (hk : 1 < k) :
    positivePSeries k = (riemannZeta (k : ℂ)).re := by
  have h := congrArg Complex.re (positivePSeries_coe_eq_zeta k hk)
  simpa only [Complex.ofReal_re] using h

theorem riemannZeta_nat_im_eq_zero (k : ℕ) (hk : 1 < k) :
    (riemannZeta (k : ℂ)).im = 0 := by
  rw [← positivePSeries_coe_eq_zeta k hk]
  rfl

end
end RiemannResearch.RH.Pareto
