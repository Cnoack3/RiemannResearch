import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The convergent Mellin transform of the Chebyshev error

For Re(s) > 1, the actual Bochner integral of (psi(x)-x) x^(-s-1)
equals -zeta'(s)/(s*zeta(s)) - 1/(s-1).

Source: user-provided V_Zeta_Vector_Spaces_Research_2026-09-16.md,
Sections 12-19, for the requested analytic link. The proof uses Mathlib's
LSeries_eq_mul_integral_of_nonneg and
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div for the
classical Abel-summation and logarithmic-derivative identities.

No convergence or equality of the integral is asserted outside Re(s) > 1.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology

namespace RiemannResearch.RH.ChebyshevMellin

theorem sum_vonMangoldt_Icc (x : ℝ) :
    (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt k) = Chebyshev.psi x := by
  rw [Chebyshev.psi_eq_sum_Icc]
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hk).2⟩
  · intro k hk hnot
    have hzero : k = 0 := by
      simp only [Finset.mem_Icc] at hk hnot
      omega
    simp [hzero]

theorem psi_measurable : Measurable Chebyshev.psi := by
  have he : Chebyshev.psi = (fun n : ℕ =>
      ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) ∘ Nat.floor := by
    funext x
    exact (sum_vonMangoldt_Icc x).symm
  rw [he]
  exact (measurable_of_countable _).comp Nat.measurable_floor

theorem vonMangoldt_partialSum_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  apply IsBigO.of_bound (Real.log 4 + 4)
  filter_upwards [] with n
  have he : (∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) =
      Chebyshev.psi (n : ℝ) := by
    simpa only [Nat.floor_natCast] using sum_vonMangoldt_Icc (n : ℝ)
  rw [he, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)

theorem psi_mellin_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hm : Measurable (fun x : ℝ =>
      (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1))) :=
    (Complex.continuous_ofReal.measurable.comp psi_measurable).mul
      (Complex.continuous_ofReal.measurable.pow_const _)
  have hi := (integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re < -1) (by norm_num : (0 : ℝ) < 1)).const_mul (Real.log 4 + 4)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
  have he : x * x ^ (-(s.re + 1)) = x ^ (-s.re) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (-(s.re + 1)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  calc
    _ ≤ ((Real.log 4 + 4) * x) * x ^ (-(s.re + 1)) :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hx0.le)
        (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [mul_assoc, he]

theorem psi_mellin_identity {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      -deriv riemannZeta s / (s * riemannZeta s) := by
  have h := LSeries_eq_mul_integral_of_nonneg ArithmeticFunction.vonMangoldt
    (by norm_num : (0 : ℝ) ≤ 1) hs vonMangoldt_partialSum_isBigO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg)
  have he (x : ℝ) : (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) =
      (Chebyshev.psi x : ℂ) := by
    rw [← Complex.ofReal_sum, sum_vonMangoldt_Icc]
  simp_rw [he] at h
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at h
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  calc
    _ = (-deriv riemannZeta s / riemannZeta s) / s := by
      apply (eq_div_iff hs0).2
      simpa only [mul_comm] using h.symm
    _ = _ := by rw [div_div, mul_comm]

theorem linear_mellin_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  calc
    _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
    _ = (x : ℂ) ^ (1 + -(s + 1)) := (Complex.cpow_add _ _ hx0).symm
    _ = _ := by congr 1; ring

theorem linear_mellin_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hi := integrableOn_Ioi_cpow_of_lt
    (by simpa using neg_lt_neg hs : (-s).re < -1) (by norm_num : (0 : ℝ) < 1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (linear_mellin_integrand s (lt_trans zero_lt_one hx)).symm

theorem linear_mellin_integral {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), (x : ℂ) * (x : ℂ) ^ (-(s + 1))) = 1 / (s - 1) := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact linear_mellin_integrand s (lt_trans zero_lt_one hx)
    _ = _ := by
      rw [integral_Ioi_cpow_of_lt
        (by simpa using neg_lt_neg hs : (-s).re < -1) (by norm_num : (0 : ℝ) < 1)]
      simp only [Complex.ofReal_one, Complex.one_cpow]
      rw [show -s + 1 = -(s - 1) by ring, div_neg]
      ring

def errorMellin (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), ((Chebyshev.psi x : ℂ) - (x : ℂ)) *
    (x : ℂ) ^ (-(s + 1))

def meromorphicError (s : ℂ) : ℂ :=
  -deriv riemannZeta s / (s * riemannZeta s) - 1 / (s - 1)

theorem error_mellin_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => ((Chebyshev.psi x : ℂ) - (x : ℂ)) *
      (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  apply ((psi_mellin_integrable hs).sub (linear_mellin_integrable hs)).congr
  filter_upwards [] with x
  dsimp
  ring

theorem error_mellin_identity {s : ℂ} (hs : 1 < s.re) :
    errorMellin s = meromorphicError s := by
  unfold errorMellin meromorphicError
  simp_rw [sub_mul]
  rw [integral_sub (psi_mellin_integrable hs) (linear_mellin_integrable hs),
    psi_mellin_identity hs, linear_mellin_integral hs]


end RiemannResearch.RH.ChebyshevMellin
