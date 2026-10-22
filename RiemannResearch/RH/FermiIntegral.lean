import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The first Fermi integral

Source: `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §6,
where this integral supplies the exact conditional-variance constant.

The Bose integral is evaluated by an absolutely integrable geometric series,
using the Gamma integral and the proved value of zeta at two.  The identity
`x/(exp x+1) = x/(exp x-1) - (2*x)/(exp(2*x)-1)` then gives the Fermi integral.
-/

open scoped BigOperators
open MeasureTheory Set Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

private def boseTerm (n : ℕ) (x : ℝ) : ℝ :=
  x * Real.exp (-((n : ℝ)+1)*x)

private theorem integral_boseTerm (n : ℕ) :
    (∫ x : ℝ in Ioi 0, boseTerm n x) = 1 / ((n : ℝ)+1)^2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := (n : ℝ)+1) (by norm_num) (by positivity)
  have hg : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  simpa only [boseTerm, show (2 : ℝ)-1 = 1 by norm_num,
    Real.rpow_one, Real.rpow_two, hg, mul_one, one_div_pow, neg_mul] using h

private theorem integrable_boseTerm (n : ℕ) :
    IntegrableOn (boseTerm n) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_boseTerm]
  positivity

private theorem tsum_boseTerm {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, boseTerm n x) = x / (Real.exp x-1) := by
  have hr : ‖Real.exp (-x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_norm_lt_one hr).mul_left (x * Real.exp (-x))
  have he (n : ℕ) : boseTerm n x =
      (x * Real.exp (-x)) * Real.exp (-x)^n := by
    unfold boseTerm
    rw [show -((n : ℝ)+1)*x = -x + (n : ℝ)*(-x) by ring,
      Real.exp_add, Real.exp_nat_mul]
    ring
  have hpos : 0 < Real.exp x-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  have hneg : 1 - Real.exp (-x) ≠ 0 := by
    have hlt : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  calc
    _ = ∑' n : ℕ, (x * Real.exp (-x)) * Real.exp (-x)^n := tsum_congr he
    _ = (x * Real.exp (-x)) * (1 - Real.exp (-x))⁻¹ := h.tsum_eq
    _ = x / (Real.exp x-1) := by
      rw [Real.exp_neg]
      have hE := (Real.exp_pos x).ne'
      have hm : 1 - (Real.exp x)⁻¹ ≠ 0 := by simpa only [Real.exp_neg] using hneg
      field_simp [hE, hm, hpos.ne']
      <;> ring

private theorem hasSum_shifted_zeta_two :
    HasSum (fun n : ℕ => 1 / ((n : ℝ)+1)^2) (Real.pi^2/6) := by
  have h0 : (∑ n ∈ Finset.range 1, (1 : ℝ) / (n : ℝ)^2) = 0 := by norm_num
  have hz : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ)^2)
      (Real.pi^2/6 + ∑ n ∈ Finset.range 1, (1 : ℝ) / (n : ℝ)^2) := by
    rw [h0, add_zero]
    exact hasSum_zeta_two
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^2) 1).mpr hz
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Exact first Bose integral, with interchange justified by absolute convergence. -/
theorem integral_bose_first :
    (∫ x : ℝ in Ioi 0, x / (Real.exp x-1)) = Real.pi^2/6 := by
  have hnorm (n : ℕ) : (∫ x : ℝ in Ioi 0, ‖boseTerm n x‖) =
      1 / ((n : ℝ)+1)^2 := by
    calc
      _ = ∫ x : ℝ in Ioi 0, boseTerm n x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change ‖boseTerm n x‖ = boseTerm n x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact mul_nonneg hx.le (Real.exp_pos _).le
      _ = _ := integral_boseTerm n
  have hn : Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0, ‖boseTerm n x‖) := by
    simpa only [hnorm] using hasSum_shifted_zeta_two.summable
  have h := integral_tsum_of_summable_integral_norm integrable_boseTerm hn
  calc
    _ = ∫ x : ℝ in Ioi 0, ∑' n : ℕ, boseTerm n x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (tsum_boseTerm hx).symm
    _ = ∑' n : ℕ, ∫ x : ℝ in Ioi 0, boseTerm n x := h.symm
    _ = Real.pi^2/6 := by
      simpa only [integral_boseTerm] using hasSum_shifted_zeta_two.tsum_eq

/-- Integrability follows from the exact nonzero Bose integral. -/
theorem integrable_bose_first :
    IntegrableOn (fun x : ℝ => x / (Real.exp x-1)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_bose_first]
  positivity

private theorem integral_bose_first_double :
    (∫ x : ℝ in Ioi 0, (2*x) / (Real.exp (2*x)-1)) = Real.pi^2/12 := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => x/(Real.exp x-1)) 0
    (b := 2) (by norm_num)
  norm_num only [mul_zero, smul_eq_mul] at h
  rw [integral_bose_first] at h
  convert h using 1 <;> first | rfl | ring

private theorem fermi_bose_difference {x : ℝ} (hx : 0 < x) :
    x / (Real.exp x+1) = x / (Real.exp x-1) -
      (2*x) / (Real.exp (2*x)-1) := by
  have hE : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hm : Real.exp x-1 ≠ 0 := by linarith
  have hp : Real.exp x+1 ≠ 0 := by linarith
  rw [show 2*x = x+x by ring, Real.exp_add]
  rw [show Real.exp x * Real.exp x-1 = (Real.exp x-1)*(Real.exp x+1) by ring]
  field_simp [hm, hp]
  <;> ring

/-- The exact first Fermi integral. -/
theorem integral_fermi_first :
    (∫ x : ℝ in Ioi 0, x / (Real.exp x+1)) = Real.pi^2/12 := by
  have hi : IntegrableOn (fun x : ℝ => (2*x)/(Real.exp (2*x)-1)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_bose_first_double]
    positivity
  calc
    _ = ∫ x : ℝ in Ioi 0, x / (Real.exp x-1) - (2*x)/(Real.exp (2*x)-1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact fermi_bose_difference hx
    _ = (∫ x : ℝ in Ioi 0, x / (Real.exp x-1)) -
        ∫ x : ℝ in Ioi 0, (2*x)/(Real.exp (2*x)-1) :=
      integral_sub integrable_bose_first hi
    _ = Real.pi^2/12 := by
      rw [integral_bose_first, integral_bose_first_double]
      ring

/-- Integrability of the first Fermi profile on the positive half-line. -/
theorem integrable_fermi_first :
    IntegrableOn (fun x : ℝ => x / (Real.exp x+1)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_fermi_first]
  positivity

end
end RiemannResearch.RH.Pareto
