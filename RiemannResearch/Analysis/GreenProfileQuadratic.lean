import RiemannResearch.Analysis.GreenProfileBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Strict quadratic profile budgets
Source: continuation of the user-provided exact-head Green profile agenda,
16 November 2026. This scalar strengthening allows a quadratic energy term
strictly below the squared signed-moment margin. It provides no analytic
uniform bound for the actual optimizer.
-/

namespace RiemannResearch.Analysis.GreenProfileBounds
private theorem le_sum_of_sq_le {u v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t)
    (h : u ^ 2 ≤ v ^ 2 + t ^ 2) : u ≤ v + t := by
  by_contra! hh
  nlinarith [mul_nonneg hv ht]

/-- A strict quadratic gap is sufficient. The profile budget may contain
k^2 q^2; only k < delta is required. All signs in the moment are retained. -/
theorem energy_scaled_le_of_quadratic_profile_deficit
    {q r tau m δ k C a B : ℝ} (hq : 0 ≤ q) (hk : 0 ≤ k) (hgap : k < δ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hr : r = q + tau)
    (ht : tau ^ 2 ≤ a * q) (he : (r - m) ^ 2 ≤ k ^ 2 * q ^ 2 + C * q)
    (hm : m ≤ (1 - δ) * q + B) :
    (δ - k) ^ 2 * q ≤ 2 * (δ - k) * B + 2 * C + 2 * a := by
  have hCq : (Real.sqrt C * Real.sqrt q) ^ 2 = C * q := by
    rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hq]
  have haq : (Real.sqrt a * Real.sqrt q) ^ 2 = a * q := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hq]
  have he' : r - m ≤ k * q + Real.sqrt C * Real.sqrt q :=
    le_sum_of_sq_le (mul_nonneg hk hq) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by rw [hCq]; nlinarith only [he])
  have ht' : -tau ≤ Real.sqrt a * Real.sqrt q := by
    have h := le_sum_of_sq_le (u := -tau) (v := 0)
      (t := Real.sqrt a * Real.sqrt q) (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by rw [haq]; nlinarith only [ht])
    simpa using h
  have hlin : (δ - k) * q ≤ B + (Real.sqrt C + Real.sqrt a) * Real.sqrt q := by
    nlinarith only [he', ht', hr, hm]
  have hh := mul_le_mul_of_nonneg_left hlin
    (show 0 ≤ 2 * (δ - k) by linarith)
  have hsq := sq_nonneg ((δ - k) * Real.sqrt q - (Real.sqrt C + Real.sqrt a))
  have hc := Real.sq_sqrt hC
  have ha' := Real.sq_sqrt ha
  have hq' := Real.sq_sqrt hq
  have hcross := sq_nonneg (Real.sqrt C - Real.sqrt a)
  nlinarith

end RiemannResearch.Analysis.GreenProfileBounds
