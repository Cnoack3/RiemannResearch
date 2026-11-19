/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.FiniteSizeBiasedSharpness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exponential majorants and sharp real-order moments for a two-atom law -/

namespace RiemannResearch.Analysis.FiniteSizeBiasedExponential

theorem rpow_le_exp_multiple {v h x : ℝ} (hv : 0 < v) (hh : 0 < h) (hx : 0 ≤ x) :
    x ^ v ≤ (v / h) ^ v * Real.exp (h * x) := by
  let z := h * x / v
  have hbase : x ≤ (v / h) * Real.exp z := by
    calc
      x = (v / h) * z := by dsimp [z]; field_simp [hh.ne', hv.ne'] <;> ring
      _ ≤ (v / h) * Real.exp z := mul_le_mul_of_nonneg_left
        (by linarith only [Real.add_one_le_exp z]) (div_nonneg hv.le hh.le)
  apply (Real.rpow_le_rpow hx hbase hv.le).trans_eq
  rw [Real.mul_rpow (div_nonneg hv.le hh.le) (Real.exp_pos _).le,
    ← Real.exp_mul, show z * v = h * x from div_mul_cancel₀ _ hv.ne']

/-- For the two-atom law of the sharp second-moment witness, the ratio
at every real order s>1 is exactly the corresponding power of 1/A. -/
theorem two_atom_realOrder_reciprocal_sharp {A z s : ℝ} (hA : 0 < A) (hz : 1 ≤ z)
    (hs : 1 < s) :
    let m := Real.exp (-(A * z))
    let p := m / z
    ((1 - p) * (0 : ℝ) ^ s + p * z ^ s) / (m * Real.log (1 / m) ^ (s - 1)) = (1 / A) ^ (s - 1) := by
  dsimp only
  let m := Real.exp (-(A * z))
  let p := m / z
  have hM : 0 < m := Real.exp_pos _
  have hz' := zero_lt_one.trans_le hz
  have hmean : p * z = m := div_mul_cancel₀ _ hz'.ne'
  have hlog : Real.log (1 / m) = A * z := by
    rw [Real.log_div one_ne_zero hM.ne', Real.log_one]
    dsimp only [m]
    rw [Real.log_exp]
    ring
  change ((1 - p) * 0 ^ s + p * z ^ s) / (m * Real.log (1 / m) ^ (s - 1)) = (1 / A) ^ (s - 1)
  rw [Real.zero_rpow (by linarith : s ≠ 0), mul_zero, zero_add, hlog,
    Real.mul_rpow hA.le hz'.le, Real.div_rpow zero_le_one hA.le, Real.one_rpow]
  have hzpow : z ^ s = z * z ^ (s - 1) := by
    calc
      _ = z ^ (1 + (s - 1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hz', Real.rpow_one]
  rw [hzpow, ← mul_assoc p, hmean]
  field_simp [hM.ne', (Real.rpow_pos_of_pos hz' (s - 1)).ne',
    (Real.rpow_pos_of_pos hA (s - 1)).ne'] <;> ring

end RiemannResearch.Analysis.FiniteSizeBiasedExponential
