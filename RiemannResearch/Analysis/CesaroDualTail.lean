/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinCesaroSummability
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Quantitative infinite dual-tail bounds, retaining the exact Pareto mixture weights. -/
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.ArithmeticCumulative

/-- The strict p-series tail is bounded by its actual improper integral. -/
theorem nat_rpow_tail_le (p : ℝ) (hp : 1 < p) (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-p)) ≤
      (N : ℝ) ^ (1 - p) / (p - 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : AntitoneOn (fun x : ℝ => x ^ (-p)) (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNR.trans_le hx) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hNR
  have h := AntitoneOn.tsum_comp_add_le_integral N ha hi
    (fun x hx => Real.rpow_nonneg (le_of_lt (hNR.trans hx)) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hNR] at h
  convert h using 1
  rw [show -p + 1 = 1 - p by ring]
  have hp0 : p - 1 ≠ 0 := by linarith
  have hp1 : 1 - p ≠ 0 := by linarith
  field_simp [hp0, hp1]
  ring

/-- The dual energy beyond the exact positive head 1,...,N. -/
def dualTail (s : ℂ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, ‖mellinSecond s (k + N + 1)‖ ^ 2 / conditionalWeight (k + N)

theorem dualTail_nonneg (s : ℂ) (N : ℕ) : 0 ≤ dualTail s N :=
  tsum_nonneg (fun k => div_nonneg (sq_nonneg _) (conditionalWeight_pos _).le)

theorem dualTail_summable (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (N : ℕ) :
    Summable (fun k : ℕ => ‖mellinSecond s (k + N + 1)‖ ^ 2 /
      conditionalWeight (k + N)) :=
  (mellinSecond_dual_summable s hs).comp_injective (fun _ _ h => Nat.add_right_cancel h)

/-- The explicit tail bound, with exponent 1 - 2 Re(s) and the full dual weight. -/
theorem dualTail_le (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (N : ℕ) (hN : 0 < N) :
    dualTail s N ≤
      (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) * (N : ℝ) ^ (1 - 2 * s.re) := by
  have hp : Summable (fun k : ℕ => ((k + N + 1 : ℕ) : ℝ) ^ (-(2 * s.re))) :=
    (Real.summable_nat_rpow.mpr (by linarith : -(2 * s.re) < -1)).comp_injective
      (fun _ _ h => Nat.add_right_cancel (Nat.add_right_cancel h))
  have hb := Summable.tsum_le_tsum
    (fun k => mellinSecond_dual_term_le s (by linarith) (k + N + 1) (by omega))
    (dualTail_summable s hs N) (hp.mul_left (3 * ‖s * (s + 1)‖ ^ 2))
  change dualTail s N ≤ _ at hb
  rw [tsum_mul_left] at hb
  calc
    dualTail s N ≤ 3 * ‖s * (s + 1)‖ ^ 2 *
        (∑' k : ℕ, ((k + N + 1 : ℕ) : ℝ) ^ (-(2 * s.re))) := hb
    _ ≤ 3 * ‖s * (s + 1)‖ ^ 2 *
        ((N : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)) :=
      mul_le_mul_of_nonneg_left (nat_rpow_tail_le (2 * s.re) (by linarith) N hN)
        (by positivity)
    _ = _ := by ring

end RiemannResearch.Analysis.Cesaro
