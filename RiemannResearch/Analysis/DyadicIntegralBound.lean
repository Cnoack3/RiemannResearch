/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Dyadic assembly with a monotone weight

A dyadic increment bound of size `D * U * W U` gives a global bound of
size `C * T * W T`, with the finite initial interval retained explicitly.
The weight can be any nonnegative monotone function on the relevant half-line.
In particular `W T = (log T)^q` incurs no extra logarithm.

Source: elementary dyadic induction, developed for the actual-zeta
fourth-moment continuation in
`THEOREM_CATALOG_INGHAM_FOURTH_MOMENT_REDUCTION_20261116.md`.
-/
noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis

/-- Exact telescoping identity for the dyadic increment of an integral. -/
theorem integral_dyadic_increment (f : ℝ → ℝ) (hf : Continuous f) (U : ℝ) :
    (∫ t in (0 : ℝ)..2 * U, f t) - (∫ t in (0 : ℝ)..U, f t) =
      ∫ t in U..2 * U, f t := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 U) (hf.intervalIntegrable U (2 * U))
  linarith

/-- No loss in the weight when summing dyadic increments; the head cost is explicit. -/
theorem bound_of_dyadic_linear_weight (F W : ℝ → ℝ) {H D C : ℝ}
    (hH : 0 < H) (hC : 0 ≤ C) (hDC : D ≤ C)
    (hmono : MonotoneOn F (Set.Ici H))
    (hW : MonotoneOn W (Set.Ici H))
    (hW0 : ∀ T ≥ H, 0 ≤ W T)
    (hhead : F (2 * H) ≤ C * H * W H)
    (hwindow : ∀ U ≥ H, F (2 * U) - F U ≤ D * U * W U) :
    ∀ T ≥ H, F T ≤ C * T * W T := by
  have hsmall : ∀ T ≥ H, T ≤ 2 * H → F T ≤ C * T * W T := by
    intro T hT hThi
    have hT0 : 0 < T := hH.trans_le hT
    calc
      F T ≤ F (2 * H) := hmono hT (by change H ≤ 2 * H; linarith) hThi
      _ ≤ C * H * W H := hhead
      _ ≤ C * T * W T := mul_le_mul
        (mul_le_mul_of_nonneg_left hT hC) (hW (show H ∈ Set.Ici H from le_refl H) hT hT)
        (hW0 H le_rfl) (by positivity)
  have hind : ∀ n : ℕ, ∀ T ≥ H, T ≤ H * 2 ^ n → F T ≤ C * T * W T := by
    intro n
    induction n with
    | zero =>
        intro T hT hu
        apply hsmall T hT
        norm_num at hu
        linarith
    | succ n ih =>
        intro T hT hu
        by_cases hs : T ≤ 2 * H
        · exact hsmall T hT hs
        have hhalf : H ≤ T / 2 := by linarith
        have hhalf0 : 0 < T / 2 := hH.trans_le hhalf
        have hhalfhi : T / 2 ≤ H * 2 ^ n := by
          rw [pow_succ] at hu
          linarith
        have hi := ih (T / 2) hhalf hhalfhi
        have hw := hwindow (T / 2) hhalf
        rw [show 2 * (T / 2) = T by ring] at hw
        have hw' : F T - F (T / 2) ≤ C * (T / 2) * W (T / 2) :=
          hw.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hDC (by linarith)) (hW0 _ hhalf))
        have hweight := mul_le_mul_of_nonneg_left
          (hW hhalf hT (by linarith : T / 2 ≤ T))
          (show 0 ≤ C * (T / 2) by positivity)
        nlinarith
  intro T hT
  obtain ⟨n, _, hn⟩ := exists_nat_pow_near
    ((one_le_div hH).mpr hT) (show (1 : ℝ) < 2 by norm_num)
  apply hind (n + 1) T hT
  exact ((div_lt_iff₀ hH).mp hn).le.trans_eq (mul_comm _ _)

/-- A continuous nonnegative integrand is controlled by its dyadic windows. -/
theorem integral_bound_of_dyadic_linear_weight
    (f W : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {H D C : ℝ} (hH : 0 < H) (hC : 0 ≤ C) (hDC : D ≤ C)
    (hW : MonotoneOn W (Set.Ici H)) (hW0 : ∀ T ≥ H, 0 ≤ W T)
    (hhead : (∫ t in (0 : ℝ)..2 * H, f t) ≤ C * H * W H)
    (hwindow : ∀ U ≥ H, (∫ t in U..2 * U, f t) ≤ D * U * W U) :
    ∀ T ≥ H, (∫ t in (0 : ℝ)..T, f t) ≤ C * T * W T := by
  refine bound_of_dyadic_linear_weight (fun T => ∫ t in (0 : ℝ)..T, f t) W
    hH hC hDC ?_ hW hW0 hhead ?_
  · intro a ha b hb hab
    exact intervalIntegral.integral_mono_interval le_rfl (hH.le.trans ha) hab
      (Filter.Eventually.of_forall hf0) (hf.intervalIntegrable 0 b)
  · intro U hU
    rw [integral_dyadic_increment f hf U]
    exact hwindow U hU

end RiemannResearch.Analysis
