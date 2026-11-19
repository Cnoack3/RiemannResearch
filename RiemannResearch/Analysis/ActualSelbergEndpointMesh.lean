/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSelbergDensityInterpolation
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Integer strikes for the moving Selberg endpoint window

The analytic target of Baluyot, Theorem 1.2.1 and §3.6, is the inclusive
count with a single logarithm. The fixed-parameter theorem holds strictly
below the endpoint. The monotonicity argument below needs a common constant
only at integer microscopic strikes through (21/2) log log T.
<https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320>
-/

noncomputable section
open Filter Set
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- A common constant for the finite list of physical strikes at each height. -/
def SelbergEndpointIntegerWindow : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ k : ℕ,
    (k : ℝ) ≤ (21 / 2) * Real.log (Real.log T) → (k : ℝ) ≤ Real.log T / 2 →
    rightInclusiveCount T (1 / 2 + (k : ℝ) / Real.log T) ≤
      C * (T * Real.log T) * Real.exp (-(8 / 7) * (k : ℝ))

/-- Rounding down preserves all threshold occurrences and costs at most e^(8/7). -/
theorem endpoint_density_iff_integer_window :
    UniformSelbergDensity (8 / 7) ↔ SelbergEndpointIntegerWindow := by
  rw [endpoint_density_iff_window]
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C,hC,?_⟩
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hd ht k hw hk
    have hL := Real.log_pos ht
    have hhalf := (div_le_iff₀ hL).mpr (by linarith only [hk] :
      (k : ℝ) ≤ (1 / 2) * Real.log T)
    have hσ : 1 / 2 + (k : ℝ) / Real.log T ∈ Icc (1 / 2 : ℝ) 1 :=
      ⟨le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hL.le), by linarith⟩
    have hex : Real.log T * ((1 / 2 + (k : ℝ) / Real.log T) - 1 / 2) = k := by field_simp [hL.ne'] <;> ring
    have hcount := hd _ hσ (by rw [hex]; exact hw)
    rw [selberg_power_kernel_eq_exp T _ _ (zero_lt_one.trans ht)] at hcount
    apply hcount.trans_eq
    rw [show -(8 / 7 * Real.log T) * ((1 / 2 + (k : ℝ) / Real.log T) - 1 / 2) =
      -(8 / 7) * (k : ℝ) by
      calc
        _ = -(8 / 7) * (Real.log T * ((1 / 2 + (k : ℝ) / Real.log T) - 1 / 2)) := by ring
        _ = _ := by rw [hex]]
    ring
  · rintro ⟨C,hC,h⟩
    refine ⟨C * Real.exp (8 / 7), mul_nonneg hC (Real.exp_pos _).le, ?_⟩
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hd ht σ hσ hw
    have hL := Real.log_pos ht
    let x := Real.log T * (σ - 1 / 2)
    have hx : 0 ≤ x := mul_nonneg hL.le (sub_nonneg.mpr hσ.1)
    let k := ⌊x⌋₊
    have hk : (k : ℝ) ≤ x := Nat.floor_le hx
    have hk' : x < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hhalf : x ≤ Real.log T / 2 := by
      dsimp [x]
      nlinarith only [mul_nonneg hL.le (sub_nonneg.mpr hσ.2)]
    have hleft : 1 / 2 + (k : ℝ) / Real.log T ≤ σ := by
      have hh := (div_le_iff₀ hL).mpr (show (k : ℝ) ≤ (σ - 1 / 2) * Real.log T by
        simpa only [x, mul_comm] using hk)
      linarith
    apply ((rightInclusiveCount_antitone T hleft).trans (hd k (hk.trans hw) (hk.trans hhalf))).trans
    rw [selberg_power_kernel_eq_exp T _ _ (zero_lt_one.trans ht)]
    have he : Real.exp (-(8 / 7) * (k : ℝ)) ≤
        Real.exp (8 / 7) * Real.exp (-(8 / 7 * Real.log T) * (σ - 1 / 2)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      dsimp only [x] at hk'
      linarith only [hk']
    calc
      _ ≤ C * (T * Real.log T) * (Real.exp (8 / 7) * Real.exp (-(8 / 7 * Real.log T) * (σ - 1 / 2))) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring

/-- Logarithms of the two off-diagonal errors in Baluyot (3.6.2) under a
moving mollifier. Here U = log T / log log T and K U is the logarithm
of the allowed residual factor. -/
theorem baluyot_moving_error_exponents (L U B D K : ℝ) :
    let y := (4 / 7) * L - B * U
    (-L / 2 + (7 / 2) * D * U + K * U + (7 / 8) * y = (K + 7 * D / 2 - 7 * B / 8) * U) ∧
    (-L + (7 / 2) * D * U + K * U + (7 / 4) * y = (K + 7 * D / 2 - 7 * B / 4) * U) := by
  dsimp only
  constructor <;> ring

end RiemannResearch.Analysis.ActualZeroOrdinate
