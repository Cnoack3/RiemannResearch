import RiemannResearch.Analysis.AbelCoboundary
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Quantitative Abel bounds for square-root orbit growth.

Source: user-provided two-seed handoff, (N22)--(N23). The tangent inequality
`2 * sqrt δ * sqrt (n+1) ≤ δ * (n+1) + 1` proves the same sharp scalar estimate
as weighted Cauchy--Schwarz, while keeping all scalar moments exact.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.AbelCoboundary

theorem hasSum_geometric_succ_moment (r : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => r ^ n * ((n : ℝ) + 1)) (1 / (1 - r) ^ 2) := by
  have hr1 : r ≠ 1 := by
    intro h
    simp [h] at hr
  have hne : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.symm
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one hr).add
    (hasSum_geometric_of_norm_lt_one hr)
  have hpoint : (fun n : ℕ => (n : ℝ) * r ^ n + r ^ n) =
      (fun n : ℕ => r ^ n * ((n : ℝ) + 1)) := by
    funext n
    ring
  have hvalue : r / (1 - r) ^ 2 + (1 - r)⁻¹ = 1 / (1 - r) ^ 2 := by
    field_simp [hne]
    ring
  rw [hpoint, hvalue] at hsum
  exact hsum

theorem summable_geometric_sqrt (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => r ^ n * Real.sqrt ((n : ℝ) + 1)) := by
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hr0 n) (Real.sqrt_nonneg _))
    (fun n => ?_) (hasSum_geometric_succ_moment r hrnorm).summable
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 n)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hsn := Real.sqrt_nonneg ((n : ℝ) + 1)
  nlinarith

/-- Exact scalar Abel bound, expressed without division on the left. -/
theorem geometric_sqrt_scaled_tsum_le_one
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 - r) * Real.sqrt (1 - r) *
      (∑' n : ℕ, r ^ n * Real.sqrt ((n : ℝ) + 1)) ≤ 1 := by
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  have hδne : 1 - r ≠ 0 := ne_of_gt hδ
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs := summable_geometric_sqrt r hr0 hr1
  have hm := hasSum_geometric_succ_moment r hrnorm
  have hg := hasSum_geometric_of_norm_lt_one hrnorm
  have hpoint (n : ℕ) :
      (2 * Real.sqrt (1 - r)) * (r ^ n * Real.sqrt ((n : ℝ) + 1)) ≤
        (1 - r) * (r ^ n * ((n : ℝ) + 1)) + r ^ n := by
    have hprod : (Real.sqrt (1 - r) * Real.sqrt ((n : ℝ) + 1)) ^ 2 =
        (1 - r) * ((n : ℝ) + 1) := by
      rw [mul_pow, Real.sq_sqrt hδ.le, Real.sq_sqrt (by positivity)]
    have ht : 2 * Real.sqrt (1 - r) * Real.sqrt ((n : ℝ) + 1) ≤
        (1 - r) * ((n : ℝ) + 1) + 1 := by
      nlinarith [sq_nonneg (Real.sqrt (1 - r) * Real.sqrt ((n : ℝ) + 1) - 1)]
    have hmul := mul_le_mul_of_nonneg_left ht (pow_nonneg hr0 n)
    nlinarith
  have hleft := hs.hasSum.mul_left (2 * Real.sqrt (1 - r))
  have hright := (hm.mul_left (1 - r)).add hg
  have hsum := hleft.summable.tsum_le_tsum hpoint hright.summable
  rw [hleft.tsum_eq, hright.tsum_eq] at hsum
  have hvalue : (1 - r) * (1 / (1 - r) ^ 2) + (1 - r)⁻¹ = 2 / (1 - r) := by
    field_simp [hδne]
    ring
  rw [hvalue] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum hδ.le
  have hcancel : (1 - r) * (2 / (1 - r)) = 2 := by field_simp [hδne]
  rw [hcancel] at hmul
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem summable_norm_geometric_of_sqrt_growth
    (r C : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (_hC : 0 ≤ C) (v : ℕ → E)
    (hv : ∀ n, ‖v n‖ ≤ C * Real.sqrt ((n : ℝ) + 1)) :
    Summable (fun n : ℕ => ‖r ^ n • v n‖) := by
  have hs := (summable_geometric_sqrt r hr0 hr1).mul_left C
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 n)]
  have hmul := mul_le_mul_of_nonneg_left (hv n) (pow_nonneg hr0 n)
  nlinarith

theorem summable_geometric_of_sqrt_growth
    (r C : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C) (v : ℕ → E)
    (hv : ∀ n, ‖v n‖ ≤ C * Real.sqrt ((n : ℝ) + 1)) :
    Summable (fun n : ℕ => r ^ n • v n) := by
  exact (summable_norm_geometric_of_sqrt_growth r C hr0 hr1 hC v hv).of_norm

omit [CompleteSpace E] in
/-- A complete-norm bound for the actual Abel average. The scalar constant is
exact: square-root orbit growth `C` gives the bound `C / sqrt (1-r)`. -/
theorem norm_average_le_of_sqrt_growth
    (r C : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C) (v : ℕ → E)
    (hv : ∀ n, ‖v n‖ ≤ C * Real.sqrt ((n : ℝ) + 1)) :
    ‖average r v‖ ≤ C / Real.sqrt (1 - r) := by
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  have hspos : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.mpr hδ
  have hs := summable_geometric_sqrt r hr0 hr1
  have hnorm := summable_norm_geometric_of_sqrt_growth r C hr0 hr1 hC v hv
  have hpoint (n : ℕ) : ‖r ^ n • v n‖ ≤
      C * (r ^ n * Real.sqrt ((n : ℝ) + 1)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 n)]
    have hmul := mul_le_mul_of_nonneg_left (hv n) (pow_nonneg hr0 n)
    nlinarith
  have hnormsum := hnorm.tsum_le_tsum hpoint (hs.mul_left C)
  rw [(hs.hasSum.mul_left C).tsum_eq] at hnormsum
  have hfirst : ‖average r v‖ ≤
      (1 - r) * (C * (∑' n : ℕ, r ^ n * Real.sqrt ((n : ℝ) + 1))) := by
    rw [average, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    exact mul_le_mul_of_nonneg_left
      ((norm_tsum_le_tsum_norm hnorm).trans hnormsum) hδ.le
  apply (le_div_iff₀ hspos).mpr
  calc
    ‖average r v‖ * Real.sqrt (1 - r) ≤
        ((1 - r) * (C * (∑' n : ℕ, r ^ n * Real.sqrt ((n : ℝ) + 1)))) *
          Real.sqrt (1 - r) := mul_le_mul_of_nonneg_right hfirst hspos.le
    _ = C * ((1 - r) * Real.sqrt (1 - r) *
        (∑' n : ℕ, r ^ n * Real.sqrt ((n : ℝ) + 1))) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (geometric_sqrt_scaled_tsum_le_one r hr0 hr1) hC
    _ = C := mul_one C

/-- Quantitative coboundary decay used in (N23): square-root orbit growth
implies an explicit `4 C sqrt (1-r)` bound for `1/2 ≤ r < 1`. -/
theorem norm_orbit_average_coboundary_le_sqrt
    (B : E →L[ℝ] E) (r C : ℝ) (hrhalf : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1)
    (hC : 0 ≤ C) (z : E)
    (hv : ∀ n, ‖orbit B z n‖ ≤ C * Real.sqrt ((n : ℝ) + 1)) :
    ‖average r (orbit B (z - B z))‖ ≤ 4 * C * Real.sqrt (1 - r) := by
  have hrpos : 0 < r := by linarith
  have hr0 : 0 ≤ r := hrpos.le
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hδ : 0 < 1 - r := sub_pos.mpr hr1
  have hspos : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.mpr hδ
  have hsne : Real.sqrt (1 - r) ≠ 0 := ne_of_gt hspos
  have hsq : Real.sqrt (1 - r) ^ 2 = 1 - r := Real.sq_sqrt hδ.le
  have hsle : Real.sqrt (1 - r) ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt (1 - r) - 1)]
  have hz0 : ‖z‖ ≤ C := by simpa using hv 0
  have hz := summable_geometric_of_sqrt_growth r C hr0 hr1 hC (orbit B z) hv
  have hshiftgrowth (n : ℕ) :
      ‖orbit B z (n + 1)‖ ≤ (2 * C) * Real.sqrt ((n : ℝ) + 1) := by
    have hroot : Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) ≤
        2 * Real.sqrt ((n : ℝ) + 1) := by
      have hsq₁ := Real.sq_sqrt (show 0 ≤ ((n : ℝ) + 1) by positivity)
      have hsq₂ := Real.sq_sqrt (show 0 ≤ (((n + 1 : ℕ) : ℝ) + 1) by positivity)
      have hs₁ := Real.sqrt_nonneg ((n : ℝ) + 1)
      have hs₂ := Real.sqrt_nonneg (((n + 1 : ℕ) : ℝ) + 1)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      norm_num only [Nat.cast_add, Nat.cast_one] at hsq₂ hs₂ ⊢
      nlinarith
    calc
      ‖orbit B z (n + 1)‖ ≤ C * Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) := hv (n + 1)
      _ ≤ C * (2 * Real.sqrt ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hroot hC
      _ = (2 * C) * Real.sqrt ((n : ℝ) + 1) := by ring
  have hBz := summable_geometric_of_sqrt_growth r (2 * C) hr0 hr1 (by positivity)
    (fun n => orbit B z (n + 1)) hshiftgrowth
  have hmean := norm_average_le_of_sqrt_growth r C hr0 hr1 hC (orbit B z) hv
  have hcoeff : (1 - r) / r ≤ 2 * (1 - r) := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg hδ.le (show 0 ≤ 2 * r - 1 by linarith)]
  have habs : |(1 - r) / r| = (1 - r) / r := abs_of_pos (div_pos hδ hrpos)
  calc
    ‖average r (orbit B (z - B z))‖ ≤
        |(1 - r) / r| * (‖z‖ + ‖average r (orbit B z)‖) :=
      norm_orbit_average_coboundary_le B r hrne z hz hBz
    _ = ((1 - r) / r) * (‖z‖ + ‖average r (orbit B z)‖) := by rw [habs]
    _ ≤ (2 * (1 - r)) * (C + C / Real.sqrt (1 - r)) :=
      mul_le_mul hcoeff (add_le_add hz0 hmean) (by positivity) (by positivity)
    _ = 2 * C * (Real.sqrt (1 - r) ^ 2 + Real.sqrt (1 - r)) := by
      calc
        (2 * (1 - r)) * (C + C / Real.sqrt (1 - r)) =
            2 * C * ((1 - r) + (1 - r) / Real.sqrt (1 - r)) := by ring
        _ = 2 * C * (Real.sqrt (1 - r) ^ 2 +
            Real.sqrt (1 - r) ^ 2 / Real.sqrt (1 - r)) := by rw [hsq]
        _ = 2 * C * (Real.sqrt (1 - r) ^ 2 + Real.sqrt (1 - r)) := by
            field_simp [hsne]
    _ ≤ 4 * C * Real.sqrt (1 - r) := by
      have hsqle : Real.sqrt (1 - r) ^ 2 ≤ Real.sqrt (1 - r) := by
        nlinarith [mul_nonneg hspos.le (sub_nonneg.mpr hsle)]
      nlinarith [mul_le_mul_of_nonneg_left hsqle hC]

end RiemannResearch.Analysis.AbelCoboundary
