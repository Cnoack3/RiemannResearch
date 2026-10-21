/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Three-stage mass, drift, and probe interpolation

Source: user-requested signed-sieve investigation, 21 October 2026.
The scalar results apply to the actual sieve slopes and Euler probes. The
Hilbert identity retains every cross term; nonsingularity is not a norm bound.
-/

noncomputable section
namespace RiemannResearch.Analysis.ThreeStageSieve

def determinant (a b c x y z : ℝ) : ℝ :=
  (c - b) * x + (a - c) * y + (b - a) * z

def numeratorOne (b c y z T : ℝ) : ℝ := b * z - c * y + (c - b) * T
def numeratorTwo (a c x z T : ℝ) : ℝ := c * x - a * z + (a - c) * T
def numeratorThree (a b x y T : ℝ) : ℝ := a * y - b * x + (b - a) * T

theorem determinant_matrix (a b c x y z : ℝ) :
    Matrix.det !![1, 1, 1; a, b, c; x, y, z] = determinant a b c x y z := by
  simp [Matrix.det_fin_three, determinant]
  ring

theorem numerator_mass (a b c x y z T : ℝ) :
    numeratorOne b c y z T + numeratorTwo a c x z T +
      numeratorThree a b x y T = determinant a b c x y z := by
  unfold numeratorOne numeratorTwo numeratorThree determinant
  ring

theorem numerator_drift (a b c x y z T : ℝ) :
    a * numeratorOne b c y z T + b * numeratorTwo a c x z T +
      c * numeratorThree a b x y T = 0 := by
  unfold numeratorOne numeratorTwo numeratorThree
  ring

theorem numerator_probe (a b c x y z T : ℝ) :
    x * numeratorOne b c y z T + y * numeratorTwo a c x z T +
      z * numeratorThree a b x y T = T * determinant a b c x y z := by
  unfold numeratorOne numeratorTwo numeratorThree determinant
  ring

theorem cramer_solution (a b c x y z T : ℝ)
    (hD : determinant a b c x y z ≠ 0) :
    let D := determinant a b c x y z
    let u := numeratorOne b c y z T / D
    let v := numeratorTwo a c x z T / D
    let w := numeratorThree a b x y T / D
    u + v + w = 1 ∧ a * u + b * v + c * w = 0 ∧ x * u + y * v + z * w = T := by
  dsimp only
  constructor
  · rw [← add_div, ← add_div, numerator_mass, div_self hD]
  constructor
  · simp only [← mul_div_assoc, ← add_div, numerator_drift, zero_div]
  · simp only [← mul_div_assoc, ← add_div, numerator_probe, mul_div_cancel_right₀ T hD]

theorem cramer_forced (a b c x y z T u v w : ℝ)
    (hm : u + v + w = 1) (hd : a * u + b * v + c * w = 0) (he : x * u + y * v + z * w = T) :
    determinant a b c x y z * u = numeratorOne b c y z T ∧
    determinant a b c x y z * v = numeratorTwo a c x z T ∧
    determinant a b c x y z * w = numeratorThree a b x y T := by
  unfold determinant numeratorOne numeratorTwo numeratorThree
  constructor
  · linear_combination (b * z - c * y) * hm + (y - z) * hd + (c - b) * he
  constructor
  · linear_combination (c * x - a * z) * hm + (z - x) * hd + (a - c) * he
  · linear_combination (a * y - b * x) * hm + (x - y) * hd + (b - a) * he

theorem cramer_unique (a b c x y z T u v w : ℝ)
    (hD : determinant a b c x y z ≠ 0)
    (hm : u + v + w = 1) (hd : a * u + b * v + c * w = 0) (he : x * u + y * v + z * w = T) :
    u = numeratorOne b c y z T / determinant a b c x y z ∧
    v = numeratorTwo a c x z T / determinant a b c x y z ∧
    w = numeratorThree a b x y T / determinant a b c x y z := by
  obtain ⟨hu, hv, hw⟩ := cramer_forced a b c x y z T u v w hm hd he
  exact ⟨(eq_div_iff hD).mpr (by nlinarith [hu]),
    (eq_div_iff hD).mpr (by nlinarith [hv]),
    (eq_div_iff hD).mpr (by nlinarith [hw])⟩

theorem singular_solvable_iff (a b c x y z T : ℝ)
    (hab : a - b ≠ 0) (hD : determinant a b c x y z = 0) :
    (∃ u v w : ℝ, u + v + w = 1 ∧ a * u + b * v + c * w = 0 ∧ x * u + y * v + z * w = T) ↔
      a * y - b * x = (a - b) * T := by
  constructor
  · rintro ⟨u, v, w, hm, hd, he⟩
    have h := (cramer_forced a b c x y z T u v w hm hd he).2.2
    rw [hD, zero_mul] at h
    unfold numeratorThree at h
    nlinarith
  · intro h
    refine ⟨-b / (a - b), a / (a - b), 0, ?_, ?_, ?_⟩
    · field_simp
      ring
    · ring
    · calc
        _ = (a * y - b * x) / (a - b) := by ring
        _ = T := (div_eq_iff hab).mpr (by nlinarith [h])

theorem alternating_of_positive_determinant (a b c x y z T : ℝ)
    (hD : 0 < determinant a b c x y z)
    (h12 : (a - b) * T < a * y - b * x)
    (h13 : (a - c) * T < a * z - c * x)
    (h23 : (b - c) * T < b * z - c * y) :
    0 < numeratorOne b c y z T / determinant a b c x y z ∧
    numeratorTwo a c x z T / determinant a b c x y z < 0 ∧
    0 < numeratorThree a b x y T / determinant a b c x y z := by
  unfold numeratorOne numeratorTwo numeratorThree
  exact ⟨div_pos (by nlinarith) hD, div_neg_of_neg_of_pos (by nlinarith) hD,
    div_pos (by nlinarith) hD⟩

theorem alternating_of_negative_determinant (a b c x y z T : ℝ)
    (hD : determinant a b c x y z < 0)
    (h12 : (a - b) * T < a * y - b * x)
    (h13 : (a - c) * T < a * z - c * x)
    (h23 : (b - c) * T < b * z - c * y) :
    numeratorOne b c y z T / determinant a b c x y z < 0 ∧
    0 < numeratorTwo a c x z T / determinant a b c x y z ∧
    numeratorThree a b x y T / determinant a b c x y z < 0 := by
  unfold numeratorOne numeratorTwo numeratorThree
  exact ⟨div_neg_of_pos_of_neg (by nlinarith) hD,
    div_pos_of_neg_of_neg (by nlinarith) hD, div_neg_of_pos_of_neg (by nlinarith) hD⟩

theorem totalVariation_exact (a b c x y z T : ℝ) :
    |numeratorOne b c y z T / determinant a b c x y z| +
    |numeratorTwo a c x z T / determinant a b c x y z| +
    |numeratorThree a b x y T / determinant a b c x y z| =
    (|numeratorOne b c y z T| + |numeratorTwo a c x z T| +
      |numeratorThree a b x y T|) / |determinant a b c x y z| := by
  simp only [abs_div, add_div]

theorem prefix_probe (u v w x y z : ℝ) (hm : u + v + w = 1) :
    u * x + v * y + w * z = z + u * (x - y) + (u + v) * (y - z) := by
  nlinarith [congrArg (fun t : ℝ => t * z) hm]

/-- The two cumulative coefficients, rather than coefficient variation, control
the probe once physical jumps have bounded them. -/
theorem prefix_probe_bound (u v w x y z M1 M2 : ℝ)
    (hm : u + v + w = 1) (hyx : y ≤ x) (hzy : z ≤ y)
    (hu : |u| ≤ M1) (hv : |u + v| ≤ M2) :
    |u * x + v * y + w * z - z| ≤ M1 * (x - y) + M2 * (y - z) := by
  rw [prefix_probe u v w x y z hm]
  have he : z + u * (x - y) + (u + v) * (y - z) - z = u * (x - y) + (u + v) * (y - z) := by ring
  rw [he]
  calc
    _ ≤ |u * (x - y)| + |(u + v) * (y - z)| := abs_add_le _ _
    _ = |u| * (x - y) + |u + v| * (y - z) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hyx),
        abs_of_nonneg (sub_nonneg.mpr hzy)]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right hu (sub_nonneg.mpr hyx))
      (mul_le_mul_of_nonneg_right hv (sub_nonneg.mpr hzy))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- All three off-diagonal inner products remain explicit. -/
theorem complete_gram (A B C : H) (u v w : ℝ) :
    ‖u • A + v • B + w • C‖ ^ 2 =
    u ^ 2 * ‖A‖ ^ 2 + v ^ 2 * ‖B‖ ^ 2 + w ^ 2 * ‖C‖ ^ 2 +
    2 * u * v * inner ℝ A B + 2 * u * w * inner ℝ A C + 2 * v * w * inner ℝ B C := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm B A, real_inner_comm C A, real_inner_comm C B]
  ring

theorem cramer_complete_gram (A B C : H) (D N1 N2 N3 : ℝ) :
    ‖(N1 / D) • A + (N2 / D) • B + (N3 / D) • C‖ ^ 2 =
    (N1 ^ 2 * ‖A‖ ^ 2 + N2 ^ 2 * ‖B‖ ^ 2 + N3 ^ 2 * ‖C‖ ^ 2 +
      2 * N1 * N2 * inner ℝ A B + 2 * N1 * N3 * inner ℝ A C +
      2 * N2 * N3 * inner ℝ B C) / D ^ 2 := by
  rw [complete_gram]
  ring

/-- Exact target error, including the three target correlations. -/
theorem cramer_error_gram (A B C F : H) (D N1 N2 N3 : ℝ) :
    ‖(N1 / D) • A + (N2 / D) • B + (N3 / D) • C - F‖ ^ 2 =
    (N1 ^ 2 * ‖A‖ ^ 2 + N2 ^ 2 * ‖B‖ ^ 2 + N3 ^ 2 * ‖C‖ ^ 2 +
      2 * N1 * N2 * inner ℝ A B + 2 * N1 * N3 * inner ℝ A C +
      2 * N2 * N3 * inner ℝ B C) / D ^ 2 -
      2 * (N1 * inner ℝ A F + N2 * inner ℝ B F + N3 * inner ℝ C F) / D + ‖F‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm B A, real_inner_comm C A, real_inner_comm C B,
    real_inner_comm F A, real_inner_comm F B, real_inner_comm F C]
  ring

end RiemannResearch.Analysis.ThreeStageSieve
