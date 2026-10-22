import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quadratic noise-to-signal and paired-weight identities

This module formalizes the scalar and finite-sum algebra in Sections 2 and 3 of
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf` (7 September 2026).
It does not assume an arithmetic identification of the parameters, an infinite
Euler product, or an RH approximation criterion.
-/

namespace RiemannResearch.LinearAlgebra.NoiseSignalQuadratic

open scoped BigOperators
noncomputable section

/-- Completion of the quadratic error after an overall scalar rescaling. -/
theorem scale_error_completion (V m t : ℝ) (hD : V + m ^ 2 ≠ 0) :
    1 - 2 * t * m + t ^ 2 * (V + m ^ 2) =
      V / (V + m ^ 2) + (V + m ^ 2) * (t - m / (V + m ^ 2)) ^ 2 := by
  field_simp [hD]
  <;> ring

theorem scale_error_at_optimum (V m : ℝ) (hD : V + m ^ 2 ≠ 0) :
    1 - 2 * (m / (V + m ^ 2)) * m +
        (m / (V + m ^ 2)) ^ 2 * (V + m ^ 2) = V / (V + m ^ 2) := by
  rw [scale_error_completion V m (m / (V + m ^ 2)) hD]
  simp

/-- The displayed optimum is a global minimum when variance is nonnegative. -/
theorem scale_error_minimum (V m t : ℝ) (hV : 0 ≤ V) (hm : m ≠ 0) :
    V / (V + m ^ 2) ≤ 1 - 2 * t * m + t ^ 2 * (V + m ^ 2) := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hD : 0 < V + m ^ 2 := by linarith
  rw [scale_error_completion V m t (ne_of_gt hD)]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hD) (sq_nonneg _))

/-- Squared residual at the best scale is `R / (1 + R)`, with `R = V / m²`. -/
theorem noise_ratio_conversion (V m : ℝ) (hm : m ≠ 0) (hD : V + m ^ 2 ≠ 0) :
    V / (V + m ^ 2) = (V / m ^ 2) / (1 + V / m ^ 2) := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hR : 1 + V / m ^ 2 = (V + m ^ 2) / m ^ 2 := by
    field_simp [hm2]
    <;> ring
  rw [hR]
  field_simp [hm2, hD]

/-- A lower bound on the best squared residual gives the corresponding ratio bound. -/
theorem ratio_floor_of_residual_floor (d R : ℝ) (hd : d < 1) (hR : 0 ≤ R)
    (hfloor : d ≤ R / (1 + R)) : d / (1 - d) ≤ R := by
  apply (div_le_iff₀ (sub_pos.mpr hd)).2
  have hden : 0 < 1 + R := by linarith
  have hcross : d * (1 + R) ≤ R := (le_div_iff₀ hden).1 hfloor
  nlinarith

theorem noise_ratio_floor_of_scale_error_floor (V m d : ℝ)
    (hV : 0 ≤ V) (hm : m ≠ 0) (hd : d < 1)
    (hfloor : d ≤ V / (V + m ^ 2)) : d / (1 - d) ≤ V / m ^ 2 := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
  have hD : V + m ^ 2 ≠ 0 := ne_of_gt (by linarith)
  apply ratio_floor_of_residual_floor d (V / m ^ 2) hd
    (div_nonneg hV (le_of_lt hm2))
  rwa [← noise_ratio_conversion V m hm hD]

/-- The paired-mass residual floor becomes `(A - 1) / (A + 1)` for the ratio. -/
theorem ratio_floor_of_mass_floor (A R : ℝ) (hA : 0 < A) (hR : 0 ≤ R)
    (hfloor : (A - 1) / (2 * A) ≤ R / (1 + R)) :
    (A - 1) / (A + 1) ≤ R := by
  have h2A : 0 < 2 * A := by positivity
  have h1R : 0 < 1 + R := by linarith
  have hAp : 0 < A + 1 := by linarith
  have hcross : (A - 1) * (1 + R) ≤ R * (2 * A) :=
    (div_le_div_iff₀ h2A h1R).1 hfloor
  apply (div_le_iff₀ hAp).2
  nlinarith

/-- The weighted average belonging to the pair of weights at `n - 1` and `n`. -/
def pairMean (n x y : ℝ) : ℝ := ((n + 1) * x + (n - 1) * y) / (2 * n)

/-- Exact completion for two successive Pareto weights with prescribed increment. -/
theorem two_point_completion (n x y c : ℝ) (hn : 1 < n) (hxy : y - x = c) :
    (1 - x) ^ 2 / ((n - 1) * n) + (1 - y) ^ 2 / (n * (n + 1)) =
      2 / (n ^ 2 - 1) * (pairMean n x y - 1) ^ 2 + c ^ 2 / (2 * n ^ 2) := by
  have hn0 : n ≠ 0 := ne_of_gt (by linarith)
  have hnm : n - 1 ≠ 0 := ne_of_gt (by linarith)
  have hnp : n + 1 ≠ 0 := ne_of_gt (by linarith)
  have hns : n ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
  rw [← hxy]
  unfold pairMean
  field_simp [hn0, hnm, hnp, hns]
  <;> ring

/-- Completion of the common-increment contribution and the first coordinate. -/
theorem common_increment_completion (A c : ℝ) (hA : A ≠ 0) :
    (1 - c) ^ 2 / 2 + (A - 1) * c ^ 2 / 2 =
      (A - 1) / (2 * A) + A / 2 * (c - 1 / A) ^ 2 := by
  field_simp [hA]
  <;> ring

def reciprocalSquareMass {ι : Type*} (s : Finset ι) (n : ι → ℝ) : ℝ :=
  1 + ∑ i ∈ s, 1 / (n i) ^ 2

theorem reciprocalSquareMass_pos {ι : Type*} (s : Finset ι) (n : ι → ℝ) :
    0 < reciprocalSquareMass s n := by
  have hsum : 0 ≤ ∑ i ∈ s, 1 / (n i) ^ 2 :=
    Finset.sum_nonneg fun i _ => div_nonneg (by norm_num) (sq_nonneg _)
  unfold reciprocalSquareMass
  linarith

/-- The finite paired energy has an exact remainder decomposition. No identification
of the finite mass with a zeta value or Euler product is used. -/
theorem finite_pair_remainder_identity {ι : Type*} (s : Finset ι)
    (n x y : ι → ℝ) (c : ℝ)
    (hn : ∀ i ∈ s, 1 < n i) (hxy : ∀ i ∈ s, y i - x i = c) :
    (1 - c) ^ 2 / 2 +
        (∑ i ∈ s, ((1 - x i) ^ 2 / ((n i - 1) * n i) +
          (1 - y i) ^ 2 / (n i * (n i + 1)))) =
      (reciprocalSquareMass s n - 1) / (2 * reciprocalSquareMass s n) +
        reciprocalSquareMass s n / 2 * (c - 1 / reciprocalSquareMass s n) ^ 2 +
        ∑ i ∈ s, 2 / ((n i) ^ 2 - 1) * (pairMean (n i) (x i) (y i) - 1) ^ 2 := by
  have hsum :
      (∑ i ∈ s, ((1 - x i) ^ 2 / ((n i - 1) * n i) +
          (1 - y i) ^ 2 / (n i * (n i + 1)))) =
        (∑ i ∈ s, 2 / ((n i) ^ 2 - 1) * (pairMean (n i) (x i) (y i) - 1) ^ 2) +
        (c ^ 2 / 2) * ∑ i ∈ s, 1 / (n i) ^ 2 := by
    calc
      _ = ∑ i ∈ s,
          (2 / ((n i) ^ 2 - 1) * (pairMean (n i) (x i) (y i) - 1) ^ 2 +
            (c ^ 2 / 2) * (1 / (n i) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [two_point_completion (n i) (x i) (y i) c (hn i hi) (hxy i hi)]
        have hi0 : n i ≠ 0 := ne_of_gt (by linarith [hn i hi])
        congr 1
        field_simp [hi0]
        <;> ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum]
  calc
    _ = ((1 - c) ^ 2 / 2 + (reciprocalSquareMass s n - 1) * c ^ 2 / 2) +
        ∑ i ∈ s, 2 / ((n i) ^ 2 - 1) * (pairMean (n i) (x i) (y i) - 1) ^ 2 := by
      unfold reciprocalSquareMass
      ring
    _ = _ := by
      rw [common_increment_completion (reciprocalSquareMass s n) c
        (ne_of_gt (reciprocalSquareMass_pos s n))]

/-- Discarding the explicit nonnegative remainders gives a finite energy lower bound. -/
theorem finite_pair_energy_lower_bound {ι : Type*} (s : Finset ι)
    (n x y : ι → ℝ) (c : ℝ)
    (hn : ∀ i ∈ s, 1 < n i) (hxy : ∀ i ∈ s, y i - x i = c) :
    (reciprocalSquareMass s n - 1) / (2 * reciprocalSquareMass s n) ≤
      (1 - c) ^ 2 / 2 +
        ∑ i ∈ s, ((1 - x i) ^ 2 / ((n i - 1) * n i) +
          (1 - y i) ^ 2 / (n i * (n i + 1))) := by
  rw [finite_pair_remainder_identity s n x y c hn hxy]
  have hcommon : 0 ≤ reciprocalSquareMass s n / 2 *
      (c - 1 / reciprocalSquareMass s n) ^ 2 := by
    exact mul_nonneg (div_nonneg (le_of_lt (reciprocalSquareMass_pos s n))
      (by norm_num)) (sq_nonneg _)
  have hpairs : 0 ≤ ∑ i ∈ s,
      2 / ((n i) ^ 2 - 1) * (pairMean (n i) (x i) (y i) - 1) ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    have hden : 0 ≤ (n i) ^ 2 - 1 := by nlinarith [hn i hi]
    exact mul_nonneg (div_nonneg (by norm_num) hden) (sq_nonneg _)
  linarith

end
end RiemannResearch.LinearAlgebra.NoiseSignalQuadratic
