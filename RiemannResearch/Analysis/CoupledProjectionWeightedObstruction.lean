/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.PolylogAbelBudget
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A coupled two-site obstruction to weighted projection bounds

Source: independent audit of the user's raw-source RH research agenda,
26 October 2026. The RH consumer is the distinction between source smoothing
and weighted stability of the squarefree projection. This example has the
same reciprocal source multiplier and projection-of-target coupling, but its
one-dimensional projection ranges are not asserted to be squarefree legal.
It does not refute a bound for the actual squarefree stages.

The two internal coordinates represent physical sites `1,m`. The target
`(1,1/m)` is the restriction of `sqrt(zeta(2)) * qOne` to those sites.
The averaging map is an orthogonal projection for the Euclidean dot product.
Raw source energies are uniformly bounded while correction energies diverge.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.Analysis.CoupledProjectionWeightedObstruction
open RiemannResearch.Analysis.LogTailWeights

def projection (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun _ => (f 0 + f 1) / 2

def reciprocal (m : ℕ) (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then f 0 / 2 else f 1 / ((m : ℝ) + 1)

def target (m : ℕ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else 1 / (m : ℝ)

def residual (m : ℕ) : Fin 2 → ℝ := target m - projection (target m)

def correction (m : ℕ) : Fin 2 → ℝ := projection (reciprocal m (residual m))

def energy (m : ℕ) (f : Fin 2 → ℝ) : ℝ :=
  polylogTailProfile 2 1 * (f 0)^2 + polylogTailProfile 2 m * (f 1)^2

theorem projection_idempotent (f : Fin 2 → ℝ) :
    projection (projection f) = projection f := by
  funext i
  simp only [projection]
  ring

/-- Orthogonality for arbitrary projected and residual vectors. -/
theorem projection_orthogonality (f g : Fin 2 → ℝ) :
    (∑ i : Fin 2, projection f i * (g i - projection g i)) = 0 := by
  rw [Fin.sum_univ_two]
  simp only [projection]
  ring

/-- The exact coefficient retains both reciprocal differences. -/
theorem correction_exact (m : ℕ) (i : Fin 2) :
    correction m i =
      (1 / 2 - 1 / ((m : ℝ) + 1)) * (1 - 1 / (m : ℝ)) / 4 := by
  norm_num [correction, projection, reciprocal, residual, target]
  ring

theorem residual_energy_exact (m : ℕ) :
    (residual m 0)^2 + (residual m 1)^2 =
      (1 - 1 / (m : ℝ))^2 / 2 := by
  norm_num [residual, target, projection]
  ring

theorem correction_energy_exact (m : ℕ) :
    energy m (correction m) =
      (polylogTailProfile 2 1 + polylogTailProfile 2 m) *
        ((1 / 2 - 1 / ((m : ℝ) + 1)) * (1 - 1 / (m : ℝ)) / 4)^2 := by
  unfold energy
  rw [correction_exact, correction_exact]
  ring

/-- The smoothing estimate is the same scalar estimate as for the RH source. -/
theorem reciprocal_energy_le (m : ℕ) (f : Fin 2 → ℝ) :
    energy m (reciprocal m f) ≤ ((f 0)^2 + (f 1)^2) / 256 := by
  have h0 := mul_le_mul_of_nonneg_right
    (polylog_two_reciprocal_multiplier_le 1) (sq_nonneg (f 0))
  have hm := mul_le_mul_of_nonneg_right
    (polylog_two_reciprocal_multiplier_le m) (sq_nonneg (f 1))
  norm_num only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] at h0
  calc
    energy m (reciprocal m f) =
        (polylogTailProfile 2 1 / 2^2) * (f 0)^2 +
          (polylogTailProfile 2 m / ((m : ℝ) + 1)^2) * (f 1)^2 := by
      norm_num [energy, reciprocal, div_pow]
      ring
    _ ≤ ((f 0)^2 + (f 1)^2) / 256 := by linarith

theorem source_energy_le (m : ℕ) (hm : 2 ≤ m) :
    energy m (reciprocal m (residual m)) ≤ (1 / 512 : ℝ) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hi0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hi1 : 1 / (m : ℝ) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < m)).mpr
    linarith
  have he := reciprocal_energy_le m (residual m)
  rw [residual_energy_exact] at he
  nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hi1)]

theorem correction_coordinate_lower (m : ℕ) (hm : 2 ≤ m) (i : Fin 2) :
    (1 / 48 : ℝ) ≤ correction m i := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hi : 1 / (m : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < m)).mpr
    linarith
  have hn : 1 / ((m : ℝ) + 1) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
    linarith
  have hp : (1 / 12 : ℝ) ≤
      (1 / 2 - 1 / ((m : ℝ) + 1)) * (1 - 1 / (m : ℝ)) := by
    have h := mul_le_mul
      (show (1 / 6 : ℝ) ≤ 1 / 2 - 1 / ((m : ℝ) + 1) by linarith)
      (show (1 / 2 : ℝ) ≤ 1 - 1 / (m : ℝ) by linarith)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show (0 : ℝ) ≤ 1 / 2 - 1 / ((m : ℝ) + 1) by linarith)
    nlinarith
  rw [correction_exact]
  linarith

theorem correction_energy_lower (m : ℕ) (hm : 2 ≤ m) :
    polylogTailProfile 2 m / 2304 ≤ energy m (correction m) := by
  have hc := correction_coordinate_lower m hm 1
  have hs : (1 / 2304 : ℝ) ≤ (correction m 1)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (polylogTailProfile_nonneg 2 m)
  have h0 : 0 ≤ polylogTailProfile 2 1 * (correction m 0)^2 :=
    mul_nonneg (polylogTailProfile_nonneg 2 1) (sq_nonneg _)
  unfold energy
  nlinarith

/-- Uniform source smoothing does not imply uniform weighted correction energy,
even with exact orthogonal-projection coupling. -/
theorem correction_energy_tendsto_atTop :
    Tendsto (fun m : ℕ => energy m (correction m)) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  filter_upwards [(polylogTailProfile_tendsto_atTop 2).eventually
    (eventually_ge_atTop (2304 * C)), eventually_ge_atTop (2 : ℕ)] with m hC hm
  have h := correction_energy_lower m hm
  linarith

end RiemannResearch.Analysis.CoupledProjectionWeightedObstruction
