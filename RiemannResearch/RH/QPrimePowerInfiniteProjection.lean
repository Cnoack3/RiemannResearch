/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Infinite same-prime projection of the floor-logarithm target

Source: user-provided orthonormal-basis research direction, 20 October 2026.
We sum the previously checked wavelet coefficients in the actual Q Hilbert
space, compute their total energy, and retain the exact residual. The target
is Nat.log p n, never the prime valuation. The normalized sum has coefficients
2/3 and 3/8 for bases two and three. QPrimePowerValuationProjection identifies
its physical coordinates with the first Meixner valuation polynomial.
No legal squarefree-closure membership or residual vanishing is assumed.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QDivisorHilbert

/-- The nonconstant same-prime coefficient series converges absolutely in the Q norm. -/
theorem primePower_nonconstant_summable (p : ℕ) (hp : p.Prime) :
    Summable (fun k : ℕ =>
      inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) •
        primePowerFrame p hp (k + 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hgeo : |(p : ℝ)⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hp0)]
    exact (inv_lt_one₀ hp0).mpr hp1
  apply Summable.of_norm
  apply ((summable_geometric_of_abs_lt_one hgeo).mul_left
    (Real.sqrt ((p : ℝ)^2 - 1))⁻¹).congr
  intro k
  rw [norm_smul, (primePowerFrame_orthonormal p hp).1, mul_one,
    qTarget_inner_primePowerFrame_succ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp [one_div, mul_comm]

/-- The actual Q-Hilbert sum of all nonconstant same-prime target modes. -/
def primePowerProjection (p : ℕ) (hp : p.Prime) : QHilbert :=
  ∑' k : ℕ, inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) •
    primePowerFrame p hp (k + 1)

/-- Finite initial expansions converge in the complete Q norm to the infinite projection. -/
theorem primePowerProjection_tendsto (p : ℕ) (hp : p.Prime) :
    Filter.Tendsto (fun N => ∑ k ∈ Finset.range N,
      inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) •
        primePowerFrame p hp (k + 1)) Filter.atTop
      (nhds (primePowerProjection p hp)) :=
  (primePower_nonconstant_summable p hp).hasSum.tendsto_sum_nat

/-- Exact geometric sum of every nonconstant same-prime coefficient square. -/
theorem primePower_nonconstant_energy_hasSum (p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ =>
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1))) ^ 2)
      ((p : ℝ)^2 / ((p : ℝ)^2 - 1)^2) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2 : (1 : ℝ) < (p : ℝ)^2 := by nlinarith
  have hD : 0 ≤ (p : ℝ)^2 - 1 := by linarith
  have hgeo : |((p : ℝ)^2)⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (by positivity))]
    exact (inv_lt_one₀ (by positivity)).mpr hp2
  have hf : (fun k : ℕ =>
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1))) ^ 2) =
      (fun k : ℕ => ((p : ℝ)^2 - 1)⁻¹ * (((p : ℝ)^2)⁻¹)^k) := by
    funext k
    rw [qTarget_inner_primePowerFrame_succ, div_pow, mul_pow, Real.sq_sqrt hD]
    simp [one_div, ← pow_mul, mul_comm]
  rw [hf]
  have hv : ((p : ℝ)^2 - 1)⁻¹ * (1 - ((p : ℝ)^2)⁻¹)⁻¹ =
      (p : ℝ)^2 / ((p : ℝ)^2 - 1)^2 := by
    have hn : (p : ℝ)^2 - 1 ≠ 0 := by linarith
    field_simp
  rw [← hv]
  exact (hasSum_geometric_of_abs_lt_one hgeo).mul_left _

/-- The infinite projection retains each same-prime coefficient. -/
theorem primePowerProjection_inner_frame (p : ℕ) (hp : p.Prime) (j : ℕ) :
    inner ℝ (primePowerFrame p hp (j + 1)) (primePowerProjection p hp) =
      inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (j + 1)) := by
  change (innerSL ℝ (primePowerFrame p hp (j + 1)))
    (∑' k : ℕ, _) = _
  rw [(innerSL ℝ (primePowerFrame p hp (j + 1))).map_tsum
    (primePower_nonconstant_summable p hp)]
  change (∑' k : ℕ, inner ℝ (primePowerFrame p hp (j + 1))
    (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) •
      primePowerFrame p hp (k + 1))) = _
  simp only [real_inner_smul_right,
    (orthonormal_iff_ite.mp (primePowerFrame_orthonormal p hp))]
  simp

/-- The target-projection pairing equals the full captured same-prime energy. -/
theorem qTarget_inner_primePowerProjection (p : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (primePowerProjection p hp) =
      (p : ℝ)^2 / ((p : ℝ)^2 - 1)^2 := by
  change (innerSL ℝ (qTarget p hp.one_lt)) (∑' k : ℕ, _) = _
  rw [(innerSL ℝ (qTarget p hp.one_lt)).map_tsum (primePower_nonconstant_summable p hp)]
  simpa [pow_two] using (primePower_nonconstant_energy_hasSum p hp).tsum_eq

/-- The infinite projection has an explicit norm square, with no discarded modes. -/
theorem primePowerProjection_norm_sq (p : ℕ) (hp : p.Prime) :
    ‖primePowerProjection p hp‖ ^ 2 = (p : ℝ)^2 / ((p : ℝ)^2 - 1)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  change (innerSL ℝ (primePowerProjection p hp)) (∑' k : ℕ, _) = _
  rw [(innerSL ℝ (primePowerProjection p hp)).map_tsum
    (primePower_nonconstant_summable p hp)]
  change (∑' k : ℕ, inner ℝ (primePowerProjection p hp)
    (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) •
      primePowerFrame p hp (k + 1))) = _
  simp only [real_inner_smul_right]
  have hi (k : ℕ) :
      inner ℝ (primePowerProjection p hp) (primePowerFrame p hp (k + 1)) =
      inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) :=
    (real_inner_comm _ _).trans (primePowerProjection_inner_frame p hp k)
  simp_rw [hi]
  simpa [pow_two] using (primePower_nonconstant_energy_hasSum p hp).tsum_eq

/-- Infinite same-prime Pythagoras with the complete unexplained residual. -/
theorem qTarget_primePower_infinite_energy_exact (p : ℕ) (hp : p.Prime) :
    ‖qTarget p hp.one_lt‖ ^ 2 =
      (p : ℝ)^2 / ((p : ℝ)^2 - 1)^2 +
        ‖qTarget p hp.one_lt - primePowerProjection p hp‖ ^ 2 := by
  rw [norm_sub_sq_real, primePowerProjection_norm_sq, qTarget_inner_primePowerProjection]
  ring

/-- The residual is orthogonal to every nonconstant same-prime wavelet. -/
theorem qTarget_sub_projection_inner_frame (p : ℕ) (hp : p.Prime) (j : ℕ) :
    inner ℝ (qTarget p hp.one_lt - primePowerProjection p hp)
      (primePowerFrame p hp (j + 1)) = 0 := by
  rw [inner_sub_left, real_inner_comm (primePowerFrame p hp (j + 1))
    (primePowerProjection p hp), primePowerProjection_inner_frame, sub_self]


/-- The nonconstant projection has zero physical Q mean. -/
theorem qOne_inner_primePowerProjection (p : ℕ) (hp : p.Prime) :
    inner ℝ qOne (primePowerProjection p hp) = 0 := by
  change (innerSL ℝ qOne) (∑' k : ℕ, _) = _
  rw [(innerSL ℝ qOne).map_tsum (primePower_nonconstant_summable p hp)]
  change (∑' k : ℕ, inner ℝ qOne
    (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) •
      primePowerFrame p hp (k + 1))) = 0
  have hi (k : ℕ) : inner ℝ qOne (primePowerFrame p hp (k + 1)) = 0 := by
    rw [← primePowerFrame_zero p hp]
    exact (primePowerFrame_orthonormal p hp).2 (by omega)
  simp [real_inner_smul_right, hi]

/-- Separate the mean and every nonconstant same-prime mode, retaining the full residual. -/
theorem qTarget_primePower_centered_energy_exact (p : ℕ) (hp : p.Prime) :
    ‖qTarget p hp.one_lt‖ ^ 2 =
      (inner ℝ (qTarget p hp.one_lt) qOne)^2 +
      (p : ℝ)^2 / ((p : ℝ)^2 - 1)^2 +
      ‖qTarget p hp.one_lt -
        inner ℝ (qTarget p hp.one_lt) qOne • qOne - primePowerProjection p hp‖^2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, qOne_norm_sq, inner_sub_left,
    real_inner_smul_left, qOne_inner_primePowerProjection,
    qTarget_inner_primePowerProjection, primePowerProjection_norm_sq,
    real_inner_smul_right]
  ring

/-- Exact error for an arbitrary convergent signed trial series. No sign condition is imposed. -/
theorem qTarget_primePower_series_error_exact (p : ℕ) (hp : p.Prime)
    (c : ℕ → ℝ)
    (hc : Summable (fun k => c k • primePowerFrame p hp (k + 1))) :
    ‖qTarget p hp.one_lt - ∑' k, c k • primePowerFrame p hp (k + 1)‖^2 =
      ‖primePowerProjection p hp - ∑' k, c k • primePowerFrame p hp (k + 1)‖^2 +
      ‖qTarget p hp.one_lt - primePowerProjection p hp‖^2 := by
  have hz : inner ℝ (qTarget p hp.one_lt - primePowerProjection p hp)
      (∑' k, c k • primePowerFrame p hp (k + 1)) = 0 := by
    change (innerSL ℝ (qTarget p hp.one_lt - primePowerProjection p hp)) (∑' k, _) = 0
    rw [(innerSL ℝ (qTarget p hp.one_lt - primePowerProjection p hp)).map_tsum hc]
    change (∑' k, inner ℝ (qTarget p hp.one_lt - primePowerProjection p hp)
      (c k • primePowerFrame p hp (k + 1))) = 0
    simp [real_inner_smul_right, qTarget_sub_projection_inner_frame]
  have hpz : inner ℝ (qTarget p hp.one_lt - primePowerProjection p hp)
      (primePowerProjection p hp) = 0 := by
    rw [inner_sub_left, qTarget_inner_primePowerProjection,
      real_inner_self_eq_norm_sq, primePowerProjection_norm_sq, sub_self]
  have he : qTarget p hp.one_lt - ∑' k, c k • primePowerFrame p hp (k + 1) =
      (qTarget p hp.one_lt - primePowerProjection p hp) +
        (primePowerProjection p hp - ∑' k, c k • primePowerFrame p hp (k + 1)) := by
    abel
  rw [he, norm_add_sq_real, inner_sub_right, hpz, hz]
  ring

/-- Normalize the infinite same-prime projection; valuation coordinates are not asserted here. -/
def primePowerProjectionUnit (p : ℕ) (hp : p.Prime) : QHilbert :=
  (((p : ℝ)^2 - 1) / p) • primePowerProjection p hp

/-- The normalized infinite projection has unit norm square. -/
theorem primePowerProjectionUnit_norm_sq (p : ℕ) (hp : p.Prime) :
    ‖primePowerProjectionUnit p hp‖^2 = 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2 - 1 ≠ 0 := by nlinarith
  rw [primePowerProjectionUnit, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, primePowerProjection_norm_sq]
  field_simp

/-- Exact target coefficient in the normalized infinite projection direction. -/
theorem qTarget_inner_primePowerProjectionUnit (p : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (primePowerProjectionUnit p hp) =
      (p : ℝ) / ((p : ℝ)^2 - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2 - 1 ≠ 0 := by nlinarith
  rw [primePowerProjectionUnit, real_inner_smul_right, qTarget_inner_primePowerProjection]
  field_simp

/-- Total dyadic nonconstant captured energy. -/
theorem primePowerProjection_two_norm_sq :
    ‖primePowerProjection 2 Nat.prime_two‖^2 = 4 / 9 := by
  norm_num [primePowerProjection_norm_sq]

/-- Total triadic nonconstant captured energy. -/
theorem primePowerProjection_three_norm_sq :
    ‖primePowerProjection 3 Nat.prime_three‖^2 = 9 / 64 := by
  norm_num [primePowerProjection_norm_sq]

/-- The dyadic normalized projection coefficient is exactly 2/3. -/
theorem qTarget_two_inner_primePowerProjectionUnit :
    inner ℝ (qTarget 2 Nat.prime_two.one_lt)
      (primePowerProjectionUnit 2 Nat.prime_two) = 2 / 3 := by
  norm_num [qTarget_inner_primePowerProjectionUnit]

/-- The triadic normalized projection coefficient is exactly 3/8. -/
theorem qTarget_three_inner_primePowerProjectionUnit :
    inner ℝ (qTarget 3 Nat.prime_three.one_lt)
      (primePowerProjectionUnit 3 Nat.prime_three) = 3 / 8 := by
  norm_num [qTarget_inner_primePowerProjectionUnit]

end RiemannResearch.RH.PrimePowerTarget
