/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Inverse-density and mixed bounds for the Q/P metric correction

Source: the user's request to combine both Radon--Nikodym derivatives with
the unconditional canonical discrepancy, 15 October 2026.
A square-root reciprocal multiplier realizes the complete correction as an
actual Hilbert Gram form. Mixed and signed-combination bounds keep the
entire correction before estimating it.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.QMetricCorrectionBounds
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric

theorem inverse_weight_identity (k : ℕ) :
    positiveWeight k = zetaTwo * positiveQWeight k * (k : ℝ) / ((k : ℝ) + 1) := by
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight, positiveQWeight]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    unfold positiveWeight positiveQWeight
    field_simp [ne_of_gt zetaTwo_pos, hkR, hk1]

/-- The inverse Radon--Nikodym derivative expresses the same correction
using Q's own squared coordinates and the shifted reciprocal multiplier. -/
theorem inverse_correction_identity (f : QHilbert) :
    metricCorrection f = zetaTwo * ∑' n : ℕ, (f n) ^ 2 / ((n : ℝ) + 2) := by
  rw [metricCorrection_eq_physical, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← qSequence_weighted_square f n]
  unfold positiveQWeight
  simp only [Nat.cast_add, Nat.cast_one]
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [ne_of_gt zetaTwo_pos, h1, h2]

/-- The inverse-density bound has H+2 in the denominator; it is equivalent
to the sharp P-energy bound after retaining the exact correction identity. -/
theorem correction_le_Qnorm_of_head_zero (f : QHilbert) (H : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence f k = 0) :
    metricCorrection f ≤ zetaTwo * ‖f‖ ^ 2 / ((H : ℝ) + 2) := by
  have h := metricCorrection_le_of_head_zero f H hhead
  have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) + 1)).mp h
  have he := norm_identity f
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) + 2)).mpr
  nlinarith only [hm, he]

/-- A genuine square-root reciprocal multiplier on the common l2 carrier. -/
def halfReciprocal (g : ThresholdHilbert) : ThresholdHilbert :=
  ⟨fun n => g n / Real.sqrt ((n : ℝ) + 1), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).mpr
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    apply (reciprocal_energy_summable g).congr
    intro n
    rw [div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]⟩

@[simp] theorem halfReciprocal_apply (g : ThresholdHilbert) (n : ℕ) :
    halfReciprocal g n = g n / Real.sqrt ((n : ℝ) + 1) := rfl

theorem halfReciprocal_inner (f g : ThresholdHilbert) :
    inner ℝ (halfReciprocal f) (halfReciprocal g) = inner ℝ f (reciprocalD g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change (g n / Real.sqrt ((n : ℝ) + 1)) * (f n / Real.sqrt ((n : ℝ) + 1)) =
    (g n / ((n : ℝ) + 1)) * f n
  rw [div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  ring

def halfReciprocalLinear : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := halfReciprocal
  map_add' f g := by
    apply Subtype.ext
    funext n
    change (f n + g n) / Real.sqrt ((n : ℝ) + 1) =
      f n / Real.sqrt ((n : ℝ) + 1) + g n / Real.sqrt ((n : ℝ) + 1)
    exact add_div _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext n
    change (c * f n) / Real.sqrt ((n : ℝ) + 1) =
      c * (f n / Real.sqrt ((n : ℝ) + 1))
    ring

/-- The complete discrepancy Gram form is the Gram form of this linear image. -/
def correctionVector : QHilbert →ₗ[ℝ] ThresholdHilbert :=
  halfReciprocalLinear.comp toParetoLinear

theorem correctionVector_inner (f g : QHilbert) :
    inner ℝ (correctionVector f) (correctionVector g) = metricPairing f g :=
  halfReciprocal_inner _ _

theorem correctionVector_norm_sq (f : QHilbert) :
    ‖correctionVector f‖ ^ 2 = metricCorrection f := by
  rw [← real_inner_self_eq_norm_sq, correctionVector_inner]
  rfl

theorem metricPairing_sq_le (f g : QHilbert) :
    (metricPairing f g) ^ 2 ≤ metricCorrection f * metricCorrection g := by
  have h := real_inner_mul_inner_self_le (correctionVector f) (correctionVector g)
  simpa only [correctionVector_inner, real_inner_self_eq_norm_sq,
    correctionVector_norm_sq, ← pow_two] using h

theorem metricPairing_abs_le_of_budget (f g : QHilbert) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : metricCorrection f ≤ ε) (hg : metricCorrection g ≤ ε) :
    |metricPairing f g| ≤ ε := by
  apply (sq_le_sq₀ (abs_nonneg _) hε).mp
  rw [sq_abs]
  exact (metricPairing_sq_le f g).trans
    (by simpa only [pow_two] using
      mul_le_mul hf hg (metricCorrection_nonneg g) hε)

/-- Signed coefficients are allowed. The full signed sum is retained
exactly as the correctionVector norm before the l1 budget is applied. -/
theorem metricCorrection_sum_le {ι : Type*} [Fintype ι]
    (v : ι → QHilbert) (a : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hv : ∀ i, metricCorrection (v i) ≤ ε) :
    metricCorrection (∑ i, a i • v i) ≤ (∑ i, |a i|) ^ 2 * ε := by
  have hi (i : ι) : ‖correctionVector (v i)‖ ≤ Real.sqrt ε := by
    have hh := hv i
    rw [← correctionVector_norm_sq] at hh
    nlinarith [Real.sq_sqrt hε, Real.sqrt_nonneg ε, norm_nonneg (correctionVector (v i))]
  have hn : ‖correctionVector (∑ i, a i • v i)‖ ≤ (∑ i, |a i|) * Real.sqrt ε := by
    rw [map_sum]
    simp only [map_smul]
    calc
      _ ≤ ∑ i, ‖a i • correctionVector (v i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a i| * Real.sqrt ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hi i) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  simpa only [mul_pow, Real.sq_sqrt hε, correctionVector_norm_sq] using hs


/-- The weighted signed budget retains the individual correction sizes. -/
theorem metricCorrection_sum_le_weighted {ι : Type*} [Fintype ι]
    (v : ι → QHilbert) (a : ι → ℝ) :
    metricCorrection (∑ i, a i • v i) ≤
      (∑ i, |a i| * Real.sqrt (metricCorrection (v i))) ^ 2 := by
  have hi (i : ι) : ‖correctionVector (v i)‖ = Real.sqrt (metricCorrection (v i)) := by
    rw [← correctionVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hn : ‖correctionVector (∑ i, a i • v i)‖ ≤
      ∑ i, |a i| * Real.sqrt (metricCorrection (v i)) := by
    rw [map_sum]
    simp only [map_smul]
    calc
      _ ≤ ∑ i, ‖a i • correctionVector (v i)‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs, hi]
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))).mpr hn
  simpa only [correctionVector_norm_sq] using hs

/-- Trace control of the entire finite correction Gram operator. -/
theorem metricCorrection_sum_le_l2 {ι : Type*} [Fintype ι]
    (v : ι → QHilbert) (a : ι → ℝ) :
    metricCorrection (∑ i, a i • v i) ≤
      (∑ i, (a i) ^ 2) * (∑ i, metricCorrection (v i)) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |a i|) (fun i => Real.sqrt (metricCorrection (v i)))
  have hs : (∑ i, |a i| * Real.sqrt (metricCorrection (v i))) ^ 2 ≤
      (∑ i, (a i) ^ 2) * (∑ i, metricCorrection (v i)) := by
    simpa only [sq_abs, Real.sq_sqrt (metricCorrection_nonneg _)] using h
  exact (metricCorrection_sum_le_weighted v a).trans hs

/-- Even unbounded l1 masses are allowed when the complete weighted
correction budget tends to zero. There is no full-energy hypothesis. -/
theorem metricCorrection_sum_tendsto_zero
    (n : ℕ → ℕ) (v : (j : ℕ) → Fin (n j) → QHilbert)
    (a : (j : ℕ) → Fin (n j) → ℝ)
    (hbudget : Filter.Tendsto
      (fun j => ∑ i, |a j i| * Real.sqrt (metricCorrection (v j i)))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun j => metricCorrection (∑ i, a j i • v j i)) Filter.atTop (𝓝 0) :=
  squeeze_zero (fun _ => metricCorrection_nonneg _)
    (fun j => metricCorrection_sum_le_weighted (v j) (a j))
    (by simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hbudget.pow 2)


/-- A reciprocal tail has an additional reciprocal factor in its squared norm. -/
theorem reciprocalD_norm_sq_le_reciprocal_energy (g : ThresholdHilbert) (H : ℕ)
    (hhead : ∀ n < H, g n = 0) :
    ‖reciprocalD g‖ ^ 2 ≤ inner ℝ g (reciprocalD g) / ((H : ℝ) + 1) := by
  rw [qNorm_sq, reciprocalD_inner_tsum, ← tsum_div_const]
  apply Summable.tsum_le_tsum _ (qCoordinate_square_summable (reciprocalD g))
    ((reciprocal_energy_summable g).div_const _)
  intro n
  by_cases hn : n < H
  · simp [reciprocalD_apply, hhead n hn]
  · rw [reciprocalD_apply, div_pow]
    have he : (g n) ^ 2 / ((n : ℝ) + 1) ^ 2 =
        ((g n) ^ 2 / ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by simp only [div_div, pow_two]
    rw [he]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.add_le_add_right (Nat.le_of_not_gt hn) 1

/-- Uniform mixed correction control for every Hilbert test, including tests
with large pointwise values; no physical boundedness hypothesis is needed. -/
theorem metricPairing_sq_le_test_norm (f g : QHilbert) (H : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ H → qSequence g k = 0) :
    (metricPairing f g) ^ 2 ≤
      ‖toPareto f‖ ^ 2 * metricCorrection g / ((H : ℝ) + 1) := by
  have hc := reciprocalD_norm_sq_le_reciprocal_energy (toPareto g) H
    (toPareto_head_zero g H hhead)
  have hs := real_inner_mul_inner_self_le (toPareto f) (reciprocalD (toPareto g))
  have hh : (metricPairing f g) ^ 2 ≤
      ‖toPareto f‖ ^ 2 * ‖reciprocalD (toPareto g)‖ ^ 2 := by
    simpa only [metricPairing, real_inner_self_eq_norm_sq, ← pow_two] using hs
  exact hh.trans
    ((mul_le_mul_of_nonneg_left hc (sq_nonneg _)).trans_eq (by
      unfold metricCorrection
      ring))

end RiemannResearch.RH.QMetricCorrectionBounds
