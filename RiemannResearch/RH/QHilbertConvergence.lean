/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Physical coordinate, L1, and square-moment limits in the actual Q space

Source: the user's projection-limit discussion, 25 October 2026.
These are consequences of continuous atomic evaluation and Cauchy--Schwarz.
All sums use the actual inverse-square probability weights, including the tail.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert

/-- Evaluation at a physical site is continuous, including the zero anchor. -/
def qEvalCLM : ℕ → QHilbert →L[ℝ] ℝ
  | 0 => 0
  | n + 1 => (Real.sqrt (qWeight n))⁻¹ • lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n

@[simp] theorem qEvalCLM_apply (k : ℕ) (f : QHilbert) :
    qEvalCLM k f = qSequence f k := by
  cases k with
  | zero => simp [qEvalCLM]
  | succ n =>
      change (Real.sqrt (qWeight n))⁻¹ * f n = qSequence f (n + 1)
      rw [qSequence_succ]
      simp [div_eq_mul_inv, mul_comm]

/-- Norm convergence gives full-sequence pointwise convergence at every site. -/
theorem qSequence_tendsto_of_tendsto {u : ℕ → QHilbert} {f : QHilbert}
    (hu : Tendsto u atTop (𝓝 f)) (k : ℕ) :
    Tendsto (fun M => qSequence (u M) k) atTop (𝓝 (qSequence f k)) := by
  simpa only [Function.comp_def, qEvalCLM_apply] using
    ((qEvalCLM k).continuous.tendsto f).comp hu

/-- Absolute value preserves square summability in the physical Q coordinates. -/
def qAbs (f : QHilbert) : QHilbert :=
  encodeQ (fun k => |qSequence f k|)
    (by simpa only [sq_abs] using qSequence_square_summable f)

@[simp] theorem qAbs_sequence (f : QHilbert) :
    qSequence (qAbs f) = fun k => |qSequence f k| :=
  qSequence_encodeQ _ _ (by simp)

@[simp] theorem qAbs_norm (f : QHilbert) : ‖qAbs f‖ = ‖f‖ := by
  have hs : ‖qAbs f‖ ^ 2 = ‖f‖ ^ 2 := by
    simp only [qNorm_weighted_sq, qAbs_sequence, sq_abs]
  nlinarith [norm_nonneg (qAbs f), norm_nonneg f]

/-- The literal expectation under the physical Q law. -/
theorem qOne_inner_weighted (f : QHilbert) :
    inner ℝ qOne f = ∑' k, positiveQWeight k * qSequence f k := by
  rw [qInner_weighted, qSequence_qOne]
  congr 1
  funext k
  by_cases hk : k = 0
  · simp [hk]
  · simp [qOneSequence, hk]

theorem qFirstMoment_summable (f : QHilbert) :
    Summable (fun k => positiveQWeight k * qSequence f k) := by
  apply (qSequence_product_summable qOne f).congr
  intro k
  rw [qSequence_qOne]
  by_cases hk : k = 0
  · simp [hk]
  · simp [qOneSequence, hk]

theorem qL1_summable (f : QHilbert) :
    Summable (fun k => positiveQWeight k * |qSequence f k|) := by
  simpa only [qAbs_sequence] using qFirstMoment_summable (qAbs f)

/-- The complete physical L1 norm. -/
def qL1 (f : QHilbert) : ℝ := ∑' k, positiveQWeight k * |qSequence f k|

theorem qL1_eq_inner (f : QHilbert) : qL1 f = inner ℝ qOne (qAbs f) := by
  rw [qOne_inner_weighted, qAbs_sequence]
  rfl

theorem qL1_nonneg (f : QHilbert) : 0 ≤ qL1 f :=
  tsum_nonneg (fun k => mul_nonneg (positiveQWeight_nonneg k) (abs_nonneg _))

/-- The probability normalization supplies the exact embedding constant one. -/
theorem qL1_le_norm (f : QHilbert) : qL1 f ≤ ‖f‖ := by
  rw [qL1_eq_inner]
  have h := real_inner_mul_inner_self_le qOne (qAbs f)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    qOne_norm_sq, qAbs_norm, one_mul] at h
  nlinarith [norm_nonneg f]

theorem qL1_sub_tendsto_zero {u : ℕ → QHilbert} {f : QHilbert}
    (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun M => qL1 (u M - f)) atTop (𝓝 0) := by
  have ht : Tendsto (fun M => ‖u M - f‖) atTop (𝓝 0) := by
    simpa using (hu.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))).norm
  exact squeeze_zero (fun M => qL1_nonneg _) (fun M => qL1_le_norm _) ht

/-- L1 distance between the squared physical functions. -/
def qSquareL1Dist (f g : QHilbert) : ℝ :=
  ∑' k, positiveQWeight k * |(qSequence f k)^2 - (qSequence g k)^2|

theorem qSquareL1Dist_summable (f g : QHilbert) :
    Summable (fun k => positiveQWeight k *
      |(qSequence f k)^2 - (qSequence g k)^2|) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveQWeight_nonneg k) (abs_nonneg _))
    _ ((qSequence_square_summable f).add (qSequence_square_summable g))
  intro k
  change positiveQWeight k * |(qSequence f k)^2 - (qSequence g k)^2| ≤
    positiveQWeight k * (qSequence f k)^2 + positiveQWeight k * (qSequence g k)^2
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg k)
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (qSequence f k), sq_nonneg (qSequence g k)]

theorem qSquareL1Dist_nonneg (f g : QHilbert) : 0 ≤ qSquareL1Dist f g :=
  tsum_nonneg (fun k => mul_nonneg (positiveQWeight_nonneg k) (abs_nonneg _))

theorem qSquareL1Dist_eq_inner (f g : QHilbert) :
    qSquareL1Dist f g = inner ℝ (qAbs (f - g)) (qAbs (f + g)) := by
  rw [qInner_weighted]
  unfold qSquareL1Dist
  congr 1
  funext k
  simp only [qAbs_sequence]
  have hs : qSequence (f - g) k = qSequence f k - qSequence g k := by
    change qSequenceLinear (f - g) k = _
    rw [map_sub]
    rfl
  have ha : qSequence (f + g) k = qSequence f k + qSequence g k := by
    change qSequenceLinear (f + g) k = _
    rw [map_add]
    rfl
  rw [hs, ha]
  have hfac : (qSequence f k)^2 - (qSequence g k)^2 =
      (qSequence f k - qSequence g k) * (qSequence f k + qSequence g k) := by ring
  rw [hfac, abs_mul]
  ring

theorem qSquareL1Dist_le (f g : QHilbert) :
    qSquareL1Dist f g ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := by
  rw [qSquareL1Dist_eq_inner]
  calc
    inner ℝ (qAbs (f - g)) (qAbs (f + g)) ≤
        ‖qAbs (f - g)‖ * ‖qAbs (f + g)‖ := real_inner_le_norm _ _
    _ = ‖f - g‖ * ‖f + g‖ := by rw [qAbs_norm, qAbs_norm]
    _ ≤ ‖f - g‖ * (‖f‖ + ‖g‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le f g) (norm_nonneg _)

theorem qSquareL1Dist_tendsto_zero {u : ℕ → QHilbert} {f : QHilbert}
    (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun M => qSquareL1Dist (u M) f) atTop (𝓝 0) := by
  have ht : Tendsto (fun M => ‖u M - f‖) atTop (𝓝 0) := by
    simpa using (hu.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))).norm
  have hb : Tendsto (fun M => ‖u M - f‖ * (‖u M‖ + ‖f‖)) atTop (𝓝 0) := by
    simpa using ht.mul (hu.norm.add tendsto_const_nhds)
  exact squeeze_zero (fun M => qSquareL1Dist_nonneg _ _)
    (fun M => qSquareL1Dist_le _ _) hb

theorem qFirstMoment_tendsto {u : ℕ → QHilbert} {f : QHilbert}
    (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun M => ∑' k, positiveQWeight k * qSequence (u M) k) atTop
      (𝓝 (∑' k, positiveQWeight k * qSequence f k)) := by
  simp_rw [← qOne_inner_weighted]
  exact tendsto_const_nhds.inner hu

theorem qSecondMoment_tendsto {u : ℕ → QHilbert} {f : QHilbert}
    (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun M => ∑' k, positiveQWeight k * (qSequence (u M) k)^2) atTop
      (𝓝 (∑' k, positiveQWeight k * (qSequence f k)^2)) := by
  simpa only [← qNorm_weighted_sq] using hu.norm.pow 2

end RiemannResearch.RH.ZetaTwoHilbert
