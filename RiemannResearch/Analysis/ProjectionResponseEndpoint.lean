/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SingleDirectionResponseDifference
import RiemannResearch.Analysis.ProjectionVariation
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Orthogonal endpoint decomposition for nested projection responses

Source: user-provided argument and item 3 of
`RH/InfiniteSquarefreeResponseResearch20261027.md` at commit
abd42dee58b969ce9c28ecfbf3cfec1e974c8b1a. These support the statement and
orthogonal decomposition. The duality argument below transfers the tail
projection estimate to the opposite side of the self-adjoint operator.
-/

noncomputable section
namespace RiemannResearch.Analysis.ProjectionResponseEndpoint
open SingleDirectionProjection ExhaustiveWalk ProjectionVariation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact signed endpoint identity, before applying any norm estimate. -/
theorem response_difference_eq (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (B : H →L[ℝ] H) (f : H) :
    responseOperator L B f - responseOperator K B f =
      (L.starProjection (B (f - L.starProjection f)) -
        K.starProjection (B (f - L.starProjection f))) -
      K.starProjection (B (L.starProjection f - K.starProjection f)) := by
  simp only [responseOperator, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, map_sub]
  abel

/-- The new output lies in the orthogonal complement of the old output space. -/
theorem projection_difference_inner_projection_eq_zero (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K ≤ L) (x y : H) :
    inner ℝ (L.starProjection x - K.starProjection x) (K.starProjection y) = 0 := by
  have hcomp : K.starProjection (L.starProjection x) = K.starProjection x :=
    congrArg (fun T : H →L[ℝ] H => T x)
      (Submodule.starProjection_comp_starProjection_of_le hKL)
  rw [real_inner_comm, K.inner_starProjection_left_eq_right, map_sub, hcomp,
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x),
    sub_self, inner_zero_right]

/-- Exact Pythagoras for both signed endpoint outputs. -/
theorem response_difference_norm_sq (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K ≤ L) (B : H →L[ℝ] H) (f : H) :
    ‖responseOperator L B f - responseOperator K B f‖ ^ 2 =
      ‖L.starProjection (B (f - L.starProjection f)) -
        K.starProjection (B (f - L.starProjection f))‖ ^ 2 +
      ‖K.starProjection (B (L.starProjection f - K.starProjection f))‖ ^ 2 := by
  rw [response_difference_eq, norm_sub_sq_real,
    projection_difference_inner_projection_eq_zero K L hKL]
  ring

/-- Self-adjointness transfers a full tail-projection bound to smoothing
of a vector in that same tail. No inverse or nonzero innovation is used. -/
theorem smoothing_projection_difference_norm_sq_le (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K ≤ L) (B : H →L[ℝ] H)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ x, ‖L.starProjection (B x) - K.starProjection (B x)‖ ^ 2 ≤
      ‖x‖ ^ 2 * T) (f : H) :
    ‖B (L.starProjection f - K.starProjection f)‖ ^ 2 ≤
      ‖L.starProjection f - K.starProjection f‖ ^ 2 * T := by
  let d := L.starProjection f - K.starProjection f
  let v := L.starProjection (B (B d)) - K.starProjection (B (B d))
  have hi : inner ℝ (B d) (B d) = inner ℝ v d := by
    rw [hB, real_inner_comm]
    exact nested_increment_pairing K L hKL (B (B d)) f
  have hc : ‖B d‖ ^ 2 ≤ ‖v‖ * ‖d‖ := by
    have h := abs_real_inner_le_norm v d
    rw [← hi, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
    exact h
  have hc2 : (‖B d‖ ^ 2) ^ 2 ≤ ‖v‖ ^ 2 * ‖d‖ ^ 2 := by
    have h := mul_self_le_mul_self (sq_nonneg ‖B d‖) hc
    simpa only [← pow_two, mul_pow] using h
  have hv : ‖v‖ ^ 2 ≤ ‖B d‖ ^ 2 * T := hbound (B d)
  have hm : (‖B d‖ ^ 2) * (‖B d‖ ^ 2) ≤
      (‖B d‖ ^ 2) * (‖d‖ ^ 2 * T) := by
    calc
      _ = (‖B d‖ ^ 2) ^ 2 := by ring
      _ ≤ ‖v‖ ^ 2 * ‖d‖ ^ 2 := hc2
      _ ≤ (‖B d‖ ^ 2 * T) * ‖d‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hv (sq_nonneg _)
      _ = _ := by ring
  change ‖B d‖ ^ 2 ≤ ‖d‖ ^ 2 * T
  by_cases hz : ‖B d‖ ^ 2 = 0
  · rw [hz]
    exact mul_nonneg (sq_nonneg _) hT
  · have hp : 0 < ‖B d‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    by_contra h
    have hpos := mul_pos hp (sub_pos.mpr (lt_of_not_ge h))
    nlinarith

/-- Factor-one endpoint bound. Its only analytic input is the stated full
tail bound; the exact residual-energy decomposition supplies the constant. -/
theorem response_difference_norm_sq_le (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hKL : K ≤ L) (B : H →L[ℝ] H)
    (hB : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ x, ‖L.starProjection (B x) - K.starProjection (B x)‖ ^ 2 ≤
      ‖x‖ ^ 2 * T) (f : H) :
    ‖responseOperator L B f - responseOperator K B f‖ ^ 2 ≤
      ‖f - K.starProjection f‖ ^ 2 * T := by
  have hfirst := hbound (f - L.starProjection f)
  have hsecond := smoothing_projection_difference_norm_sq_le
    K L hKL B hB T hT hbound f
  have hp : ‖K.starProjection (B (L.starProjection f - K.starProjection f))‖ ^ 2 ≤
      ‖B (L.starProjection f - K.starProjection f)‖ ^ 2 := by
    have h := mul_self_le_mul_self
      (norm_nonneg (K.starProjection (B (L.starProjection f - K.starProjection f))))
      (Submodule.norm_starProjection_apply_le K
        (B (L.starProjection f - K.starProjection f)))
    simpa only [← pow_two] using h
  rw [response_difference_norm_sq K L hKL]
  calc
    _ ≤ ‖f - L.starProjection f‖ ^ 2 * T +
        ‖L.starProjection f - K.starProjection f‖ ^ 2 * T :=
      add_le_add hfirst (hp.trans hsecond)
    _ = ‖f - K.starProjection f‖ ^ 2 * T := by
      rw [nested_projection_energy K L hKL f]
      ring

end RiemannResearch.Analysis.ProjectionResponseEndpoint
