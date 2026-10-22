/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import RiemannResearch.Analysis.ProjectionCompressionDefect
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Orthogonal screening of a contractive perturbation

Source: user-directed CRT carry continuation, 22 October 2026. The exact
square completion is derived in RH/QCarryContractionResearch20261022.md.
The concrete RH consumer is RH/QCarryContraction: zero-charge paired residue
sums are (S_p - I)f, and the complete Q floor dilation has squared contraction
constant 1/p. No uniform arithmetic bound or RH premise is assumed here.
-/

noncomputable section
namespace RiemannResearch.Analysis.ContractionScreening
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (V : Submodule ℝ H) [V.HasOrthogonalProjection]

theorem screening_identity (q : ℝ) (f v : H) (hf : f ∈ V) :
    q * ‖v - f‖ ^ 2 =
      ‖v - f - V.starProjection (v - f)‖ ^ 2 +
      ‖V.starProjection v - q • f‖ ^ 2 +
      (1 - q) * (q * ‖f‖ ^ 2 - ‖v‖ ^ 2) := by
  have he : v - f - V.starProjection (v - f) = v - V.starProjection v := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr hf]
    abel
  have ho := Submodule.starProjection_inner_eq_zero v f hf
  rw [inner_sub_left] at ho
  have hi : inner ℝ (V.starProjection v) f = inner ℝ v f := by linarith
  have hp := Submodule.starProjection_inner_eq_zero v (V.starProjection v)
    (V.starProjection_apply_mem v)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hp
  have hiP : inner ℝ v (V.starProjection v) = ‖V.starProjection v‖ ^ 2 := by
    linarith
  rw [he]
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, inner_smul_right, hi, hiP]
  ring

theorem screened_sq_le (q : ℝ) (hq : q ≤ 1) (f v : H) (hf : f ∈ V)
    (hv : ‖v‖ ^ 2 ≤ q * ‖f‖ ^ 2) :
    ‖v - f-V.starProjection (v - f)‖ ^ 2 ≤ q * ‖v - f‖ ^ 2 := by
  have hd : 0 ≤ (1 - q) * (q * ‖f‖ ^ 2-‖v‖ ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hv)
  nlinarith [screening_identity V q f v hf,
    sq_nonneg ‖V.starProjection v-q • f‖]

theorem retained_energy_controls_total (q : ℝ) (hq : q < 1)
    (f v : H) (hf : f ∈ V) (hv : ‖v‖ ^ 2 ≤ q * ‖f‖ ^ 2) :
    ‖v - f‖ ^ 2 ≤ ‖V.starProjection (v - f)‖ ^ 2 / (1 - q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  nlinarith [screened_sq_le V q hq.le f v hf hv,
    ProjectionCompression.projection_pythagoras V (v - f)]

end RiemannResearch.Analysis.ContractionScreening
end
