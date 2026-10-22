import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional leakage required by an exact projection gain

Source: independent continuation of Sections 6 and 12 of the user-provided
CRT-carry memorandum, 19 October 2026. C is the old measurable cylinder
space, r is the old residual, and h is the actual new optimizer increment.
The hypothesis inner r h = norm(h)^2 holds for a nested projection step.

-/

noncomputable section
namespace RiemannResearch.Analysis.ConditionalGainGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An old-measurable residual only detects the conditional mean. -/
theorem score_eq_conditional (C : Submodule ℝ H) [C.HasOrthogonalProjection]
    (r h : H) (hr : r ∈ C) :
    inner ℝ r h = inner ℝ r (C.starProjection h) := by
  have ho := (C.mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal h) r hr
  rw [inner_sub_right] at ho
  exact sub_eq_zero.mp ho

/-- Exact split into the conditional mean and the within-fiber remainder. -/
theorem conditional_energy (C : Submodule ℝ H) [C.HasOrthogonalProjection]
    (h : H) :
    ‖h‖ ^ 2 = ‖C.starProjection h‖ ^ 2 + ‖h - C.starProjection h‖ ^ 2 := by
  have ho := (C.mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal h)
    (C.starProjection h) (C.starProjection_apply_mem h)
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at ho
  rw [norm_sub_sq_real]
  have hc : inner ℝ h (C.starProjection h) = inner ℝ (C.starProjection h) h :=
    real_inner_comm _ _
  rw [hc]
  linarith

/-- For an exact optimizer increment, I^2 <= D*J and J <= I.
Here I=norm(h)^2, D=norm(r)^2, J=norm(E[h|old residues])^2. -/
theorem gain_detected_by_conditional (C : Submodule ℝ H)
    [C.HasOrthogonalProjection] (r h : H) (hr : r ∈ C)
    (hgain : inner ℝ r h = ‖h‖ ^ 2) :
    (‖h‖ ^ 2) ^ 2 ≤ ‖r‖ ^ 2 * ‖C.starProjection h‖ ^ 2 ∧
      ‖C.starProjection h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
  constructor
  · have hs := score_eq_conditional C r h hr
    have hn := norm_inner_le_norm (𝕜 := ℝ) r (C.starProjection h)
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    simp only [Real.norm_eq_abs, sq_abs, mul_pow] at hsq
    rw [← hs, hgain] at hsq
    exact hsq
  · have he := conditional_energy C h
    nlinarith [sq_nonneg ‖h - C.starProjection h‖]

/-- If conditioning lands back inside the old legal space, an increment
orthogonal to that space has zero gain. This identifies why full legal
invariance cannot be used as a mechanism for positive improvements. -/
theorem no_gain_of_conditional_old_legal
    (C V : Submodule ℝ H) [C.HasOrthogonalProjection]
    (r h : H) (hr : r ∈ C)
    (horth : ∀ v ∈ V, inner ℝ r v = 0)
    (hc : C.starProjection h ∈ V)
    (hgain : inner ℝ r h = ‖h‖ ^ 2) : h = 0 := by
  have hs := score_eq_conditional C r h hr
  have hz := horth _ hc
  have he : ‖h‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)

end RiemannResearch.Analysis.ConditionalGainGeometry
