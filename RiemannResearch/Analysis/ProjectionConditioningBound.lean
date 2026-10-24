import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditioning cost under a uniform projection-loss bound

Source: elementary Pythagoras and Cauchy--Schwarz applied to the user's
conditioning problem, 24 October 2026.

The finite family spans a subspace orthogonal to the target. If projection
retains a fixed fraction of the squared norm on that span, the conditioning
cost is controlled by the target's own residual, independently of dimension.
The argument is Pythagoras and Cauchy--Schwarz, with all cross terms retained.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem projected_independent_of_loss_bound
    (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (e : ι → H) (hi : LinearIndependent ℝ e) (ρ : ℝ) (hρ1 : ρ < 1)
    (hloss : ∀ v ∈ synthesisSpan e,
      ‖v - V.starProjection v‖ ^ 2 ≤ ρ * ‖v‖ ^ 2) :
    LinearIndependent ℝ (fun i => V.starProjection (e i)) := by
  apply (V.starProjection.toLinearMap.linearIndependent_iff_of_injOn ?_).mpr hi
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hz : V.starProjection (x - y) = 0 := by
    change V.starProjection x = V.starProjection y at hxy
    rw [map_sub, hxy, sub_self]
  have hh := hloss (x - y) ((synthesisSpan e).sub_mem hx hy)
  rw [hz, sub_zero] at hh
  have hm : (1 - ρ) * ‖x - y‖ ^ 2 ≤ (1 - ρ) * 0 := by nlinarith
  have hs : ‖x - y‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x - y‖]
  exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))

theorem conditioning_projection_mul_bound
    (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (e : ι → H) (u : H) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (ho : ∀ v ∈ synthesisSpan e, inner ℝ u v = 0)
    (hloss : ∀ v ∈ synthesisSpan e,
      ‖v - V.starProjection v‖ ^ 2 ≤ ρ * ‖v‖ ^ 2) :
    (1 - ρ) * ‖(synthesisSpan (fun i => V.starProjection (e i))).starProjection
      (V.starProjection u)‖ ^ 2 ≤ ρ * ‖u - V.starProjection u‖ ^ 2 := by
  let W := synthesisSpan (fun i => V.starProjection (e i))
  let w := W.starProjection (V.starProjection u)
  change (1 - ρ) * ‖w‖ ^ 2 ≤ ρ * ‖u - V.starProjection u‖ ^ 2
  by_cases hwz : w = 0
  · simp only [hwz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_nonneg hρ0 (sq_nonneg _)
  have hwp : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwz)
  have hw : w ∈ W := W.starProjection_apply_mem _
  have hw' : w ∈ synthesisSpan (fun i => V.starProjection (e i)) := hw
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hw'
  obtain ⟨c, hc⟩ := hw'
  let v := Fintype.linearCombination ℝ e c
  have hv : v ∈ synthesisSpan e := synthesis_mem e c
  have hpv : V.starProjection v = w := by
    simpa only [v, Fintype.linearCombination_apply, map_sum, map_smul] using hc
  have hpy : ‖v‖ ^ 2 = ‖w‖ ^ 2 + ‖v - V.starProjection v‖ ^ 2 := by
    simpa only [Submodule.starProjection_orthogonal_val, hpv] using
      Submodule.norm_sq_eq_add_norm_sq_starProjection v V
  have hs : (1 - ρ) * ‖v - V.starProjection v‖ ^ 2 ≤ ρ * ‖w‖ ^ 2 := by
    have h := hloss v hv
    rw [hpy] at h
    nlinarith
  have hwinner : inner ℝ (V.starProjection u) w = ‖w‖ ^ 2 := by
    have h := W.starProjection_inner_eq_zero (V.starProjection u) w hw
    change inner ℝ (V.starProjection u - w) w = 0 at h
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
    linarith
  have hleft : inner ℝ u (V.starProjection v) =
      inner ℝ (V.starProjection u) (V.starProjection v) := by
    have h := V.starProjection_inner_eq_zero u (V.starProjection v)
      (V.starProjection_apply_mem v)
    rw [inner_sub_left] at h
    linarith
  have hright : inner ℝ (V.starProjection u) v =
      inner ℝ (V.starProjection u) (V.starProjection v) := by
    have h := V.starProjection_inner_eq_zero v (V.starProjection u)
      (V.starProjection_apply_mem u)
    rw [inner_sub_left] at h
    have hc1 := real_inner_comm v (V.starProjection u)
    have hc2 := real_inner_comm (V.starProjection v) (V.starProjection u)
    linarith
  have hcross : inner ℝ (u - V.starProjection u) (v - V.starProjection v) =
      -(‖w‖ ^ 2) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, ho v hv, hleft, hright,
      hpv, hwinner]
    ring
  have hcs : (‖w‖ ^ 2) ^ 2 ≤
      ‖u - V.starProjection u‖ ^ 2 * ‖v - V.starProjection v‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg
        (inner ℝ (u - V.starProjection u) (v - V.starProjection v)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_inner_le_norm (u - V.starProjection u) (v - V.starProjection v))
    simpa only [hcross, norm_neg, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖w‖),
      mul_pow] using h
  by_contra hbad
  have hbadmul := mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hwp
  have h1 := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖u - V.starProjection u‖)
  have h2 := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 1 - ρ by linarith)
  nlinarith

theorem conditioning_projection_bound
    (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (e : ι → H) (u : H) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (ho : ∀ v ∈ synthesisSpan e, inner ℝ u v = 0)
    (hloss : ∀ v ∈ synthesisSpan e,
      ‖v - V.starProjection v‖ ^ 2 ≤ ρ * ‖v‖ ^ 2) :
    ‖(synthesisSpan (fun i => V.starProjection (e i))).starProjection
      (V.starProjection u)‖ ^ 2 ≤
      (ρ / (1 - ρ)) * ‖u - V.starProjection u‖ ^ 2 := by
  have h := conditioning_projection_mul_bound V e u ρ hρ0 hρ1 ho hloss
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show 0 < 1 - ρ by linarith)).mpr
  nlinarith [h]

end RiemannResearch.Analysis.FiniteHilbertGram
