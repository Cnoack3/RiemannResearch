import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Exact weighted optimizer resolvent

Source: user-provided argument, `Exact_Optimizer_Cancellation_20261008.tex`,
moving optimizer resolvent section. The RH consumer compares the Pareto
optimizer with the inverse-square optimizer in one ambient Hilbert space.

The weighted normal equation is an actual orthogonality statement. The
inverse metric relation and the inverse equivalence are stated explicitly.
No asymptotic coefficient bound or arithmetic cancellation provider is
asserted. The original optimizer residual remains complete throughout.
-/

noncomputable section
namespace RiemannResearch.LinearAlgebra.WeightedOptimizerResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (K : Submodule ℝ H) [K.HasOrthogonalProjection]

/-- The unweighted optimizer residual, using the actual orthogonal
projection onto the complete finite legal dictionary. -/
def residual (x : H) : H := x - K.starProjection x

/-- The reciprocal-coordinate multiplier compressed to the legal orthogonal
complement. It is defined on the ambient space for normal-equation assembly. -/
def compressed (D : H →ₗ[ℝ] H) : H →ₗ[ℝ] H :=
  D - K.starProjection.toLinearMap.comp D

theorem compressed_apply (D : H →ₗ[ℝ] H) (v : H) :
    compressed K D v = D v - K.starProjection (D v) := rfl

theorem residual_mem_orthogonal (x : H) : residual K x ∈ Kᗮ :=
  Submodule.sub_starProjection_mem_orthogonal x

/-- The weighted metric image satisfies the exact compressed resolvent
equation after the legal projection is removed. -/
theorem weighted_normal_resolvent (D : H →ₗ[ℝ] H) (x fP y : H)
    (hfP : fP ∈ K) (hy : y ∈ Kᗮ)
    (hmetric : y + D y = x - fP) :
    y + compressed K D y = residual K x := by
  have hy0 : K.starProjection y = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff K).2 hy
  have hfPfix : K.starProjection fP = fP :=
    Submodule.starProjection_eq_self_iff.mpr hfP
  have hprojected : K.starProjection (D y) = K.starProjection x - fP := by
    have hp := congrArg K.starProjection hmetric
    simpa only [map_add, map_sub, hy0, hfPfix, zero_add] using hp
  rw [compressed_apply, hprojected]
  unfold residual
  calc
    y + (D y - (K.starProjection x - fP)) =
        (y + D y) - K.starProjection x + fP := by abel
    _ = _ := by
      rw [hmetric]
      abel

/-- A genuine equivalence realizing the full compressed forward operator
identifies its inverse with the weighted metric image. -/
theorem weighted_normal_inverse (D : H →ₗ[ℝ] H)
    (E : H ≃ₗ[ℝ] H) (hE : ∀ v, E v = v + compressed K D v)
    (x fP y : H) (hfP : fP ∈ K) (hy : y ∈ Kᗮ)
    (hmetric : y + D y = x - fP) :
    y = E.symm (residual K x) := by
  apply E.injective
  rw [hE y, E.apply_symm_apply]
  exact weighted_normal_resolvent K D x fP y hfP hy hmetric

/-- Moving the weighted legal optimizer to the unweighted residual retains
the complete marked pairing. -/
theorem weighted_marked_pairing (x fP y : H)
    (hfP : fP ∈ K) (hy : y ∈ Kᗮ) :
    inner ℝ (x - fP) y = inner ℝ (residual K x) y := by
  have hfPorth : inner ℝ fP y = 0 := (K.mem_orthogonal y).mp hy fP hfP
  have hPortho : inner ℝ (K.starProjection x) y = 0 :=
    (K.mem_orthogonal y).mp hy _ (K.starProjection_apply_mem x)
  simp only [residual, inner_sub_left, hfPorth, hPortho]

/-- Exact optimum energy as a residual-weighted resolvent. The weighted
normal equation and metric relation are both exposed in the theorem type. -/
theorem weighted_optimizer_energy_resolvent (D : H →ₗ[ℝ] H)
    (E : H ≃ₗ[ℝ] H) (hE : ∀ v, E v = v + compressed K D v)
    (x fP y : H) (hfP : fP ∈ K) (hy : y ∈ Kᗮ)
    (hmetric : y + D y = x - fP) :
    inner ℝ (x - fP) y =
      inner ℝ (residual K x) (E.symm (residual K x)) := by
  rw [weighted_marked_pairing K x fP y hfP hy,
    weighted_normal_inverse K D E hE x fP y hfP hy hmetric]

/-- Exact normalized comparison. The denominator is the complete
unweighted optimal squared residual norm. -/
theorem weighted_optimizer_ratio_resolvent (D : H →ₗ[ℝ] H)
    (E : H ≃ₗ[ℝ] H) (hE : ∀ v, E v = v + compressed K D v)
    (x fP y : H) (hfP : fP ∈ K) (hy : y ∈ Kᗮ)
    (hmetric : y + D y = x - fP) :
    inner ℝ (x - fP) y / ‖residual K x‖ ^ 2 =
      inner ℝ (residual K x) (E.symm (residual K x)) / ‖residual K x‖ ^ 2 := by
  rw [weighted_optimizer_energy_resolvent K D E hE x fP y hfP hy hmetric]

/-- The weighted normal equation really is an optimizer: its complete
quadratic remainder is the energy of the legal displacement. -/
theorem weighted_optimizer_completion (M : H →ₗ[ℝ] H)
    (hM : ∀ u v, inner ℝ (M u) v = inner ℝ u (M v))
    (x fP f : H) (hfP : fP ∈ K) (hf : f ∈ K)
    (hy : M (x - fP) ∈ Kᗮ) :
    inner ℝ (x - f) (M (x - f)) =
      inner ℝ (x - fP) (M (x - fP)) + inner ℝ (f - fP) (M (f - fP)) := by
  have hz : f - fP ∈ K := K.sub_mem hf hfP
  have hleft : inner ℝ (f - fP) (M (x - fP)) = 0 :=
    (K.mem_orthogonal _).mp hy _ hz
  have hright : inner ℝ (x - fP) (M (f - fP)) = 0 := by
    rw [← hM, real_inner_comm]
    exact hleft
  have hid : x - f = (x - fP) - (f - fP) := by abel
  rw [hid, map_sub]
  simp only [inner_sub_left, inner_sub_right, hleft, hright, sub_zero, zero_sub]
  ring

theorem weighted_optimizer_minimizes (M : H →ₗ[ℝ] H)
    (hM : ∀ u v, inner ℝ (M u) v = inner ℝ u (M v))
    (hpositive : ∀ v, 0 ≤ inner ℝ v (M v))
    (x fP f : H) (hfP : fP ∈ K) (hf : f ∈ K)
    (hy : M (x - fP) ∈ Kᗮ) :
    inner ℝ (x - fP) (M (x - fP)) ≤ inner ℝ (x - f) (M (x - f)) := by
  rw [weighted_optimizer_completion K M hM x fP f hfP hf hy]
  exact le_add_of_nonneg_right (hpositive (f - fP))

end RiemannResearch.LinearAlgebra.WeightedOptimizerResolvent
