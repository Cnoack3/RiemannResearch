import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive compression and inexact equation certificates

Source: the Pareto-first transfer manuscript, Section 9, 11 November 2026.
Coercivity is proved from positivity. Finite-head certificates retain one
complete error term on r-v and do not assume exact inversion or vanishing.
-/

noncomputable section
namespace RiemannResearch.Analysis.PositiveCompressionCertificate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (V : Submodule ℝ E) [V.HasOrthogonalProjection]

def normalOperator (D : E →L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + V.starProjection.comp D

@[simp] theorem normalOperator_apply (D : E →L[ℝ] E) (x : E) :
    normalOperator V D x = x + V.starProjection (D x) := rfl

theorem projection_norm_le (x : E) : ‖V.starProjection x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖V.starProjection‖ * ‖x‖ := V.starProjection.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right V.starProjection_norm_le (norm_nonneg x)
    _ = _ := one_mul _

theorem inner_projection (x y : E) (hx : x ∈ V) :
    inner ℝ x (V.starProjection y) = inner ℝ x y := by
  have h := Submodule.starProjection_inner_eq_zero y x hx
  rw [inner_sub_left] at h
  rw [← real_inner_comm x (V.starProjection y), ← real_inner_comm x y]
  linarith

theorem norm_le_normalOperator (D : E →L[ℝ] E)
    (hpos : ∀ x, 0 ≤ inner ℝ x (D x)) (x : E) (hx : x ∈ V) :
    ‖x‖ ≤ ‖normalOperator V D x‖ := by
  have hp := hpos x
  have he : inner ℝ x (normalOperator V D x) =
      ‖x‖ ^ 2 + inner ℝ x (D x) := by
    rw [normalOperator_apply, inner_add_right, real_inner_self_eq_norm_sq,
      inner_projection V x (D x) hx]
  have hc := (le_abs_self (inner ℝ x (normalOperator V D x))).trans
    (abs_real_inner_le_norm x (normalOperator V D x))
  rw [he] at hc
  by_cases hz : ‖x‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hn : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hz)
    nlinarith

theorem normalOperator_norm_le (D : E →L[ℝ] E)
    (hD : ∀ x, ‖D x‖ ≤ ‖x‖) (x : E) :
    ‖normalOperator V D x‖ ≤ 2 * ‖x‖ := by
  calc
    _ ≤ ‖x‖ + ‖V.starProjection (D x)‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖x‖ := add_le_add le_rfl ((projection_norm_le V _).trans (hD x))
    _ = _ := by ring

theorem solution_norm_bounds (D : E →L[ℝ] E)
    (hpos : ∀ x, 0 ≤ inner ℝ x (D x)) (hD : ∀ x, ‖D x‖ ≤ ‖x‖)
    (d a : E) (hd : d ∈ V) (heq : normalOperator V D d = a) :
    ‖a‖ / 2 ≤ ‖d‖ ∧ ‖d‖ ≤ ‖a‖ := by
  constructor
  · have h := normalOperator_norm_le V D hD d
    rw [heq] at h
    linarith
  · simpa only [heq] using norm_le_normalOperator V D hpos d hd

theorem aPosteriori (D : E →L[ℝ] E)
    (hpos : ∀ x, 0 ≤ inner ℝ x (D x))
    (d a v : E) (hd : d ∈ V) (hv : v ∈ V)
    (heq : normalOperator V D d = a) :
    ‖d - v‖ ≤ ‖a - normalOperator V D v‖ := by
  have h := norm_le_normalOperator V D hpos (d-v) (V.sub_mem hd hv)
  rwa [map_sub, heq] at h

theorem solution_unique (D : E →L[ℝ] E)
    (hpos : ∀ x, 0 ≤ inner ℝ x (D x))
    (d e : E) (hd : d ∈ V) (he : e ∈ V)
    (heq : normalOperator V D d = normalOperator V D e) : d = e := by
  have h := aPosteriori V D hpos d (normalOperator V D e) e hd he heq
  rw [sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- A single tail budget acts on r-v; the signed correction is retained. -/
theorem truncated_residual_exact (D B : E →L[ℝ] E) (r v : E) :
    V.starProjection (D r) - normalOperator V D v =
      (V.starProjection (B r) - normalOperator V B v) +
        V.starProjection ((D-B) (r-v)) := by
  simp only [normalOperator_apply, map_sub, sub_apply]
  abel

theorem truncated_aPosteriori (D B : E →L[ℝ] E)
    (hpos : ∀ x, 0 ≤ inner ℝ x (D x))
    (δ : ℝ) (htail : ∀ x, ‖(D-B) x‖ ≤ δ * ‖x‖)
    (d r v : E) (hd : d ∈ V) (hv : v ∈ V)
    (heq : normalOperator V D d = V.starProjection (D r)) :
    ‖d-v‖ ≤ ‖V.starProjection (B r) - normalOperator V B v‖ + δ * ‖r-v‖ := by
  calc
    _ ≤ ‖V.starProjection (D r) - normalOperator V D v‖ :=
      aPosteriori V D hpos d _ v hd hv heq
    _ = _ := congrArg norm (truncated_residual_exact V D B r v)
    _ ≤ ‖V.starProjection (B r) - normalOperator V B v‖ +
        ‖V.starProjection ((D-B) (r-v))‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl ((projection_norm_le V _).trans (htail (r-v)))

/-- Exact certificate for the forcing norm from any trial in V. -/
theorem forcing_energy_exact (D : E →L[ℝ] E) (r v : E) (hv : v ∈ V) :
    ‖V.starProjection (D r)‖ ^ 2 =
      2 * inner ℝ (D r) v - ‖v‖ ^ 2 + ‖V.starProjection (D r) - v‖ ^ 2 := by
  have hp := inner_projection V v (D r) hv
  rw [← real_inner_comm v (V.starProjection (D r)), ← real_inner_comm v (D r)] at hp
  have hn := norm_sub_sq_real (V.starProjection (D r)) v
  nlinarith

end RiemannResearch.Analysis.PositiveCompressionCertificate
