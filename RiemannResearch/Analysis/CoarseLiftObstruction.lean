import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Exact coarse-lift obstruction

Source: Christian Noack, *A two-seed threshold and an exact distance criterion
for the Riemann hypothesis*, September 7, 2026, Section 10,
Theorem `thm:crt-linear`, equations `eq:crt-witness-equality` and
`eq:crt-annihilator-cost`. This module proves the underlying Hilbert-space
statement. Construction and quantitative approximation of the paper's actual
phase witness are separate, unresolved formalization obligations.
-/

namespace RiemannResearch.Analysis.CoarseLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Exact signed pairing; no tail is discarded. -/
theorem coarse_lift_witness_identity (P : E →ₗ[ℝ] E)
    (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (e F z : E) (he : P e = e) (hF : P F = e)
    (hz : ⟪F, z⟫ = 0) :
    ⟪F - e, z - P z⟫ = -⟪e, z⟫ := by
  have hzero : ⟪F - e, P z⟫ = 0 := by
    rw [← hP, map_sub, hF, he, sub_self, inner_zero_left]
  rw [inner_sub_right, hzero, sub_zero, inner_sub_left, hz, zero_sub]

/-- An exact coarse fit has the Pythagorean norm, including the entire residual. -/
theorem coarse_lift_norm_identity (P : E →ₗ[ℝ] E)
    (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (e F : E) (he : P e = e) (hF : P F = e) :
    ‖F‖ ^ 2 = ‖e‖ ^ 2 + ‖F - e‖ ^ 2 := by
  have hinner : ⟪F, e⟫ = ‖e‖ ^ 2 := by
    calc
      ⟪F, e⟫ = ⟪F, P e⟫ := by rw [he]
      _ = ⟪P F, e⟫ := (hP F e).symm
      _ = ‖e‖ ^ 2 := by rw [hF, real_inner_self_eq_norm_sq]
  have h := norm_sub_sq_real F e
  nlinarith

/-- Cauchy--Schwarz obstruction in multiplicative form, valid even if the
projected witness residual vanishes. -/
theorem coarse_lift_energy_product (P : E →ₗ[ℝ] E)
    (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (e F z : E) (he : P e = e) (hF : P F = e)
    (hz : ⟪F, z⟫ = 0) :
    ⟪e, z⟫ ^ 2 ≤ (‖F‖ ^ 2 - ‖e‖ ^ 2) * ‖z - P z‖ ^ 2 := by
  have hi := coarse_lift_witness_identity P hP e F z he hF hz
  have hn := coarse_lift_norm_identity P hP e F he hF
  have hc := real_inner_mul_inner_self_le (F - e) (z - P z)
  rw [hi, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  nlinarith

/-- Positive target pairing forces a nonzero unresolved witness tail. -/
theorem coarse_lift_witness_residual_ne_zero (P : E →ₗ[ℝ] E)
    (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (e F z : E) (he : P e = e) (hF : P F = e)
    (hz : ⟪F, z⟫ = 0) (hez : ⟪e, z⟫ ≠ 0) : z - P z ≠ 0 := by
  intro hzero
  have hi := coarse_lift_witness_identity P hP e F z he hF hz
  rw [hzero, inner_zero_right] at hi
  exact hez (by linarith)

/-- Exact-lift lower bound with the genuine witness residual as denominator. -/
theorem coarse_lift_energy_lower_bound (P : E →ₗ[ℝ] E)
    (hP : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (e F z : E) (he : P e = e) (hF : P F = e)
    (hz : ⟪F, z⟫ = 0) (hez : ⟪e, z⟫ ≠ 0) :
    ‖e‖ ^ 2 + ⟪e, z⟫ ^ 2 / ‖z - P z‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  have hpos : 0 < ‖z - P z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr
    (coarse_lift_witness_residual_ne_zero P hP e F z he hF hz hez))
  have h := (div_le_iff₀ hpos).mpr
    (coarse_lift_energy_product P hP e F z he hF hz)
  linarith

end RiemannResearch.Analysis.CoarseLift
