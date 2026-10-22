import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact Hilbert-space geometry of a phase witness

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, 8 September 2026,
Section 6, Theorem `thm:pythagoras`. This proves the geometric inference from
a witness, including the exact excess and the equality case. Construction
of the actual arithmetic vector `r_a` and its annihilation property is a
separate domain-specific obligation; it is not supplied by this module.
-/

namespace RiemannResearch.Analysis.PhaseWitness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The squared norm of the witness, with its exact scalar normalization. -/
theorem normalized_witness_norm (u r : E) (μ C : ℝ)
    (hu : ‖u‖^2 = 1) (hr : ‖r‖^2 = C)
    (hur : ⟪u, r⟫ = μ) (hC : C ≠ 0) :
    ‖u - (μ / C) • r‖^2 = 1 - μ^2 / C := by
  have hp : ‖(μ / C) • r‖^2 = (μ / C)^2 * C := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hr]
  rw [norm_sub_sq_real, hu, hp, real_inner_smul_right, hur]
  field_simp
  <;> ring

/-- Exact decomposition, retaining the complete arithmetic excess. -/
theorem error_eq_floor_add_excess (u r F : E) (μ C : ℝ)
    (hu : ‖u‖^2 = 1) (hr : ‖r‖^2 = C)
    (hur : ⟪u, r⟫ = μ) (hC : C ≠ 0)
    (hann : ⟪F, u - (μ / C) • r⟫ = 0) :
    ‖u - F‖^2 = (1 - μ^2 / C) + ‖F - (μ / C) • r‖^2 := by
  have hp : ‖(μ / C) • r‖^2 = (μ / C)^2 * C := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hr]
  have hid : (μ / C)^2 * C = μ^2 / C := by
    field_simp
  rw [inner_sub_right] at hann
  have huF : ⟪u, F⟫ = ⟪F, (μ / C) • r⟫ := by
    rw [real_inner_comm]
    linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, hu, hp, hid, huF]
  ring

/-- The quantitative lower bound follows after, rather than before, the
full signed error identity. -/
theorem error_ge_floor (u r F : E) (μ C : ℝ)
    (hu : ‖u‖^2 = 1) (hr : ‖r‖^2 = C)
    (hur : ⟪u, r⟫ = μ) (hC : C ≠ 0)
    (hann : ⟪F, u - (μ / C) • r⟫ = 0) :
    1 - μ^2 / C ≤ ‖u - F‖^2 := by
  rw [error_eq_floor_add_excess u r F μ C hu hr hur hC hann]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Equality at the phase floor has exactly one possible vector. -/
theorem error_eq_floor_iff (u r F : E) (μ C : ℝ)
    (hu : ‖u‖^2 = 1) (hr : ‖r‖^2 = C)
    (hur : ⟪u, r⟫ = μ) (hC : C ≠ 0)
    (hann : ⟪F, u - (μ / C) • r⟫ = 0) :
    ‖u - F‖^2 = 1 - μ^2 / C ↔ F = (μ / C) • r := by
  rw [error_eq_floor_add_excess u r F μ C hu hr hur hC hann]
  constructor
  · intro h
    have hn : ‖F - (μ / C) • r‖^2 = 0 := by linarith
    have hz : ‖F - (μ / C) • r‖ = 0 := by nlinarith [norm_nonneg (F - (μ / C) • r)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro h
    rw [h, sub_self, norm_zero]
    ring

end RiemannResearch.Analysis.PhaseWitness
