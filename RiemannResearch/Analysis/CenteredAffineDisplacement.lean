/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact centered affine-displacement remainder

Source: the user-provided CRT/Ramanujan/Pareto agenda, Priority 3, and the
centered proof developed in this continuation. This extends the internal
`QShiftedReciprocalBounds.displacement_energy_remainder` to an arbitrary
centered response parameter. The related metric-angle setting is discussed
by Lin and Sinnamon, *The generalized Wielandt inequality*,
https://www.math.uwo.ca/faculty/sinnamon/pdf/wielandt.pdf ; the identity below
is proved directly and uses no theorem from that paper.

The intended RH consumer takes `m = H + 2`, `x` to be the tail of the Q
minimum-energy exact-head interpolant, and `d` to be its displacement to the
Pareto minimizer on the same affine set. This identity supplies an exact
nonnegative remainder, not an arithmetic bound on either minimum energy.
-/

noncomputable section
namespace RiemannResearch.Analysis.CenteredAffineDisplacement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scaled centered response, requiring no linearity for this identity. -/
def centeredResponse (B : E → E) (m : ℝ) (y : E) : E :=
  (2 * m) • B y - y

/-- Exact centered pairing for an orthogonal displacement satisfying its
normal equation. -/
theorem centered_pairing (B : E → E) (m : ℝ) (x d : E)
    (horth : inner ℝ d x = 0)
    (hnormal : inner ℝ d (B (x + d)) = ‖d‖ ^ 2) :
    inner ℝ d (centeredResponse B m (x + d)) =
      (2 * m - 1) * ‖d‖ ^ 2 := by
  unfold centeredResponse
  rw [inner_sub_right, inner_smul_right, inner_add_right, hnormal,
    horth, zero_add, real_inner_self_eq_norm_sq]
  ring

/-- Exact energy remainder. When the centered response contracts at `x+d`,
both terms on the right are nonnegative. -/
theorem displacement_energy_remainder (B : E → E) (m : ℝ) (x d : E)
    (horth : inner ℝ d x = 0)
    (hnormal : inner ℝ d (B (x + d)) = ‖d‖ ^ 2) :
    ‖x‖ ^ 2 - 4 * m * (m - 1) * ‖d‖ ^ 2 =
      (‖x + d‖ ^ 2 - ‖centeredResponse B m (x + d)‖ ^ 2) +
      ‖centeredResponse B m (x + d) - (2 * m - 1) • d‖ ^ 2 := by
  have hc : inner ℝ (centeredResponse B m (x + d)) d =
      (2 * m - 1) * ‖d‖ ^ 2 := by
    rw [real_inner_comm]
    exact centered_pairing B m x d horth hnormal
  have hsum : ‖x + d‖ ^ 2 = ‖x‖ ^ 2 + ‖d‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_comm, horth]
    ring
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_right, hc, hsum]
  ring

/-- The sharp squared bound follows by discarding the two exact nonnegative
remainders. No positivity assumption on `m` is needed for this implication. -/
theorem sharp_displacement_energy_bound (B : E → E) (m : ℝ) (x d : E)
    (horth : inner ℝ d x = 0)
    (hnormal : inner ℝ d (B (x + d)) = ‖d‖ ^ 2)
    (hcenter : ‖centeredResponse B m (x + d)‖ ≤ ‖x + d‖) :
    4 * m * (m - 1) * ‖d‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have he := displacement_energy_remainder B m x d horth hnormal
  have hs := mul_self_le_mul_self (norm_nonneg _) hcenter
  nlinarith [sq_nonneg
    ‖centeredResponse B m (x + d) - (2 * m - 1) • d‖]

end RiemannResearch.Analysis.CenteredAffineDisplacement
