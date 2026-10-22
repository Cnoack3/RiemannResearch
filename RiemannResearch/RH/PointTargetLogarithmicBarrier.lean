import RiemannResearch.RH.ParetoTailCapacity
import RiemannResearch.Analysis.PointLogarithmicTransfer

/-!
# The point-target logarithmic transfer and dyadic rate obstruction

Source: user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`, Section 19.
The external analytic input is J.-F. Burnol, "A lower bound in an
approximation problem involving the zeros of the Riemann zeta function",
Theorem 1.3, https://arxiv.org/pdf/math/0103058 . This source supports the
unformalized analytic provider, not an unconditional theorem in this file.

The generic scalar transfer and rate obstruction are proved in
`Analysis.PointLogarithmicTransfer`. This module specializes the rate theorem
to the actual point dictionary. Its analytic envelope is a proposition to be
supplied, not an axiom.
-/

noncomputable section
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.LogarithmicResidualBarrier

/-- The actual squared point error at largest modulus `2^(j+1)`. -/
def dyadicPointError (j : ℕ) : ℝ :=
  walkError residueAtom id (paretoPointHilbert 0) (2 ^ (j + 1) - 1)

theorem dyadicPointError_pos (j : ℕ) : 0 < dyadicPointError j :=
  TailCapacity.pointError_pos (2 ^ (j + 1) - 1)

/-- Open formalization obligation for Section 19.3. The classical Burnol
theorem and its comparison with this exact point dictionary are not supplied. -/
def PointBurnolLogLowerEnvelope : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
    c / Real.log (N : ℝ) ≤
      walkError residueAtom id (paretoPointHilbert 0) (N - 1)

private theorem index_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hp : 0 < 2 ^ k := pow_pos (by omega) k
    omega

/-- Specialization of the logarithmic envelope to the actual dyadic moduli.
This proves a transfer from the displayed hypothesis, not its provider. -/
theorem dyadic_point_envelope_of_log_envelope
    (h : PointBurnolLogLowerEnvelope) :
    ∃ c : ℝ, 0 < c ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      c / ((j : ℝ) + 1) ≤ dyadicPointError j := by
  obtain ⟨c, hc, N₀, hbound⟩ := h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c / Real.log 2, div_pos hc hl2, N₀, ?_⟩
  intro j hj
  have hp : 1 ≤ 2 ^ j := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hN : N₀ ≤ 2 ^ (j + 1) := by
    have hstep := index_le_two_pow j
    rw [pow_succ]
    omega
  have htwo : 2 ≤ 2 ^ (j + 1) := by
    rw [pow_succ]
    omega
  have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) =
      ((j : ℝ) + 1) * Real.log 2 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
      Nat.cast_add, Nat.cast_one]
  have hb := hbound (2 ^ (j + 1)) hN htwo
  rw [hlog] at hb
  change c / (((j : ℝ) + 1) * Real.log 2) ≤ dyadicPointError j at hb
  simpa only [div_div, mul_comm (Real.log 2) ((j : ℝ) + 1)] using hb

/-- Conditional point-target rate obstruction. Finite-stage positivity comes
from the actual tail-capacity theorem; the Burnol envelope is the analytic gap. -/
theorem point_no_fixed_dyadic_fraction
    (h : PointBurnolLogLowerEnvelope)
    (η : ℝ) (hη : 0 < η) (J : ℕ) :
    ∃ j, J ≤ j ∧ (1 - η) * dyadicPointError j < dyadicPointError (j + 1) := by
  obtain ⟨c, hc, N₀, hbound⟩ := dyadic_point_envelope_of_log_envelope h
  exact exists_late_failure_of_fixed_contraction
    dyadicPointError dyadicPointError_pos c hc N₀ hbound η hη J

end RiemannResearch.RH.Pareto.CoefficientStabilization
