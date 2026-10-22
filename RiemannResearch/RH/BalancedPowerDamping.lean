import RiemannResearch.RH.BalancedHeadInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual power-damped balanced sequence and its open analytic obligation

Source: user-provided argument, `RH_Minimal_Seeds_Continuation_20260916.md`,
Section 12. The finite pointwise sum below is the actual arithmetic sequence,
not the rational Mellin symbol. Hilbert nonmembership is recorded only as an
unproved proposition. `MinimalSeedPowerDamping` verifies the resonance algebra;
the infinite Mellin identity and pole realization still need formal providers.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Pointwise finite sum of the forced balanced coefficients damped by m^(-ε). -/
def balancedPowerDampedSequence (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    scalarBalancedCoefficient ⟨k + 1, Nat.succ_pos k⟩ hilbertOne *
      ((k + 1 : ℕ) : ℝ) ^ (-ε) * balancedSelected (k + 1) n

@[simp] theorem balancedPowerDampedSequence_zero (ε : ℝ) :
    balancedPowerDampedSequence ε 0 = 0 := by
  simp [balancedPowerDampedSequence]

/-- OPEN FORMALIZATION OBLIGATION: the intended nonmembership statement.
The actual Mellin bridge has not yet been checked in Lean.
This is a proposition definition, not an axiom or an asserted theorem. -/
def BalancedPowerDampingNonmembership : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ¬ Summable (fun n => positiveWeight n * balancedPowerDampedSequence ε n ^ 2)

end
end RiemannResearch.RH.Pareto
