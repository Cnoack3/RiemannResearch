import RiemannResearch.RH.DyadicProjectedResidueAbel
import RiemannResearch.RH.DyadicRegularizedSummability

/-!
# Complete signed Mobius sum of the exact residue Abel identities

Source: the fixed-conductor residue Abel identity proved in the sibling module
and the actual product-index norm summability established in
`DyadicSignedMeanEnergyVerification20260910(1).md` and its dependencies.

The entire signed residue bracket is retained inside every conductor summand.
Its norm summability follows from the already summable original product series.
No separate convergence of either residue component, no uniform estimate as
damping vanishes, and no legal-closure or RH conclusion is asserted.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- One full signed conductor contribution after the exact projected Abel
telescope. Both residue terms stay together before the outer sum is taken. -/
def dyadicRegularizedResidueAbelTerm (ε : ℝ) (m : ℕ) : ThresholdHilbert :=
  ((ArithmeticFunction.moebius (m + 1) : ℝ) / (m + 1 : ℝ) ^ (1 + ε)) •
    (-dyadicQuotientProjection (hilbertResidue (m + 1) (by positivity)) +
      (1 - triadicDampingRatio ε) •
        ∑' j : ℕ, triadicDampingRatio ε ^ j •
          dyadicQuotientProjection
            (hilbertResidue ((m + 1) * 3 ^ (j + 1)) (by positivity)))

/-- The full signed Abel bracket equals the genuinely convergent original
triadic row for this conductor, including a possibly zero Mobius coefficient. -/
theorem dyadicRegularizedResidueAbelTerm_eq_tsum
    {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    dyadicRegularizedResidueAbelTerm ε m =
      ∑' j : ℕ, dyadicRegularizedTerm ε (m, j) := by
  unfold dyadicRegularizedResidueAbelTerm
  rw [← dyadicProjectedTriadicColumn_tsum_eq (m + 1) (by positivity) hε]
  have hs := (dyadicProjectedTriadicColumn_summable (m + 1) (by positivity) hε).hasSum.const_smul
      ((ArithmeticFunction.moebius (m + 1) : ℝ) / (m + 1 : ℝ) ^ (1 + ε))
  simpa only [dyadicRegularizedTerm, dyadicRegularizationCoefficient, smul_smul]
    using hs.tsum_eq.symm

/-- The outer Mobius series of full signed residue brackets is norm absolutely
summable. Its two residue components need not be estimated separately. -/
theorem dyadicRegularizedResidueAbelTerm_norm_summable
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ => ‖dyadicRegularizedResidueAbelTerm ε m‖) := by
  have hp := dyadicRegularizedTerm_norm_summable hε
  have hmajor : Summable (fun m : ℕ =>
      ∑' j : ℕ, ‖dyadicRegularizedTerm ε (m, j)‖) := hp.prod
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ hmajor
  intro m
  rw [dyadicRegularizedResidueAbelTerm_eq_tsum hε m]
  apply norm_tsum_le_tsum_norm
  exact hp.comp_injective (fun a b h => by simpa using congrArg Prod.snd h)

/-- The complete signed conductor series has its ordinary Hilbert meaning. -/
theorem dyadicRegularizedResidueAbelTerm_summable
    {ε : ℝ} (hε : 0 < ε) :
    Summable (dyadicRegularizedResidueAbelTerm ε) :=
  (dyadicRegularizedResidueAbelTerm_norm_summable hε).of_norm

/-- Exact global residue Abel representation of the actual regularized
arithmetic vector. All signed conductor contributions remain bundled. -/
theorem dyadicRegularizedFamily_eq_residueAbel
    {ε : ℝ} (hε : 0 < ε) :
    dyadicRegularizedFamily ε =
      dyadicRegularizationNormalization ε •
        ∑' m : ℕ, dyadicRegularizedResidueAbelTerm ε m := by
  unfold dyadicRegularizedFamily
  congr 1
  rw [(dyadicRegularizedTerm_summable hε).tsum_prod]
  exact tsum_congr (fun m => (dyadicRegularizedResidueAbelTerm_eq_tsum hε m).symm)

end
end RiemannResearch.RH.Pareto
