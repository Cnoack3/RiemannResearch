import RiemannResearch.Analysis.FirstMomentTails
import RiemannResearch.RH.ParetoSummableTailRigidity
/-!
# First absolute moment uniqueness for actual Pareto annihilators
Source: user-provided RH_Regression_Analytic_Repair_20260911, tail uniqueness
argument. The moment assumption is in the original physical coordinates.
The proof derives summable tails and weighted-tail decay, then invokes actual
dyadic orthogonality; no Fourier regularity hypothesis is used.
-/

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
theorem legalAnnihilator_eq_zero_of_coefficient_firstMoment
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hm : Summable (fun n : ℕ => (n : ℝ)*|signedCoefficient h n|))
    {n : ℕ} (hn : 0 < n) : h n = 0 := by
  have ha := signedCoefficient_summable hh.1
  have hraw : Summable (signedTail h) := rawTail_summable_of_firstMoment _ ha hm
  have hanch : Summable (anchoredSignedTail h) := by
    apply hraw.abs.of_norm_bounded
    intro k
    by_cases hk : k = 0
    · simp [anchoredSignedTail, hk]
    · simp [anchoredSignedTail, hk, Real.norm_eq_abs]
  have hlim := weighted_rawTail_tendsto_zero_of_firstMoment _ ha hm
  have hw : Filter.Tendsto (fun k : ℕ => (k : ℝ)*anchoredSignedTail h k)
      Filter.atTop (nhds 0) := by
    convert hlim using 1
    funext k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [anchoredSignedTail, signedTail, hk]
  exact legalAnnihilator_eq_zero_of_weighted_tail_tendsto hS hh hanch hw hn

/-- The first absolute moment in the original physical coordinates. -/
theorem legalAnnihilator_eq_zero_of_first_absolute_moment
    {S : Set ℕ} (hS : 2 ∈ S) {h : ℕ → ℝ} (hh : LegalAnnihilator S h)
    (hm : Summable (fun n : ℕ => |h n|/((n : ℝ)+1)))
    {n : ℕ} (hn : 0 < n) : h n = 0 := by
  apply legalAnnihilator_eq_zero_of_coefficient_firstMoment hS hh _ hn
  apply hm.of_norm_bounded
  intro k
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_mul, norm_zero]
    positivity
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hkR' : (k : ℝ)+1 ≠ 0 := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Nat.cast_nonneg k)]
    unfold signedCoefficient
    rw [abs_mul, abs_of_nonneg (positiveWeight_nonneg k)]
    unfold positiveWeight
    apply le_of_eq
    field_simp
end RiemannResearch.RH.Pareto
