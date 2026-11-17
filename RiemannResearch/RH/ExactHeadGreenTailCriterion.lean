import RiemannResearch.RH.ExactHeadGreenAffineCriterion
import RiemannResearch.RH.ExactHeadMomentTail

/-!
# Conditional RH from a tail-only affine moment probe

Source: the user's exact-head Green memorandum, agenda R4/R5, and the
repository's signed-profile deficit criterion. The head contributes exactly
zero to the signed observation and is absent from the required probe budget.
Dispersion and tail control are still independent analytic obligations and
must hold at the same cofinal stages.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.MobiusAffineProfile
open MobiusHeadGreen

/-- No coefficient compactness, bounded-q premise, or head-energy bound is used. -/
theorem riemannHypothesis_of_atom_affine_tail_probe
    (c0 c1 : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (alpha eps k C M : ℝ) (heps : 0 < eps) (hk : 0 ≤ k)
    (hgap : k < 1 - alpha - eps) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hdata : ∀ J, ∃ x, J ≤ x ∧ 2 ≤ x ∧
      mass (Finset.Icc 1 x) weight * c0 x +
        (∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x)) * c1 x =
        ∑ d ∈ Finset.Icc 1 x, weight d * atomProfile (greenPeriod x) x d ∧
      (∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x)) * c0 x +
        energy (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x) * c1 x =
        ∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x) *
          atomProfile (greenPeriod x) x d ∧
      v x ∈ upperSpan (greenPeriod x) x (atom (greenPeriod x)) ∧
      (signedSum x (atomProfile (greenPeriod x) x) -
        signedSum x (fun d => c0 x + c1 x * ((d : ℝ) / x))) ^ 2 ≤
        k ^ 2 * atomEnergy (greenPeriod x) x ^ 2 + C * atomEnergy (greenPeriod x) x ∧
      centeredMomentTailEnergy x alpha (v x) ≤ M) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_atom_signed_profile_deficit
    (fun x d => c0 x + c1 x * ((d : ℝ) / x))
    (1 - alpha - eps) k C (M / (4 * eps)) hk hgap hC
  intro J
  obtain ⟨x, hxJ, hx, h0, h1, hv, hd, ht⟩ := hdata J
  refine ⟨x, hxJ, hd, ?_⟩
  rw [fitted_moment_eq_probe (greenPeriod x) x hx (c0 x) (c1 x) h0 h1]
  have hm := fitted_moment_deficit_of_tail_probe_bound x alpha M eps hM heps (v x) hv ht
  convert hm using 1 <;> ring

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
