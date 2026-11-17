import RiemannResearch.RH.ExactHeadGreenQuadraticCriterion
import RiemannResearch.RH.MobiusAffineDuality

/-!
# Conditional RH from the affine-residual Mobius dispersion budget

The observing Mobius vector may have any affine function removed before
measuring dispersion. Its own normal fit gives the smallest such factor.
Both analytic bounds must still hold at the same cofinal stages.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.Analysis.FiniteProfileEnergy
open MobiusHeadGreen
open RiemannResearch.RH.MobiusAffineProfile

/-- A direct signed budget avoids any compulsory full-mass Cauchy--Schwarz loss. -/
theorem riemannHypothesis_of_atom_signed_profile_deficit (h : ℕ → ℕ → ℝ)
    (δ k C B : ℝ) (hk : 0 ≤ k) (hgap : k < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      (signedSum x (atomProfile (greenPeriod x) x) - signedSum x (h x)) ^ 2 ≤
        k ^ 2 * atomEnergy (greenPeriod x) x ^ 2 + C * atomEnergy (greenPeriod x) x ∧
      signedSum x (h x) ≤ (1 - δ) * atomEnergy (greenPeriod x) x + B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_cofinal_signed_profile_deficit
    greenPeriod greenPeriod_gt primorialNormalCoefficients h
    (fun x => (primorialNormalCoefficients_spec x).1)
    (fun x => (primorialNormalCoefficients_spec x).2.1) ?_ δ k C B hk hgap hC ?_
  · intro x d hd hxd hc
    exact (primorialNormalCoefficients_spec x).2.2 d hd hxd
      ((primorialNormalCoefficients_spec x).2.1 d hd hc)
  · have hf (x : ℕ) : profile (greenPeriod x) (primorialNormalCoefficients x) =
        atomProfile (greenPeriod x) x := by
      funext d
      exact primorial_profile_eq_atomProfile x d
    simpa only [primorial_q_eq_atomEnergy, hf] using hdata

/-- The stagewise observer coefficients need not be optimal or uniformly bounded. -/
theorem riemannHypothesis_of_atom_affine_residual_deficit
    (c0 c1 a0 a1 : ℕ → ℝ)
    (δ k C B : ℝ) (hk : 0 ≤ k) (hgap : k < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      (∑ d ∈ Finset.Icc 1 x, weight d *
        (atomProfile (greenPeriod x) x d - c0 x - c1 x * ((d : ℝ) / x))) = 0 ∧
      (∑ d ∈ Finset.Icc 1 x, weight d * ((d : ℝ) / x) *
        (atomProfile (greenPeriod x) x d - c0 x - c1 x * ((d : ℝ) / x))) = 0 ∧
      affineLoss (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x)
        (fun d => (ArithmeticFunction.moebius d : ℝ)) (a0 x) (a1 x) *
      affineLoss (Finset.Icc 1 x) weight (fun d => (d : ℝ) / x)
        (atomProfile (greenPeriod x) x) (c0 x) (c1 x) ≤
          k ^ 2 * atomEnergy (greenPeriod x) x ^ 2 + C * atomEnergy (greenPeriod x) x ∧
      signedSum x (fun d => c0 x + c1 x * ((d : ℝ) / x)) ≤
        (1 - δ) * atomEnergy (greenPeriod x) x + B) : RiemannHypothesis := by
  apply riemannHypothesis_of_atom_signed_profile_deficit
    (fun x d => c0 x + c1 x * ((d : ℝ) / x)) δ k C B hk hgap hC
  intro J
  obtain ⟨x, hx, h0, h1, he, hm⟩ := hdata J
  exact ⟨x, hx, (profile_error_sq_le_affine_mobius_loss x
    (atomProfile (greenPeriod x) x) (c0 x) (c1 x) (a0 x) (a1 x) h0 h1).trans he, hm⟩

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
