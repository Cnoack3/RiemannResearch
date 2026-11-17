import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.Analysis.GreenProfileQuadratic

/-!
# Conditional RH criterion with a strict quadratic dispersion gap
The actual gcd-atom optimizer may satisfy W E <= k^2 q^2 + C q, with
0 <= k < delta, instead of the previous W E <= C q hypothesis.
The one-sided signed moment m <= (1-delta)q+B is retained.
These analytic estimates remain open; all finite arithmetic providers are supplied.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.MobiusHeadGreen
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.GreenProfileBounds
open RiemannResearch.RH.ExactHeadGreenProfile
open FloorProfileExtension

theorem riemannHypothesis_of_cofinal_signed_profile_deficit
    (P : ℕ → ℕ) (hP : ∀ x, x < P x) (c h : ℕ → ℕ → ℝ)
    (hlow : ∀ x d, 1 ≤ d → d ≤ x → c x d = (ArithmeticFunction.moebius d : ℝ))
    (hdiv : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), c x d ≠ 0 → d ∣ P x)
    (hupper : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), x < d → c x d ≠ 0 →
      score (Finset.Icc 1 (P x - 1)) (progressionWeight (P x)) (residual (P x) (c x)) d = 0)
    (δ k C B : ℝ) (hk : 0 ≤ k) (hgap : k < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      (MobiusAffineProfile.signedSum x (profile (P x) (c x)) -
        MobiusAffineProfile.signedSum x (h x)) ^ 2 ≤ k ^ 2 * q (P x) (c x) ^ 2 + C * q (P x) (c x) ∧
      MobiusAffineProfile.signedSum x (h x) ≤ (1 - δ) * q (P x) (c x) + B) :
    RiemannHypothesis := by
  have hPpos (x : ℕ) : 0 < P x := lt_of_le_of_lt (Nat.zero_le x) (hP x)
  let hd := fun x d (hd : d ∈ Finset.Icc 1 (P x)) => (Finset.mem_Icc.mp hd).1
  let f (x : ℕ) := hilbertExtension (P x) (hPpos x) (Finset.Icc 1 (P x)) (c x) (hd x)
  choose n hn he hm using hdata
  refine riemannHypothesis_of_bounded_exact_head_residuals (Set.Ici 1)
    (by intro a ha; exact ha) (fun J => f (n J))
    (fun J => hilbertExtension_legal _ _ _ _ _) ?_
    (1 + (2 * (δ - k) * B + 2 * C + 2) / (δ - k) ^ 2) ?_
  · intro J k hk hkJ
    apply hilbertExtension_head (P (n J)) (hPpos (n J)) _ (c (n J)) _ (n J) (hP (n J))
      (mobius_floor_head (P (n J)) (n J) (hP (n J)).le (c (n J)) (hlow (n J)))
    · exact hk
    · exact hkJ.trans (hn J)
  · intro J
    let x := n J
    have hq := q_nonneg (P x) (c x)
    have ht : tau (P x) (c x) ^ 2 ≤ 1 * q (P x) (c x) := by
      have hh := actual_tail_charge (P x) x (hPpos x) (hP x).le (c x) (hlow x)
      have hh' : q (P x) (c x) / ((x : ℝ) + 1) ≤ q (P x) (c x) :=
        div_le_self hq (by have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x; linarith)
      simpa using hh.trans hh'
    have herr := he J
    have hqb := energy_scaled_le_of_quadratic_profile_deficit hq hk hgap hC
      (show (0 : ℝ) ≤ 1 by norm_num)
      (signed_root_identity (P x) x (hP x).le (c x) (hlow x) (hupper x))
      ht herr (hm J)
    have hterm : progressionWeight (P x) (P x) ≤ 1 := by
      have hh := Finset.single_le_sum (s := Finset.Icc 1 (P x))
        (f := progressionWeight (P x)) (fun r _ => progressionWeight_nonneg _ r)
        (Finset.mem_Icc.mpr ⟨hPpos x, le_rfl⟩)
      simpa [ExactHeadGreen.period_mass (P x) (hPpos x)] using hh
    change ‖hilbertOne - hilbertExtension (P x) (hPpos x) _ (c x) _‖ ^ 2 ≤ _
    rw [actual_energy_split (P x) (hPpos x) (c x) (hdiv x)]
    have hd2 : 0 < (δ - k) ^ 2 := sq_pos_of_pos (sub_pos.mpr hgap)
    have heq : q (P x) (c x) ≤ (2 * (δ - k) * B + 2 * C + 2) / (δ - k) ^ 2 := by
      apply (le_div_iff₀ hd2).mpr
      nlinarith only [hqb]
    linarith only [hterm, heq]

/-- The full-mass estimate is a sufficient special case of the signed criterion. -/
theorem riemannHypothesis_of_cofinal_quadratic_mobius_profile_deficit
    (P : ℕ → ℕ) (hP : ∀ x, x < P x) (c h : ℕ → ℕ → ℝ)
    (hlow : ∀ x d, 1 ≤ d → d ≤ x → c x d = (ArithmeticFunction.moebius d : ℝ))
    (hdiv : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), c x d ≠ 0 → d ∣ P x)
    (hupper : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), x < d → c x d ≠ 0 →
      score (Finset.Icc 1 (P x - 1)) (progressionWeight (P x)) (residual (P x) (c x)) d = 0)
    (δ k C B : ℝ) (hk : 0 ≤ k) (hgap : k < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      mass (Finset.Icc 1 x) MobiusAffineProfile.weight *
        energy (Finset.Icc 1 x) MobiusAffineProfile.weight
          (fun d => profile (P x) (c x) d - h x d) ≤ k ^ 2 * q (P x) (c x) ^ 2 + C * q (P x) (c x) ∧
      MobiusAffineProfile.signedSum x (h x) ≤ (1 - δ) * q (P x) (c x) + B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_signed_profile_deficit P hP c h hlow hdiv hupper
    δ k C B hk hgap hC
  intro J
  obtain ⟨x, hx, he, hm⟩ := hdata J
  exact ⟨x, hx, (MobiusAffineProfile.profile_error_sq_le x
    (profile (P x) (c x)) (h x)).trans he, hm⟩

end RiemannResearch.RH.Pareto.MobiusHeadGreen

namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.Analysis.FiniteProfileEnergy
open MobiusHeadGreen

/-- Only the jointly cofinal analytic bounds remain as research obligations. -/
theorem riemannHypothesis_of_atom_quadratic_profile_deficit (h : ℕ → ℕ → ℝ)
    (δ k C B : ℝ) (hk : 0 ≤ k) (hgap : k < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      mass (Finset.Icc 1 x) MobiusAffineProfile.weight *
        energy (Finset.Icc 1 x) MobiusAffineProfile.weight
          (fun d => atomProfile (greenPeriod x) x d - h x d) ≤
            k ^ 2 * atomEnergy (greenPeriod x) x ^ 2 + C * atomEnergy (greenPeriod x) x ∧
      MobiusAffineProfile.signedSum x (h x) ≤
        (1 - δ) * atomEnergy (greenPeriod x) x + B) : RiemannHypothesis := by
  refine riemannHypothesis_of_cofinal_quadratic_mobius_profile_deficit
    greenPeriod greenPeriod_gt primorialNormalCoefficients h
    (fun x => (primorialNormalCoefficients_spec x).1)
    (fun x => (primorialNormalCoefficients_spec x).2.1) ?_ δ k C B hk hgap hC ?_
  · intro x d hd hxd hc
    exact (primorialNormalCoefficients_spec x).2.2 d hd hxd
      ((primorialNormalCoefficients_spec x).2.1 d hd hc)
  · simpa only [primorial_q_eq_atomEnergy, primorial_profile_eq_atomProfile] using hdata

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
