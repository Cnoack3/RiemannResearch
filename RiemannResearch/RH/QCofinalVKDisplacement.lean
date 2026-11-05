/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCofinalProfileTransfer
import RiemannResearch.Analysis.CofinalLogCutoffs
import RiemannResearch.RH.QMertensUniformDefectSlope
import RiemannResearch.RH.QCofinalHarmonicWitness
import RiemannResearch.RH.QCofinalDisplacementMoments
import RiemannResearch.Analysis.VinogradovKorobovProfile

/-!
# Cofinal harmonic displacement bounds at the Vinogradov–Korobov scale

Bertrand's theorem gives legal heads at any fixed power below one half. Their exact signed pairings and vanishing complete tail costs transfer the ordinary Mertens estimate to a cofinal harmonic criterion.
-/

/-!
# Cofinal VK criterion for one-sided harmonic prefixes of the actual displacement

A legal head just above `X ^ θ`, with `θ < 1 / 2`, has a vanishing harmonic tail
cost. All rates strictly below `a (1 / 2) ^ (3 / 5)` follow by choosing θ close to
one half and the defect exponent strictly below the ordinary Mertens rate `a`.
-/
noncomputable section
open Filter
open scoped Topology BigOperators ENNReal

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability QSignedTailRigidity QAnnihilatorTailEscape
open RiemannResearch.Analysis RiemannResearch.Analysis.CofinalMoments
open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Any fixed fraction `θ < 1 / 2` yields the coefficient `c θ ^ (3 / 5)`.
The sign can vary at the cofinal cutoffs. -/
theorem witness_mean_zero_of_cofinal_vk_fraction (a c C θ b : ℝ)
    (hc : 0 < c) (hca : c < a) (hθ : 0 < θ) (hhalf : θ < 1 / 2)
    (hb : 0 ≤ b) (hgap : b < c * θ ^ (3 / 5 : ℝ))
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (hgood : ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ Real.exp (b * vkProfile (X : ℝ))) :
    inner ℝ qOne witness = 0 := by
  exact witness_mean_zero_of_cofinal_profile_fraction (fun X : ℕ => vkProfile (X : ℝ))
    c θ b (θ ^ (3 / 5 : ℝ)) hc hθ hhalf hb hgap
    (vkProfile_tendsto_atTop.comp tendsto_natCast_atTop_atTop)
    (QMertensFirstMoment.abs_defect_le_vk_cutoff_slope a c C hc hca hM)
    (vk_exists_scaled_head θ hθ (by linarith)) hgood

/-- The Mertens coefficient `a` yields all cofinal harmonic prefix rates
strictly below `(1 / 2) ^ (3 / 5) a`, with arbitrary changes of sign. -/
theorem riemannHypothesis_of_cofinal_vk_harmonic_prefix (a b C : ℝ)
    (hb : 0 ≤ b) (hba : b < a * (1 / 2 : ℝ) ^ (3 / 5 : ℝ))
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (hgood : ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ Real.exp (b * vkProfile (X : ℝ))) :
    RiemannHypothesis := by
  obtain ⟨θ, c, hθ, hhalf, hc, hca, hgap⟩ := exists_profile_cutoff_parameters (d := 3 / 5) (by norm_num) hb hba
  exact riemannHypothesis_of_witness_mean_zero
    (witness_mean_zero_of_cofinal_vk_fraction a c C θ b hc hca hθ hhalf hb hgap hM hgood)

/-- Literal extended-real lower limit on the nonnegative eventual growth ratio.
Using extended nonnegative reals also covers convergence to positive infinity. -/
theorem riemannHypothesis_of_liminf_vk_harmonic_prefix (a C : ℝ) (ha : 0 < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (h : Filter.liminf (fun X : ℕ => ENNReal.ofReal
      (Real.log (2 + minimumHarmonicPrefix X) / vkProfile (X : ℝ))) atTop <
        ENNReal.ofReal (a * (1 / 2 : ℝ) ^ (3 / 5 : ℝ))) : RiemannHypothesis := by
  have hV : Tendsto (fun X : ℕ => vkProfile (X : ℝ)) atTop atTop :=
    vkProfile_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨b, hb, hbt, hf⟩ := exists_frequently_exp_of_liminf_log_ratio_lt
    (H := minimumHarmonicPrefix) (φ := fun X : ℕ => vkProfile (X : ℝ))
    (by positivity) (hV.eventually (eventually_gt_atTop 0)) h
  exact riemannHypothesis_of_cofinal_vk_harmonic_prefix a b C hb.le hbt hM hf

/-- The Lee–Leong specialization uses precisely the published ordinary
Mertens bound in the repository's explicit input proposition. -/
theorem riemannHypothesis_of_leeLeong_liminf_harmonic_prefix
    (hM : QMertensFirstMoment.LeeLeongMertensEstimate)
    (h : Filter.liminf (fun X : ℕ => ENNReal.ofReal
      (Real.log (2 + minimumHarmonicPrefix X) / vkProfile (X : ℝ))) atTop <
        ENNReal.ofReal (QMertensFirstMoment.leeLeongRate * (1 / 2 : ℝ) ^ (3 / 5 : ℝ))) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_liminf_vk_harmonic_prefix QMertensFirstMoment.leeLeongRate 1 ?_
    (QMertensFirstMoment.mertens_vk_of_leeLeong hM) h
  unfold QMertensFirstMoment.leeLeongRate
  positivity

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
