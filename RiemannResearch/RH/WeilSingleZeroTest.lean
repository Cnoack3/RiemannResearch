import RiemannResearch.Analysis.FiniteTransformZeroRemoval
import RiemannResearch.Analysis.CompactLaplaceInterpolation
import RiemannResearch.RH.NymanTransformNullity
import RiemannResearch.RH.SmoothWeilMatrix

/-!
# An admissible smooth test isolating any one actual zeta zero

An explicit compact interpolation seed passes through the actual conductor-two
Nyman full return. Its transform vanishes at every actual zero and has finite
order at the chosen zero. Finite integral zero removal and normalization give
unit transform at that zero and zero at all the others. No RH, zero simplicity,
or spectral interpolation provider is assumed.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open scoped Topology

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section
set_option backward.isDefEq.respectTransparency false

open ZetaConductorRegularization

private theorem centeredTransform_const_mul (f : ℝ → ℂ) (c s : ℂ) :
    centeredTransform (fun x => c * f x) s = c * centeredTransform f s := by
  unfold centeredTransform transform
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- Every actual nontrivial zero has an actual smooth-superexponential
Kronecker test. Analytic multiplicity is removed, never assumed simple. -/
theorem exists_smooth_single_actual_zero_test (ρ : Zeta23.zetaZeroConfig.carrier) :
    ∃ g : ℝ → ℂ, SmoothSuperexponentialDecay g ∧
      centeredTransform g (ρ : ℂ) = 1 ∧
      ∀ σ : Zeta23.zetaZeroConfig.carrier, σ ≠ ρ →
        centeredTransform g (σ : ℂ) = 0 := by
  let v : ℝ → ℂ := compactLaplaceSeed (ρ : ℂ)
  have hv := compactLaplaceSeed_contDiff (ρ : ℂ)
  have hva := compactLaplaceSeed_zero_below (ρ : ℂ)
  have hvb := compactLaplaceSeed_zero_above (ρ : ℂ)
  let f : ℝ → ℂ := nymanFullReturn 2 v
  have hf : SmoothSuperexponentialDecay f :=
    smoothSuperexponentialDecay_nymanFullReturn hv hva hvb 2
  have hformula (s : ℂ) : centeredTransform f s =
      conductorZeta 2 s * centeredTransform v s :=
    centeredTransform_nymanFullReturn 2 hv hva hvb s
  have hHv : AnalyticAt ℂ (centeredTransform v) (ρ : ℂ) :=
    analyticAt_centeredTransform
      (hasExponentialMoments_of_compactSupport hv.continuous
        (compactLaplaceSeed_hasCompactSupport (ρ : ℂ))) (ρ : ℂ)
  have hvne : centeredTransform v (ρ : ℂ) ≠ 0 :=
    centeredTransform_compactLaplaceSeed_ne_zero (ρ : ℂ)
  have heq : centeredTransform f = conductorZeta 2 * centeredTransform v := by
    funext s
    exact hformula s
  have hfinite : analyticOrderAt (centeredTransform f) (ρ : ℂ) ≠ ⊤ := by
    rw [heq, analyticOrderAt_mul (analyticAt_conductorZeta 2 (by norm_num) _) hHv,
      hHv.analyticOrderAt_eq_zero.mpr hvne, add_zero]
    exact analyticOrderAt_conductorZeta_ne_top 2 (by norm_num) _
  have hzeros (σ : Zeta23.zetaZeroConfig.carrier) : centeredTransform f (σ : ℂ) = 0 := by
    have hs1 : (σ : ℂ) ≠ 1 := by
      intro h
      have hp := σ.property.2.2
      simp [h] at hp
    rw [hformula, conductorZeta_eq_zero_of_zeta_zero 2 hs1 σ.property.1, zero_mul]
  obtain ⟨g, hg, hgρ, hgzeros⟩ := exists_transform_zero_removed hf (ρ : ℂ) hfinite
  refine ⟨fun x => (centeredTransform g (ρ : ℂ))⁻¹ * g x,
    hg.const_mul _, ?_, ?_⟩
  · rw [centeredTransform_const_mul, inv_mul_cancel₀ hgρ]
  · intro σ hσ
    rw [centeredTransform_const_mul, hgzeros (σ : ℂ) ?_ (hzeros σ), mul_zero]
    intro he
    exact hσ (Subtype.ext he)

end
end RiemannResearch.RH.SignedWeilCorrelation
