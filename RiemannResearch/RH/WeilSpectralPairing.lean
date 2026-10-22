import RiemannResearch.RH.WeilNoncompactExplicitFormula
import RiemannResearch.RH.NymanMixedSpectralNullity
import RiemannResearch.RH.AutocorrelationHalfMass

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The exact sesquilinear Weil formula, with multiplicity-preserving reindexing

The pairing is the actual literal arithmetic expression of a cross-correlation.
The zero-side identity is proved from the full explicit formula, the actual
correlation transform, and reflection of actual analytic zero multiplicities.
The argument retains the note's conjugate-linear-first-variable convention.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open scoped ComplexConjugate BigOperators

namespace RiemannResearch.RH.WeilExplicitFormula

private theorem one_sub_mem (ρ : Zeta23.zetaZeroConfig.carrier) :
    1 - (ρ : ℂ) ∈ Zeta23.zetaZeroConfig.carrier := by
  have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.property
  refine ⟨riemannZeta_one_sub_eq_zero_of_strip hρ.1 hρ.2.1 hρ.2.2, ?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re]
    linarith [hρ.2.2]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith [hρ.2.1]

def actualZeroOneSub : Zeta23.zetaZeroConfig.carrier ≃ Zeta23.zetaZeroConfig.carrier where
  toFun ρ := ⟨1 - (ρ : ℂ), one_sub_mem ρ⟩
  invFun ρ := ⟨1 - (ρ : ℂ), one_sub_mem ρ⟩
  left_inv ρ := by apply Subtype.ext; change 1 - (1 - (ρ : ℂ)) = (ρ : ℂ); ring
  right_inv ρ := by apply Subtype.ext; change 1 - (1 - (ρ : ℂ)) = (ρ : ℂ); ring

theorem zeroMult_actualZeroOneSub (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.zeroMult (actualZeroOneSub ρ) = Zeta23.zeroMult ρ := by
  change (analyticOrderAt riemannZeta (1 - (ρ : ℂ))).toNat =
    (analyticOrderAt riemannZeta (ρ : ℂ)).toNat
  rw [Zeta23.analyticOrderAt_zeta_one_sub ρ.property.2.1 ρ.property.2.2]

def actualZeroReflect : Zeta23.zetaZeroConfig.carrier ≃ Zeta23.zetaZeroConfig.carrier where
  toFun ρ := ⟨Zeta23.reflect ρ, Zeta23.zeta_reflect_zero ρ ρ.property⟩
  invFun ρ := ⟨Zeta23.reflect ρ, Zeta23.zeta_reflect_zero ρ ρ.property⟩
  left_inv ρ := by apply Subtype.ext; simp [Zeta23.reflect]
  right_inv ρ := by apply Subtype.ext; simp [Zeta23.reflect]

theorem zeroMult_actualZeroReflect (ρ : Zeta23.zetaZeroConfig.carrier) :
    Zeta23.zeroMult (actualZeroReflect ρ) = Zeta23.zeroMult ρ :=
  Zeta23.zeta_mult_reflect ρ ρ.property

end RiemannResearch.RH.WeilExplicitFormula

namespace RiemannResearch.RH.SignedWeilCorrelation

open WeilExplicitFormula

/-- The complete arithmetic sesquilinear pairing, conjugate-linear in f. -/
noncomputable def arithmeticWeilPairing (f g : ℝ → ℂ) : ℂ :=
  Zeta23.EF.literatureRHS (RiemannResearch.Analysis.crossCorrelation g f)

private theorem actualZeroOneSub_summand {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g)
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    (Zeta23.zeroMult (actualZeroOneSub ρ) : ℂ) *
      Zeta23.paperFT (RiemannResearch.Analysis.crossCorrelation g f)
        (Zeta23.gammaOf (actualZeroOneSub ρ)) =
    (Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform f (1 - conj (ρ : ℂ))) *
      centeredTransform g (ρ : ℂ) := by
  rw [zeroMult_actualZeroOneSub, paperFT_gammaOf_eq_centeredTransform,
    centeredTransform_crossCorrelation
      (hg.decay.hasExponentialMoments hg.1.continuous)
      (hf.decay.hasExponentialMoments hf.1.continuous) hg.1.continuous hf.1.continuous]
  change (Zeta23.zeroMult ρ : ℂ) *
      (centeredTransform g (1 - (1 - (ρ : ℂ))) *
        conj (centeredTransform f (1 - conj (1 - (1 - (ρ : ℂ)))))) = _
  rw [show 1 - (1 - (ρ : ℂ)) = (ρ : ℂ) by ring]
  ring

/-- Absolute convergence of the precise product series in equation (2.5). -/
theorem summable_norm_arithmeticWeilPairing_zero_terms {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      ‖(Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform f (1 - conj (ρ : ℂ))) *
        centeredTransform g (ρ : ℂ)‖) := by
  have hs := (summable_norm_actual_zero_terms (hg.crossCorrelation hf)).comp_injective
    actualZeroOneSub.injective
  exact hs.congr (fun ρ => congrArg norm (actualZeroOneSub_summand hf hg ρ))

/-- The exact note convention: multiplicity times conjugate M f(1−conj ρ)
times M g(ρ), with the complete arithmetic pairing on the other side. -/
theorem arithmeticWeilPairing_eq_zero_sum {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g) :
    arithmeticWeilPairing f g =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform f (1 - conj (ρ : ℂ))) *
          centeredTransform g (ρ : ℂ) := by
  unfold arithmeticWeilPairing
  rw [← actual_noncompact_literal_Weil_explicit_formula (hg.crossCorrelation hf)]
  calc
    _ = ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult (actualZeroOneSub ρ) : ℂ) *
          Zeta23.paperFT (RiemannResearch.Analysis.crossCorrelation g f)
            (Zeta23.gammaOf (actualZeroOneSub ρ)) := (actualZeroOneSub.tsum_eq _).symm
    _ = _ := tsum_congr (actualZeroOneSub_summand hf hg)

/-- Reflection of actual zeros and multiplicities proves Hermitian symmetry. -/
theorem arithmeticWeilPairing_hermitian {f g : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (hg : SmoothSuperexponentialDecay g) :
    arithmeticWeilPairing f g = conj (arithmeticWeilPairing g f) := by
  rw [arithmeticWeilPairing_eq_zero_sum hf hg, arithmeticWeilPairing_eq_zero_sum hg hf]
  calc
    _ = ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult (actualZeroReflect ρ) : ℂ) *
          conj (centeredTransform f (1 - conj (actualZeroReflect ρ : ℂ))) *
            centeredTransform g (actualZeroReflect ρ : ℂ) := (actualZeroReflect.tsum_eq _).symm
    _ = ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        conj ((Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform g (1 - conj (ρ : ℂ))) *
          centeredTransform f (ρ : ℂ)) := by
      apply tsum_congr
      intro ρ
      rw [zeroMult_actualZeroReflect]
      change (Zeta23.zeroMult ρ : ℂ) *
        conj (centeredTransform f (1 - conj (1 - conj (ρ : ℂ)))) *
          centeredTransform g (1 - conj (ρ : ℂ)) = _
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = _ := by simpa only [starRingEnd_apply] using
      (tsum_star (f := fun ρ : Zeta23.zetaZeroConfig.carrier =>
        (Zeta23.zeroMult ρ : ℂ) * conj (centeredTransform g (1 - conj (ρ : ℂ))) *
          centeredTransform f (ρ : ℂ))).symm

/-- The diagonal is exactly the original real spatial arithmetic form. -/
theorem arithmeticWeilPairing_self_eq {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) :
    arithmeticWeilPairing f f =
      (infinitePrimePowerCorrelationValue
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) (realAutocorrelation f) : ℂ) := by
  have hc := hf.crossCorrelation hf
  have heven (t : ℝ) : (RiemannResearch.Analysis.crossCorrelation f f (-t)).re =
      (RiemannResearch.Analysis.crossCorrelation f f t).re := by
    change realAutocorrelation f (-t) = realAutocorrelation f t
    exact realAutocorrelation_neg f t
  have h := actual_noncompact_Weil_explicit_formula_of_smooth hc heven
  rw [actual_noncompact_literal_Weil_explicit_formula hc] at h
  have hh := congrArg Complex.im (arithmeticWeilPairing_hermitian hf hf)
  simp only [Complex.conj_im] at hh
  apply Complex.ext
  · exact h
  · simp only [Complex.ofReal_im]
    linarith

end RiemannResearch.RH.SignedWeilCorrelation
