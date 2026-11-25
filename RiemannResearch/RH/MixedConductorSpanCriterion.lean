import RiemannResearch.RH.QComplementDensitySeparation
import RiemannResearch.RH.RamanujanPointwiseCriterion
import RiemannResearch.RH.QComplementZeroDimension
import RiemannResearch.RH.RealZetaNonvanishing
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.BaezDuarteNaturalApproximation

/-!
# The mixed-conductor spanning condition and conjugate zero pairs

The density change embeds the real Q orthogonal complement into the real
Pareto complement. Each nonreal right-hand zero and its conjugate give two
independent Mellin functionals, so containment of the Pareto complement in
one real line implies RH. The mixed-conductor splitting identifies precisely
which residual would have to span that complement.

Source: Christian Noack's proposed mixed-conductor split and the repository's
zero-functional dimension theorem. The final identification of the screened
line with the constants uses the reverse implication of L. Báez-Duarte,
*A strengthening of the Nyman-Beurling criterion for the Riemann hypothesis*,
https://arxiv.org/abs/math/0205003, as an explicit argument.
-/

noncomputable section
namespace RiemannResearch.RH.ParetoComplementTransfer
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open QDensityMetric QDensityMetricInverse
open Pareto.CoefficientStabilization
open scoped InnerProductSpace

private theorem fullMap_eq :
    QFullResidueProjection.closure.map toParetoLinear = closedSpace := by
  have hm (f : QHilbert) : f ∈ QFullResidueProjection.closure ↔ toPareto f ∈ closedSpace := by
    simpa only [toPareto_residueAtom, QFullResidueProjection.closure,
      QFullResidueProjection.legalSpan, closedSpace,
      RiemannResearch.Analysis.ExhaustiveWalk.dictionaryClosure] using
      mem_closure_span_iff (fun i : ℕ => qResidue (i + 2)) f
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (hm g).mp hg
  · intro hf
    exact ⟨toQ f, (hm _).mpr (by simpa using hf), toPareto_toQ f⟩

private def complementMap :
    QComplementZeroDimension.W →ₗ[ℝ] closedSpaceᗮ :=
  ((toParetoLinear.comp B.toLinearMap).comp QComplementZeroDimension.W.subtype).codRestrict _ (by
    intro u
    have he := QComplementDensitySeparation.pareto_orthogonal_eq_density_image
    rw [fullMap_eq] at he
    have hu : B u.val ∈ QComplementDensitySeparation.U.map B.toLinearMap :=
      ⟨u.val, u.property, rfl⟩
    rw [← he] at hu
    exact hu)

private theorem complementMap_injective : Function.Injective complementMap := by
  intro u v h
  apply Subtype.ext
  apply densityEquiv.injective
  apply paretoEquiv.injective
  exact congrArg Subtype.val h

theorem fullComplement_dimension_transfer [FiniteDimensional ℝ closedSpaceᗮ]
    (h : Module.finrank ℝ closedSpaceᗮ ≤ 1) :
    FiniteDimensional ℝ QComplementZeroDimension.W ∧
      Module.finrank ℝ QComplementZeroDimension.W ≤ 1 :=
  ⟨FiniteDimensional.of_injective complementMap complementMap_injective,
    (LinearMap.finrank_le_finrank_of_injective complementMap_injective).trans h⟩

theorem fullComplement_dimension_of_line (v : ThresholdHilbert)
    (hline : closedSpaceᗮ ≤ Submodule.span ℝ {v}) :
    FiniteDimensional ℝ QComplementZeroDimension.W ∧
      Module.finrank ℝ QComplementZeroDimension.W ≤ 1 := by
  classical
  have hi := Submodule.inclusion_injective hline
  letI : FiniteDimensional ℝ closedSpaceᗮ :=
    FiniteDimensional.of_injective (Submodule.inclusion hline) hi
  apply fullComplement_dimension_transfer
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans
    ((finrank_span_le_card ({v} : Set ThresholdHilbert)).trans (by simp))

end RiemannResearch.RH.ParetoComplementTransfer

open scoped ComplexConjugate
open RiemannResearch.RH

namespace RiemannResearch.RH.QComplementZeroDimension

/-- Nonreal right zeros occur with their distinct conjugates, and the
positive real strip has no zeta zeros. Thus at most one right zero is
equivalent to RH. -/
theorem riemannHypothesis_iff_subsingleton_rightZero : RiemannHypothesis ↔ Subsingleton RightZero := by
  constructor
  · intro h
    refine ⟨fun u _ => False.elim ?_⟩
    exact riemannHypothesis_iff_right_half_strip_zero_free.mp h u
      u.property.1 u.property.2.1 u.property.2.2
  · intro h
    apply riemannHypothesis_iff_right_half_strip_zero_free.mpr
    intro s hs h1 hz
    have hreal : s.im ≠ 0 := by
      intro hi
      have he : (s.re : ℂ) = s := Complex.ext (by simp) (by simpa using hi.symm)
      exact (riemannZeta_ofReal_ne_zero s.re (by linarith) (by linarith)) (he.symm ▸ hz)
    have hdiff : s ≠ conj s := by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.conj_im] at hi
      exact hreal (by linarith)
    let u : RightZero := ⟨s, hs, h1, hz⟩
    let v : RightZero := ⟨conj s, by simpa using hs, by simpa using h1,
      by simp [riemannZeta_conj, hz]⟩
    exact hdiff (congrArg Subtype.val (h.elim u v))

theorem rh_of_finrank_le_one [FiniteDimensional ℝ W] (hdim : Module.finrank ℝ W ≤ 1) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_subsingleton_rightZero.mpr
  refine ⟨fun u v => ?_⟩
  by_contra hne
  let f : Bool → RightZero := fun b => if b then v else u
  have hf : Function.Injective f := by
    intro a b he
    cases a <;> cases b
    · rfl
    · exact False.elim (hne he)
    · exact False.elim (hne he.symm)
    · rfl
  have h := rightZero_family_card_le_finrank f hf
  norm_num at h
  omega

end RiemannResearch.RH.QComplementZeroDimension

namespace RiemannResearch.RH.ParetoComplementTransfer
open Pareto Pareto.CoefficientStabilization

theorem riemannHypothesis_of_pareto_complement_le_line (z : ThresholdHilbert)
    (hline : closedSpaceᗮ ≤ Submodule.span ℝ {z}) : RiemannHypothesis := by
  obtain ⟨hfinite, hdim⟩ := fullComplement_dimension_of_line z hline
  letI : FiniteDimensional ℝ QComplementZeroDimension.W := hfinite
  exact QComplementZeroDimension.rh_of_finrank_le_one hdim

end RiemannResearch.RH.ParetoComplementTransfer

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The proposed mixed-complement spanning identity suffices for RH. -/
theorem riemannHypothesis_of_mixed_orthogonal_span_one
    (hspan : mixedClosureᗮ = screenedPrimeClosure ⊔ Submodule.span ℝ {hilbertOne}) :
    RiemannHypothesis :=
  RiemannResearch.RH.ParetoComplementTransfer.riemannHypothesis_of_pareto_complement_le_line
    limitResidual (mixed_orthogonal_span_one_iff_residual_spans.mp hspan).le

/-- With the published reverse natural approximation implication, the spanning
hypothesis identifies the screened line with the constant line. -/
theorem screened_eq_span_one_of_mixed_orthogonal_span_one
    (hspan : mixedClosureᗮ = screenedPrimeClosure ⊔ Submodule.span ℝ {hilbertOne})
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    screenedPrimeClosure = Submodule.span ℝ {hilbertOne} := by
  have hmem := BaezDuarte.one_mem_of_riemannHypothesis hBaezDuarte
    (riemannHypothesis_of_mixed_orthogonal_span_one hspan)
  rw [screenedPrimeClosure_eq_span_two, one_mem_closedSpace_iff_normalizedScreenedTwo.mp hmem]

end RiemannResearch.RH.Pareto.PrimePowerSchur
