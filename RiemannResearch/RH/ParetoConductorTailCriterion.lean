/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoActualSpectralResolvent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A cofinal conductor-times-tail sufficient condition for RH

Conditional research reduction. Source: the user-requested actual-source
resolvent work, 7 October 2026. The source-escape providers are proved in
ParetoActualSpectralResolvent.lean; the displayed arithmetic bound on the
actual complete optimizer tail remains Open. This is a sufficient condition;
no converse or unconditional RH conclusion is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis
open FiniteSpectralBudget

private theorem fourfold_stage_tendsto :
    Tendsto (fun m : ℕ => 4*m) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with m hm
  omega

/-- A concrete OPEN arithmetic sufficient condition: the actual complete
optimizer-tail square, multiplied by the conductor, stays bounded along an
explicit cofinal subsequence of fourfold stages. No such bound is proved here. -/
theorem riemannHypothesis_of_compactSpectrum_fourfold_cofinal_bounded_tail
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ᶠ m in atTop,
      ((4*k m+4 : ℕ) : ℝ) * optimizerTail Finset.univ
        (compactSpectrumWeight (4*k m)) (compactSpectrumEigenvalue (4*k m)) ≤ B) :
    RiemannHypothesis := by
  have hstage : Tendsto (fun m => 4*k m) atTop atTop :=
    fourfold_stage_tendsto.comp hk
  have hT : Tendsto (fun m => correction Finset.univ
      (compactSpectrumWeight (4*k m)) (compactSpectrumEigenvalue (4*k m)))
      atTop (𝓝 compactProjectionDefect) :=
    compactSpectrum_correction_tendsto_defect.comp hstage
  have hS : Tendsto (fun m => optimizerTail Finset.univ
      (compactSpectrumWeight (4*k m)) (compactSpectrumEigenvalue (4*k m)))
      atTop (𝓝 0) := compactSpectrum_optimizerTail_tendsto_zero.comp hstage
  have hδc : ∀ c : ℝ, 0 < c → compactProjectionDefect ≤ c*B := by
    intro c hc
    have hM : Tendsto (fun m => highMass Finset.univ
        (compactSpectrumWeight (4*k m)) (compactSpectrumEigenvalue (4*k m))
        (c * (4*k m+4 : ℕ))) atTop (𝓝 0) :=
      (compactSpectrum_fourfold_highMass_conductor_tendsto_zero c hc).comp hk
    have hR : Tendsto (fun m => optimizerTail Finset.univ
        (compactSpectrumWeight (4*k m)) (compactSpectrumEigenvalue (4*k m)) +
        c*B + highMass Finset.univ
          (compactSpectrumWeight (4*k m)) (compactSpectrumEigenvalue (4*k m))
          (c * (4*k m+4 : ℕ))) atTop (𝓝 (c*B)) := by
      simpa only [zero_add, add_zero] using
        (hS.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => c*B) atTop (𝓝 (c*B)))).add hM
    have hineq : ∀ᶠ m in atTop,
        correction Finset.univ (compactSpectrumWeight (4*k m))
          (compactSpectrumEigenvalue (4*k m)) ≤
        optimizerTail Finset.univ (compactSpectrumWeight (4*k m))
          (compactSpectrumEigenvalue (4*k m)) + c*B +
        highMass Finset.univ (compactSpectrumWeight (4*k m))
          (compactSpectrumEigenvalue (4*k m)) (c * (4*k m+4 : ℕ)) := by
      filter_upwards [hbudget] with m hm
      have ht := correction_le_threshold_tail_add_highMass Finset.univ
        (compactSpectrumWeight (4*k m)) (compactSpectrumEigenvalue (4*k m))
        (c * (4*k m+4 : ℕ))
        (fun i _ => compactSpectrumWeight_nonneg (4*k m) i)
        (fun i _ => compactSpectrumEigenvalue_nonneg (4*k m) i) (by positivity)
      have hm' := mul_le_mul_of_nonneg_left hm hc.le
      nlinarith only [ht, hm']
    exact le_of_tendsto_of_tendsto hT hR hineq
  have hδ0 : 0 ≤ compactProjectionDefect := sq_nonneg _
  have hδle : compactProjectionDefect ≤ 0 := by
    by_contra hnot
    have hδpos : 0 < compactProjectionDefect := lt_of_not_ge hnot
    let c : ℝ := compactProjectionDefect / (2*(B+1))
    have hc : 0 < c := by dsimp [c]; positivity
    have hh := hδc c hc
    have hh' : compactProjectionDefect ≤ compactProjectionDefect*B/(2*(B+1)) := by
      simpa only [c, div_mul_eq_mul_div] using hh
    have hden : 0 < 2*(B+1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hh'
    have hprod : 0 ≤ compactProjectionDefect*B := mul_nonneg hδ0 hB
    nlinarith only [hmul, hδpos, hprod]
  have hz : compactProjectionDefect = 0 := le_antisymm hδle hδ0
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

/-- The simpler whole-fourfold-sequence variant of the same OPEN tail budget. -/
theorem riemannHypothesis_of_compactSpectrum_fourfold_bounded_tail
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ᶠ m in atTop,
      ((4*m+4 : ℕ) : ℝ) * optimizerTail Finset.univ
        (compactSpectrumWeight (4*m)) (compactSpectrumEigenvalue (4*m)) ≤ B) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_compactSpectrum_fourfold_cofinal_bounded_tail
    id tendsto_id B hB hbudget

end RiemannResearch.RH.Pareto.CoefficientStabilization
