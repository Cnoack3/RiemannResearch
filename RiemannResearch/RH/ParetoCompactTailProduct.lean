/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoActualSpectralResolvent
import Mathlib.Topology.Order.OrderClosed

/-!
# Actual compact trial-tail product and sharp defect obstruction

Source: user-requested source-resolvent continuation, 7 October 2026.
The exact signed projection identity is already established in
ParetoTrialTailConditions. This module assembles its literal compact trial
and complete constructed spectrum. Both full physical tails are retained.
The cofinal vanishing-product RH consumer is a conditional research reduction:
its sole arithmetic provider remains Open.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis
open FiniteSpectralBudget FiniteHeadTailSpectralRealization

def compactFourfoldSignedTailPairing (m : ℕ) : ℝ :=
  twoThreeTrialTailPairing (4 * m + 4)
    (compactCorrectedHilbert (4 * m + 4) (by omega))

def compactFourfoldTailProduct (m : ℕ) : ℝ :=
  ‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2 *
    optimizerTail Finset.univ (compactSpectrumWeight (4 * m))
      (compactSpectrumEigenvalue (4 * m))

private theorem fourfold_cutoff_atTop :
    Tendsto (fun m : ℕ => 4 * m + 4) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with m hm
  omega

private theorem fourfold_stage_atTop :
    Tendsto (fun m : ℕ => 4 * m + 3) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with m hm
  omega

private theorem fourfold_index_atTop :
    Tendsto (fun m : ℕ => 4 * m) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with m hm
  omega

/-- Reciprocal cancellation supplies the actual compact trial's vanishing
physical head mismatch; the complete physical tail is not estimated here. -/
theorem compactCorrectedHilbert_fourfold_head_norm_tendsto_zero :
    Tendsto (fun m : ℕ => ‖twoThreeDual - compactHead (4 * m + 4)
      (compactCorrectedHilbert (4 * m + 4) (by omega))‖) atTop (𝓝 0) := by
  have hcharge : Tendsto (fun m : ℕ => (compactReciprocalSum (4 * m + 4)) ^ 2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by norm_num : 2 ≠ 0)] using
      (compactReciprocalSum_tendsto_zero.comp fourfold_cutoff_atTop).pow 2
  have hsq : Tendsto (fun m : ℕ => ‖twoThreeDual - compactHead (4 * m + 4)
      (compactCorrectedHilbert (4 * m + 4) (by omega))‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun m => sq_nonneg _) _ hcharge
    intro m
    have h := compactCorrectedHilbert_head_energy_le_charge_sq (4 * m + 4) (by omega)
    rw [compactHead_sub, compactHead_twoThreeDual (4 * m + 4) (by omega)] at h
    exact h
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- The signed whole trial/optimizer tail pairing has exactly the surviving
closed-span defect as its limit, unconditionally. Cancellation and both full
physical tails are retained before the limiting argument. -/
theorem compactFourfoldSignedTailPairing_tendsto_defect :
    Tendsto compactFourfoldSignedTailPairing atTop (𝓝 compactProjectionDefect) := by
  let D : ℕ → ℝ := fun m => ‖twoThreeDualResidual (4 * m + 3)‖ ^ 2
  let H : ℕ → ℝ := fun m => inner ℝ
    (compactHead (4 * m + 4) (twoThreeDualResidual (4 * m + 3)))
    (twoThreeDual - compactHead (4 * m + 4)
      (compactCorrectedHilbert (4 * m + 4) (by omega)))
  let E : ℕ → ℝ := fun m => ‖twoThreeDual - compactHead (4 * m + 4)
    (compactCorrectedHilbert (4 * m + 4) (by omega))‖
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖ ^ 2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  have hd : Tendsto D atTop (𝓝 compactProjectionDefect) := hd0.comp fourfold_stage_atTop
  have hhead : ∀ᶠ m in atTop, |H m| ≤ ‖twoThreeDual‖ * E m := by
    apply Filter.Eventually.of_forall
    intro m
    simpa only [H, E, show 4 * m + 4 - 1 = 4 * m + 3 by omega] using
      twoThree_actual_trial_head_pair_abs_le (4 * m + 4)
        (compactCorrectedHilbert (4 * m + 4) (by omega))
  have hid : ∀ m, D m = H m + compactFourfoldSignedTailPairing m := by
    intro m
    simpa only [D, H, compactFourfoldSignedTailPairing, twoThreeTrialTailPairing,
      show 4 * m + 4 - 1 = 4 * m + 3 by omega] using
      twoThree_actual_trial_signed_identity (4 * m + 4) (by omega)
        (compactCorrectedHilbert (4 * m + 4) (by omega))
        (compactCorrectedHilbert_mem_conductorStage (4 * m + 4) (by omega))
  exact HeadTailStrengthening.signed_tail_tendsto_of_head_error_bound
    D H compactFourfoldSignedTailPairing E compactProjectionDefect ‖twoThreeDual‖
    hd compactCorrectedHilbert_fourfold_head_norm_tendsto_zero hhead hid

/-- Coefficient-one Cauchy budget for the actual complete compact source.
All optimizer and trial physical-tail values and every conductor remain. -/
theorem compactFourfoldSignedTailPairing_sq_le_product (m : ℕ) :
    (compactFourfoldSignedTailPairing m) ^ 2 ≤ compactFourfoldTailProduct m := by
  let u := compactCorrectedHilbert (4 * m + 4) (by omega)
  have hc := twoThreeTrialTailPairing_sq_le (4 * m + 4) u
  have hopt :
      ‖(finiteSpace (4 * m + 3)).starProjection twoThreeDual -
        compactHead (4 * m + 4)
          ((finiteSpace (4 * m + 3)).starProjection twoThreeDual)‖ ^ 2 =
      optimizerTail Finset.univ (compactSpectrumWeight (4 * m))
        (compactSpectrumEigenvalue (4 * m)) := by
    simpa only [compactSpectrumWeight, compactSpectrumEigenvalue] using
      actualOptimizerTail_eq_spectral (4 * m + 3) (4 * m + 4) (by omega)
        twoThreeDual (compactHead_twoThreeDual (4 * m + 4) (by omega))
  rw [show 4 * m + 4 - 1 = 4 * m + 3 by omega, hopt] at hc
  have htrialtail : ‖u - compactHead (4 * m + 4) u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    nlinarith [compactHead_pythagoras (4 * m + 4) u,
      sq_nonneg ‖compactHead (4 * m + 4) u‖]
  have hS : 0 ≤ optimizerTail Finset.univ (compactSpectrumWeight (4 * m))
      (compactSpectrumEigenvalue (4 * m)) :=
    optimizerTail_nonneg Finset.univ _ _
      (fun i _ => compactSpectrumWeight_nonneg (4 * m) i)
      (fun i _ => compactSpectrumEigenvalue_nonneg (4 * m) i)
  exact hc.trans (mul_le_mul_of_nonneg_right htrialtail hS)

/-- Unconditional sharp product floor. A positive surviving defect forces
the actual compact trial/tail product to stay above every smaller constant.
No upper product provider or RH premise is introduced. -/
theorem compactFourfoldTailProduct_lower_floor
    (a : ℝ) (ha : a < compactProjectionDefect ^ 2) :
    ∀ᶠ m in atTop, a < compactFourfoldTailProduct m := by
  have h := compactFourfoldSignedTailPairing_tendsto_defect.pow 2
  filter_upwards [h.eventually_const_lt ha] with m hm
  exact hm.trans_le (compactFourfoldSignedTailPairing_sq_le_product m)

/-- Actual complete-source RH consumer. The one remaining arithmetic input
is cofinal vanishing of trial full energy times actual optimizer tail square. -/
theorem riemannHypothesis_of_compactFourfold_cofinal_tailProduct
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (hprod : Tendsto (fun m => compactFourfoldTailProduct (k m)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hle : compactProjectionDefect ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto
      ((compactFourfoldSignedTailPairing_tendsto_defect.comp hk).pow 2) hprod
      (Filter.Eventually.of_forall (fun m =>
        compactFourfoldSignedTailPairing_sq_le_product (k m)))
  have hz : compactProjectionDefect = 0 :=
    sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖ ^ 2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

/-- Subsequence-free arithmetic provider: arbitrarily late small products
are sufficient, with all source weights and full physical tails retained. -/
theorem riemannHypothesis_of_compactFourfold_arbitrarily_late_small_tailProduct
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ M : ℕ,
      ∃ m : ℕ, M ≤ m ∧ compactFourfoldTailProduct m ≤ ε) : RiemannHypothesis := by
  have hz := HeadTailStrengthening.limit_eq_zero_of_arbitrarily_late_small_tail_product
    compactFourfoldSignedTailPairing
    (fun m => ‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2)
    (fun m => optimizerTail Finset.univ (compactSpectrumWeight (4 * m))
      (compactSpectrumEigenvalue (4 * m)))
    compactProjectionDefect compactFourfoldSignedTailPairing_tendsto_defect
    (Filter.Eventually.of_forall compactFourfoldSignedTailPairing_sq_le_product) hsmall
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖ ^ 2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

/-- A strict fractional product saving is enough. The product itself need
not be shown to vanish independently; the surviving squared correction is
the quantity being absorbed. The budget remains an open arithmetic input. -/
theorem riemannHypothesis_of_compactFourfold_cofinal_product_fraction
    (k : ℕ → ℕ) (E : ℕ → ℝ) (theta : ℝ)
    (hk : Tendsto k atTop atTop) (htheta : theta < 1)
    (hE : Tendsto E atTop (𝓝 0))
    (hbudget : ∀ᶠ m in atTop,
      compactFourfoldTailProduct (k m) ≤
        theta * (correction Finset.univ (compactSpectrumWeight (4 * k m))
          (compactSpectrumEigenvalue (4 * k m))) ^ 2 + E m) :
    RiemannHypothesis := by
  have hL := (compactFourfoldSignedTailPairing_tendsto_defect.comp hk).pow 2
  have hT := (compactSpectrum_correction_tendsto_defect.comp
    (fourfold_index_atTop.comp hk)).pow 2
  have hrhs := (hT.const_mul theta).add hE
  have hbound : ∀ᶠ m in atTop,
      (compactFourfoldSignedTailPairing (k m)) ^ 2 ≤
        theta * (correction Finset.univ (compactSpectrumWeight (4 * k m))
          (compactSpectrumEigenvalue (4 * k m))) ^ 2 + E m := by
    filter_upwards [hbudget] with m hm
    exact (compactFourfoldSignedTailPairing_sq_le_product (k m)).trans hm
  have hle : compactProjectionDefect ^ 2 ≤ theta * compactProjectionDefect ^ 2 := by
    simpa only [Function.comp_def, add_zero] using
      le_of_tendsto_of_tendsto hL hrhs hbound
  have hfactor : 0 < 1 - theta := sub_pos.mpr htheta
  have hzero : (1 - theta) * compactProjectionDefect ^ 2 = 0 := by
    apply le_antisymm
    · nlinarith only [hle]
    · exact mul_nonneg hfactor.le (sq_nonneg _)
  have hz : compactProjectionDefect = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hfactor))
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖ ^ 2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0


/-- Finite complete-source product estimate obtained from the exact resolvent
tangent remainder. Zero trial energy and zero optimizer tail are included. -/
theorem compactFourfold_correction_add_tail_le_trial_product (m : ℕ) :
    correction Finset.univ (compactSpectrumWeight (4 * m))
      (compactSpectrumEigenvalue (4 * m)) +
    optimizerTail Finset.univ (compactSpectrumWeight (4 * m))
      (compactSpectrumEigenvalue (4 * m)) ≤
    (compactReciprocalSum (4 * m + 4)) ^ 2 +
      2 * Real.sqrt (compactFourfoldTailProduct m) := by
  exact correction_add_tail_le_trial_product Finset.univ _ _
    (compactReciprocalSum (4 * m + 4))
    (‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2)
    (fun i _ => compactSpectrumWeight_nonneg (4 * m) i)
    (fun i _ => compactSpectrumEigenvalue_nonneg (4 * m) i)
    (sq_nonneg _) (fun t ht => compactSpectrum_fourfold_sourceDeficit_le_trial m t ht)

/-- If a positive defect survives, conductor times the literal optimizer-tail
square diverges to infinity. The full signed pairing is used before Cauchy;
the supplied sublinear full trial energy then forces this precise obstruction. -/
theorem compactFourfold_conductor_tail_tendsto_atTop_of_defect_pos
    (hδ : 0 < compactProjectionDefect) :
    Tendsto (fun m : ℕ => ((4 * m + 4 : ℕ) : ℝ) *
      optimizerTail Finset.univ (compactSpectrumWeight (4 * m))
        (compactSpectrumEigenvalue (4 * m))) atTop atTop := by
  apply HeadTailStrengthening.tail_energy_tendsto_atTop_of_positive_correction
    compactFourfoldSignedTailPairing _
    (fun m : ℕ => ‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2 /
      (4 * m + 4 : ℕ)) compactProjectionDefect hδ
    compactFourfoldSignedTailPairing_tendsto_defect
    compactCorrectedHilbert_fourfold_sublinear
  · exact Filter.Eventually.of_forall (fun m =>
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  · apply Filter.Eventually.of_forall
    intro m
    have hN : ((4 * m + 4 : ℕ) : ℝ) ≠ 0 := by positivity
    have heq : (((4 * m + 4 : ℕ) : ℝ) *
      optimizerTail Finset.univ (compactSpectrumWeight (4 * m))
        (compactSpectrumEigenvalue (4 * m))) *
        (‖compactCorrectedHilbert (4 * m + 4) (by omega)‖ ^ 2 /
          (4 * m + 4 : ℕ)) = compactFourfoldTailProduct m := by
      unfold compactFourfoldTailProduct
      field_simp [hN]
    rw [heq]
    exact compactFourfoldSignedTailPairing_sq_le_product m

end RiemannResearch.RH.Pareto.CoefficientStabilization
