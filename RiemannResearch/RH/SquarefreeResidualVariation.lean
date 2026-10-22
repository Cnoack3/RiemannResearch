/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import RiemannResearch.RH.SquarefreeResidualSampling
import RiemannResearch.Analysis.ProjectionResidualVariation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- The Apache-specific header convention does not determine project licensing.
set_option linter.style.header false

/-!
# Sharp total variation for the actual squarefree insertion law

Source: user-provided DPP residual-law continuation, equations (4)--(5),
October 2026. This specializes the generic coordinate theorem to the
existing Pareto residuals and their existing physical `siteMass` definition.
Every squarefree conductor in the stage is retained. No RH assertion occurs.

-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.SquarefreeSampling
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.CoordinateSquareVariation
open RiemannResearch.Analysis.ProjectionResidualSampling

theorem normalized_residual_coordinate_square (n i : ℕ) :
    ((normalized (residual n)) i) ^ 2 = siteMass n i := by
  have hn : ‖residual n‖ ≠ 0 := norm_ne_zero_iff.mpr (residual_ne_zero n)
  rw [siteMass, hilbertGibbsPhysical_square]
  change (‖residual n‖⁻¹ * (residual n i)) ^ 2 = (residual n i) ^ 2/‖residual n‖ ^ 2
  field_simp [hn]

/-- The complete physical insertion laws obey the sharp energy-drop bound;
the left side is the ordinary half-l1 total variation squared. -/
theorem siteMass_totalVariation_sq_le {n m : ℕ} (hnm : n ≤ m) :
    ((∑' i : ℕ, |siteMass n i-siteMass m i|)/2) ^ 2 ≤
      (energy n-energy m)/energy n := by
  have hST : finiteSpace n ≤ finiteSpace m := walkSpan_mono atom id hnm
  have h := nested_residual_coordinateTV_sq_le
    (finiteSpace n) (finiteSpace m) hST hilbertOne
    (residual_ne_zero n) (residual_ne_zero m)
  change (coordinateTV (normalized (residual n)) (normalized (residual m))) ^ 2 ≤
    (energy n-energy m)/energy n at h
  unfold coordinateTV at h
  simpa only [normalized_residual_coordinate_square] using h

/-- A finite-head version retains the absolute coordinate differences,
before summing signs into an event probability. -/
theorem siteMass_finiteVariation_sq_le {n m : ℕ} (hnm : n ≤ m) (A : Finset ℕ) :
    (∑ i ∈ A, |siteMass n i-siteMass m i|) ^ 2 ≤
      4*(energy n-energy m)/energy n := by
  have hu := normalized_norm_sq (residual n) (residual_ne_zero n)
  have hv := normalized_norm_sq (residual m) (residual_ne_zero m)
  have h := finite_coordinate_variation_sq_le
    (normalized (residual n)) (normalized (residual m)) hu hv A
  have hST : finiteSpace n ≤ finiteSpace m := walkSpan_mono atom id hnm
  have hi := normalized_nested_residual_inner
    (finiteSpace n) (finiteSpace m) hST hilbertOne
    (residual_ne_zero n) (residual_ne_zero m)
  change inner ℝ (normalized (residual n)) (normalized (residual m)) =
    ‖residual m‖/‖residual n‖ at hi
  rw [hi] at h
  simp only [normalized_residual_coordinate_square] at h
  have hn : ‖residual n‖ ≠ 0 := norm_ne_zero_iff.mpr (residual_ne_zero n)
  have hid : 4*(1-(‖residual m‖/‖residual n‖) ^ 2) =
      4*(energy n-energy m)/energy n := by
    unfold energy
    field_simp [hn]
  rwa [hid] at h

/-- Nonzero limiting energy is precisely the hypothesis needed to normalize
the actual closed-space residual. -/
theorem limitResidual_ne_zero_of_limitEnergy_ne_zero
    (hE : limitingError atom hilbertOne ≠ 0) : limitResidual ≠ 0 := by
  intro hR
  apply hE
  change ‖limitResidual‖ ^ 2 = 0
  simp only [hR, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- The limiting coordinate law has exactly the original physical Pareto
weights. Coordinate zero of the anchored physical sequence is already
omitted by the established `hilbertGibbsPhysical` indexing. -/
theorem normalized_limitResidual_coordinate_square (i : ℕ)
    (hE : limitingError atom hilbertOne ≠ 0) :
    ((normalized limitResidual) i) ^ 2 = limitingSiteMass i := by
  have hn : ‖limitResidual‖ ≠ 0 := norm_ne_zero_iff.mpr
    (limitResidual_ne_zero_of_limitEnergy_ne_zero hE)
  rw [limitingSiteMass, hilbertGibbsPhysical_square]
  change (‖limitResidual‖⁻¹ * (limitResidual i)) ^ 2 =
    (limitResidual i) ^ 2/‖limitResidual‖ ^ 2
  field_simp [hn]

/-- The full insertion law approaches its actual limiting physical law with
the sharp covariance bound of paper equation (4). The limiting energy is
explicitly assumed nonzero; no target-membership or RH claim is made. -/
theorem siteMass_limiting_totalVariation_sq_le (n : ℕ)
    (hE : limitingError atom hilbertOne ≠ 0) :
    ((∑' i : ℕ, |siteMass n i-limitingSiteMass i|)/2) ^ 2 ≤
      (energy n-limitingError atom hilbertOne)/energy n := by
  have h := nested_residual_coordinateTV_sq_le
    (finiteSpace n) closedSpace (finiteSpace_le_closedSpace n) hilbertOne
    (residual_ne_zero n) (limitResidual_ne_zero_of_limitEnergy_ne_zero hE)
  change (coordinateTV (normalized (residual n)) (normalized limitResidual)) ^ 2 ≤
    (energy n-limitingError atom hilbertOne)/energy n at h
  unfold coordinateTV at h
  simpa only [normalized_residual_coordinate_square,
    normalized_limitResidual_coordinate_square _ hE] using h

theorem limitingSiteMass_summable : Summable limitingSiteMass := by
  unfold limitingSiteMass
  exact (hilbertGibbsPhysical_square_summable limitResidual).div_const _

theorem limitingSiteMass_tsum
    (hE : limitingError atom hilbertOne ≠ 0) :
    (∑' i, limitingSiteMass i) = 1 := by
  simp only [limitingSiteMass, tsum_div_const, hilbertGibbsPhysical_square]
  rw [← hilbert_norm_sq]
  change ‖limitResidual‖ ^ 2 / ‖limitResidual‖ ^ 2 = 1
  exact div_self (by change limitingError atom hilbertOne ≠ 0; exact hE)

open RiemannResearch.Analysis.ExhaustiveWalk

theorem siteMass_totalVariation_le_sqrt {n m : ℕ} (hnm : n ≤ m) :
    (∑' i : ℕ, |siteMass n i - siteMass m i|) / 2 ≤
      Real.sqrt ((energy n - energy m) / energy n) := by
  have h := siteMass_totalVariation_sq_le hnm
  have hnonneg : 0 ≤ (∑' i : ℕ, |siteMass n i - siteMass m i|) / 2 :=
    div_nonneg (tsum_nonneg (fun i => abs_nonneg _)) (by norm_num)
  exact (Real.le_sqrt hnonneg (le_trans (sq_nonneg _) h)).mpr h

theorem siteMass_limiting_totalVariation_le_sqrt (n : ℕ)
    (hE : limitingError atom hilbertOne ≠ 0) :
    (∑' i : ℕ, |siteMass n i - limitingSiteMass i|) / 2 ≤
      Real.sqrt ((energy n - limitingError atom hilbertOne) / energy n) := by
  have h := siteMass_limiting_totalVariation_sq_le n hE
  have hnonneg : 0 ≤ (∑' i : ℕ, |siteMass n i - limitingSiteMass i|) / 2 :=
    div_nonneg (tsum_nonneg (fun i => abs_nonneg _)) (by norm_num)
  exact (Real.le_sqrt hnonneg (le_trans (sq_nonneg _) h)).mpr h

theorem siteMass_limiting_totalVariation_tendsto_zero
    (hE : limitingError atom hilbertOne ≠ 0) :
    Tendsto (fun n => (∑' i : ℕ, |siteMass n i - limitingSiteMass i|) / 2)
      atTop (𝓝 0) := by
  have hR : Tendsto
      (fun n => (energy n - limitingError atom hilbertOne) / energy n)
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => limitingError atom hilbertOne)
        atTop (𝓝 (limitingError atom hilbertOne)) := tendsto_const_nhds
    have ht : Tendsto
        (fun n => (energy n - limitingError atom hilbertOne) / energy n)
        atTop (𝓝 ((limitingError atom hilbertOne -
          limitingError atom hilbertOne) / limitingError atom hilbertOne)) :=
      (energy_tendsto.sub hc).div energy_tendsto hE
    simpa only [sub_self, zero_div] using ht
  have hs : Tendsto
      (fun n => ((∑' i : ℕ, |siteMass n i - limitingSiteMass i|) / 2) ^ 2)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun n => sq_nonneg _)
      (fun n => siteMass_limiting_totalVariation_sq_le n hE) hR
  have hnonneg (n : ℕ) :
      0 ≤ (∑' i : ℕ, |siteMass n i - limitingSiteMass i|) / 2 :=
    div_nonneg (tsum_nonneg (fun i => abs_nonneg _)) (by norm_num)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hs
  have hfun :
      (fun n => Real.sqrt
        (((∑' i : ℕ, |siteMass n i - limitingSiteMass i|) / 2) ^ 2)) =
      (fun n => (∑' i : ℕ, |siteMass n i - limitingSiteMass i|) / 2) := by
    funext n
    exact Real.sqrt_sq (hnonneg n)
  simpa only [Function.comp_def, hfun, Real.sqrt_zero] using hsqrt

theorem siteMass_eq_limiting_plus_projectionError_signedCross
    (n i : ℕ) (hE :
      RiemannResearch.Analysis.ExhaustiveWalk.limitingError atom hilbertOne ≠ 0) :
    siteMass n i =
      (RiemannResearch.Analysis.ExhaustiveWalk.limitingError atom hilbertOne /
        energy n) * limitingSiteMass i +
      paretoWeight i *
        (hilbertGibbsPhysical
          (closedSpace.starProjection hilbertOne -
            (finiteSpace n).starProjection hilbertOne) i) ^ 2 / energy n +
      2 * paretoWeight i * hilbertGibbsPhysical limitResidual i *
        hilbertGibbsPhysical
          (closedSpace.starProjection hilbertOne -
            (finiteSpace n).starProjection hilbertOne) i / energy n := by
  have hsplit : residual n = limitResidual +
      (closedSpace.starProjection hilbertOne -
        (finiteSpace n).starProjection hilbertOne) := by
    unfold residual limitResidual
    abel
  have hphysical : hilbertGibbsPhysical (residual n) i =
      hilbertGibbsPhysical limitResidual i +
        hilbertGibbsPhysical
          (closedSpace.starProjection hilbertOne -
            (finiteSpace n).starProjection hilbertOne) i := by
    have hp := congrArg (physicalEvaluationCLM i) hsplit
    rw [map_add] at hp
    simpa only [physicalEvaluationCLM_apply, ← hilbertGibbsPhysical_eq] using hp
  have hn : energy n ≠ 0 := ne_of_gt (energy_pos n)
  unfold siteMass limitingSiteMass
  rw [hphysical]
  field_simp [hE, hn]
  ring

end RiemannResearch.RH.Pareto.SquarefreeSampling
