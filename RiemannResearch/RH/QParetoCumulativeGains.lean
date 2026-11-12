/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoPrimorialForcing
import RiemannResearch.Analysis.ProjectionTrialEnergy
import RiemannResearch.RH.QPrimorialResidualCertificate
import Mathlib.Topology.Algebra.InfiniteSum.Real
import RiemannResearch.LinearAlgebra.ConditionalSchurDecomposition

/-!
# Exact cumulative gains on the changing primorial tower

Source: Pareto-first research agenda, Priority 4, 11 November 2026.
The nested full spaces, rather than a fixed prime/carry basis, define the
gains. Their entire series is computed unconditionally. Exhausting the
initial error is equivalent to zero limiting residual and remains Open.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.NestedProjectionGains
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem energy_drop (S T : Submodule ℝ E)
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (hST : S ≤ T) (x : E) :
    ‖x - S.starProjection x‖ ^ 2 - ‖x - T.starProjection x‖ ^ 2 =
      ‖T.starProjection x - S.starProjection x‖ ^ 2 := by
  have h := projection_trial_energy T x (S.starProjection x)
    (hST (S.starProjection_apply_mem x))
  linarith

/-- Any full normal block computes the same geometric gain, regardless of its coordinates. -/
theorem normal_block_gain {ι : Type*} [Fintype ι]
    (S T : Submodule ℝ E) [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    (hST : S ≤ T) (x : E) (z : ι → E) (c : ι → ℝ)
    (hfit : T.starProjection x - S.starProjection x = Fintype.linearCombination ℝ z c)
    (hnormal : ∀ i, inner ℝ (z i) (Fintype.linearCombination ℝ z c) =
      inner ℝ (z i) (x - S.starProjection x)) :
    ‖x - S.starProjection x‖ ^ 2 - ‖x - T.starProjection x‖ ^ 2 =
      ∑ i, c i * inner ℝ (z i) (x - S.starProjection x) := by
  rw [energy_drop S T hST x, hfit, FiniteHilbertGram.gram_quadratic]
  apply Finset.sum_congr rfl
  intro i _
  change c i * inner ℝ (z i) (Fintype.linearCombination ℝ z c) = _
  rw [hnormal i]


/-- The actual optimized block gain uses the complete residualized Schur matrix and source. -/
theorem augmented_schur_gain {ι : Type*} [Fintype ι]
    (S : Submodule ℝ E) [S.HasOrthogonalProjection] (z : ι → E)
    [(S ⊔ Submodule.span ℝ (Set.range z)).HasOrthogonalProjection]
    (x : E) (G : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (hG : ∀ c i, G c i = ∑ j,
      (inner ℝ (z i) (z j) - inner ℝ (S.starProjection (z i)) (S.starProjection (z j))) * c j) :
    ‖x - S.starProjection x‖ ^ 2 -
      ‖x - (S ⊔ Submodule.span ℝ (Set.range z)).starProjection x‖ ^ 2 =
      ∑ i, G.symm (fun j =>
        inner ℝ (z j) x - inner ℝ (S.starProjection (z j)) (S.starProjection x)) i *
        (inner ℝ (z i) x - inner ℝ (S.starProjection (z i)) (S.starProjection x)) := by
  let y := RiemannResearch.LinearAlgebra.ConditionalSchur.packetResidual S ∘ z
  let r := RiemannResearch.LinearAlgebra.ConditionalSchur.packetResidual S x
  have hG' (c : ι → ℝ) (i : ι) : G c i = ∑ j, inner ℝ (y i) (y j) * c j := by
    simpa only [y, Function.comp_apply,
      RiemannResearch.LinearAlgebra.ConditionalSchur.packetResidual,
      RiemannResearch.LinearAlgebra.inner_residualized_eq_schur] using hG c i
  have hn := RiemannResearch.LinearAlgebra.finiteSchur_inverse_normal r y G hG'
  have ha := RiemannResearch.LinearAlgebra.ConditionalSchur.augmented_projection_residual
    S z x (G.symm (fun i => inner ℝ (y i) r)) hn
  have h := RiemannResearch.LinearAlgebra.finiteSchurResidual_inverse_gain r y G hG'
  rw [ha] at h
  simpa only [y, r, Function.comp_apply,
    RiemannResearch.LinearAlgebra.ConditionalSchur.packetResidual,
    RiemannResearch.LinearAlgebra.inner_residualized_eq_schur] using h

end RiemannResearch.Analysis.NestedProjectionGains

namespace RiemannResearch.RH.QParetoCumulativeGains
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer
open QPrimorialMatchedDisplacement QSquarefreePrimorialCofinality
open QSquarefreeDisplacementRigidity QParetoPrimorialForcing
open RiemannResearch.Analysis.NestedProjectionGains

def gain (n : ℕ) : ℝ :=
  ‖(paretoStage (n + 1)).starProjection hilbertOne -
    (paretoStage n).starProjection hilbertOne‖ ^ 2

theorem gain_nonneg (n : ℕ) : 0 ≤ gain n := sq_nonneg _

theorem pError_eq (n : ℕ) :
    pError n = ‖hilbertOne - (paretoStage n).starProjection hilbertOne‖ ^ 2 := by
  rw [← QParetoPrimorialForcing.residual, residual_eq_physical]
  rfl

theorem gain_eq_drop (n : ℕ) : gain n = pError n - pError (n + 1) := by
  rw [pError_eq, pError_eq]
  exact (energy_drop _ _ (Submodule.map_mono (primorialStage_mono (by omega)))
    hilbertOne).symm

/-- Exact finite telescoping includes every change in the prime and carry spaces. -/
theorem finite_gain_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, gain n) = pError 0 - pError N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, gain_eq_drop]
    ring

theorem gains_summable : Summable gain := by
  apply summable_of_sum_range_le (c := pError 0) gain_nonneg
  intro N
  rw [finite_gain_sum]
  exact sub_le_self _ (sq_nonneg _)

/-- Unconditional exact total gain, with the unexhausted limiting energy retained. -/
theorem total_gain :
    (∑' n, gain n) = pError 0 - ‖toPareto pResidual‖ ^ 2 := by
  have h : Tendsto (fun N => ∑ n ∈ Finset.range N, gain n) atTop
      (𝓝 (pError 0 - ‖toPareto pResidual‖ ^ 2)) := by
    simp only [finite_gain_sum]
    exact tendsto_const_nhds.sub pError_tendsto
  exact tendsto_nhds_unique gains_summable.tendsto_sum_tsum_nat h

/-- This is an equivalence, not a proof of the exhaustion premise. -/
theorem exhaustion_iff_zero_residual :
    (∑' n, gain n) = pError 0 ↔ pResidual = 0 := by
  rw [total_gain]
  constructor
  · intro h
    have hz : ‖toPareto pResidual‖ ^ 2 = 0 := by linarith
    have hz' : toPareto pResidual = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    apply QParetoEquivalence.paretoEquiv.injective
    simpa only [map_zero, QParetoEquivalence.paretoEquiv_apply] using hz'
  · intro h
    have hz : toPareto (0 : QHilbert) = 0 := toParetoLinear.map_zero
    simp only [h, hz, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]

open QPrimorialMatchedGram
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteProjectionForcingCertificate

theorem pError_projection_energy (n : ℕ) :
    pError n = 1 - ‖(paretoStage n).starProjection hilbertOne‖ ^ 2 := by
  have h := RiemannResearch.Analysis.projection_trial_energy
    (paretoStage n) hilbertOne 0 ((paretoStage n).zero_mem)
  rw [sub_zero, sub_zero, hilbertOne_norm_sq, ← pError_eq] at h
  linarith

/-- Full inverse-Gram gain, independent of any moving prime/carry coordinates. -/
theorem gain_inverseGram (n : ℕ) :
    gain n =
      dotProduct (cross (paretoDivisorAtom (n + 1)) hilbertOne)
        ((gramMatrix (paretoDivisorAtom (n + 1)))⁻¹.mulVec
          (cross (paretoDivisorAtom (n + 1)) hilbertOne)) -
      dotProduct (cross (paretoDivisorAtom n) hilbertOne)
        ((gramMatrix (paretoDivisorAtom n))⁻¹.mulVec
          (cross (paretoDivisorAtom n) hilbertOne)) := by
  have hn := projection_energy_inverseGram (paretoDivisorAtom_independent n) hilbertOne
  have hs := projection_energy_inverseGram (paretoDivisorAtom_independent (n + 1)) hilbertOne
  simp only [synthesisSpan_eq] at hn hs
  rw [gain_eq_drop, pError_projection_energy, pError_projection_energy, hn, hs]
  ring

/-- Certified gains accumulate before any assertion about exhaustion. -/
theorem finite_gain_lower_bound (L : ℕ → ℝ) (hL : ∀ n, L n ≤ gain n) (N : ℕ) :
    (∑ n ∈ Finset.range N, L n) ≤ pError 0 - pError N := by
  rw [← finite_gain_sum]
  exact Finset.sum_le_sum fun n _ => hL n

theorem limiting_residual_bound (L : ℕ → ℝ) (hL : ∀ n, L n ≤ gain n) (N : ℕ) :
    ‖toPareto pResidual‖ ^ 2 ≤ pError 0 - ∑ n ∈ Finset.range N, L n := by
  have h := finite_gain_lower_bound L hL N
  have hr := QPrimorialResidualCertificate.limiting_pError_le N
  linarith


end RiemannResearch.RH.QParetoCumulativeGains
