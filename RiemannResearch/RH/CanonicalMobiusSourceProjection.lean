/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CanonicalMobiusSingleHeadCapacity
import RiemannResearch.RH.CanonicalMobiusWindowGainBounds

/-!
# The first-head arithmetic source as a projection residual

Source: the existing single-observation minimum in
CanonicalMobiusSingleHeadCapacity and the signed gain identity in
CanonicalMobiusWindowGainBounds, combined in the directed continuation of
24 September 2026. The optimizer is identified as an actual vector, not only
by equality of minimum energies. This is standard projection algebra; no
novelty claim is made.

For first-head error E_M and capacity normal Q_M, the exact identity is
E_M Q_M = tail(P_M e_1) = -tail(e_1 - P_M e_1). It identifies the signed
source with the actual residual innovation, while supplying no proof that
the limiting residual vanishes. All complete tails are retained.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.SingleObservationProjection

/-- The exact arithmetic optimizer is the normalized projection as an actual vector. -/
theorem singleHead_optimizer_eq_projection (M : ℕ) (hM : 1 ≤ M) :
    optimizedAverage 1 (canonicalWindowIndex 1 M) (canonicalWindowIndex_pos 1 M (by omega)) =
      observationOptimizer (finiteSpace M) (finiteHeadIndicator 1) (1 / 2 : ℝ) := by
  have hu : canonicalMobiusHilbert 1 ∈ finiteSpace M :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hM
      (canonicalMobiusHilbert_mem_finiteSpace 1)
  have hq := singleHeadProjection_norm_sq_pos (finiteSpace M) hu
  have hx := canonicalWindow_combination_mem_finiteSpace 1 M hM
    (affineCoefficients (normal 1 (canonicalWindowIndex 1 M)
      (canonicalWindowIndex_pos 1 M (by omega))))
  have ho : inner ℝ (finiteHeadIndicator 1)
      (optimizedAverage 1 (canonicalWindowIndex 1 M)
        (canonicalWindowIndex_pos 1 M (by omega))) = (1 / 2 : ℝ) := by
    rw [real_inner_comm, inner_singleHeadIndicator,
      optimizedAverage_exact 1 _ _ (canonicalWindowIndex_ge 1 M) 1 (by omega) le_rfl]
    ring
  apply (observationOptimizer_unique (finiteSpace M) (finiteHeadIndicator 1) _
    (1 / 2 : ℝ) (ne_of_gt hq) hx ho).mp
  have he := singleHead_full_minimum M hM
  change ‖optimizedAverage 1 (canonicalWindowIndex 1 M)
    (canonicalWindowIndex_pos 1 M (by omega))‖ ^ 2 = _
  rw [optimizedAverage_norm_sq _ _ _ (canonicalWindowIndex_ge 1 M)]
  norm_num only [Nat.cast_one, one_add_one_eq_two]
  convert he using 1
  norm_num [windowCapacity]

theorem optimizedAverage_tail_eq_inv_capacity_normal
    (N M : ℕ) (hN : 0 < N) :
    hilbertTailShift (optimizedAverage N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN)) N =
      (windowCapacity N M hN)⁻¹ • windowNormal N M hN := by
  rw [optimizedAverage, combination_tail]
  change Fintype.linearCombination ℝ (tailFamily N (canonicalWindowIndex N M))
      ((windowCapacity N M hN)⁻¹ • normal N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN)) = _
  rw [map_smul]
  rfl

/-- The canonical capacity normal is the tail of the finite projection,
scaled by its actual first-coordinate projection error. -/
theorem singleHeadError_smul_windowNormal_eq_projection_tail
    (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError M • windowNormal 1 M (by omega) =
      hilbertTailShift ((finiteSpace M).starProjection (finiteHeadIndicator 1)) 1 := by
  let K : ℝ := windowCapacity 1 M (by omega)
  let q : ℝ := ‖(finiteSpace M).starProjection (finiteHeadIndicator 1)‖ ^ 2
  let E : ℝ := singleHeadError M
  have hu : canonicalMobiusHilbert 1 ∈ finiteSpace M :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hM
      (canonicalMobiusHilbert_mem_finiteSpace 1)
  have hq : 0 < q := singleHeadProjection_norm_sq_pos (finiteSpace M) hu
  have hK : 0 < K := capacity_pos _ _ _
  have hE : E = (K + 2)⁻¹ := singleHeadError_eq_inv_capacity_add_two M hM
  have hEq : E = 1 / 2 - q := by
    dsimp [E, q, singleHeadError]
    rw [projection_defect_energy, finiteHeadIndicator_norm_sq]
    norm_num
  have hEK : E * K = 2 * q := by
    have hEn : E * (K + 2) = 1 := by rw [hE]; exact inv_mul_cancel₀ (by positivity)
    nlinarith
  have ht := optimizedAverage_tail_eq_inv_capacity_normal 1 M (by omega)
  rw [singleHead_optimizer_eq_projection M hM, observationOptimizer] at ht
  have ht' : ((1 / 2 : ℝ) / q) •
      hilbertTailShift ((finiteSpace M).starProjection (finiteHeadIndicator 1)) 1 =
      K⁻¹ • windowNormal 1 M (by omega) := by
    change (hilbertTailShiftLinear 1) _ = _ at ht
    rw [map_smul] at ht
    exact ht
  have hscale : E * K * ((1 / 2 : ℝ) / q) = 1 := by
    rw [hEK]
    field_simp [ne_of_gt hq]
  have hs := congrArg (fun x : ThresholdHilbert => (E * K) • x) ht'
  rw [smul_smul, smul_smul, hscale, one_smul] at hs
  have hcancel : E * K * K⁻¹ = E := by field_simp [ne_of_gt hK]
  rw [hcancel] at hs
  exact hs.symm

theorem singleHeadError_smul_windowNormal_eq_neg_residual_tail
    (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError M • windowNormal 1 M (by omega) =
      -hilbertTailShift
        (finiteHeadIndicator 1 - (finiteSpace M).starProjection (finiteHeadIndicator 1)) 1 := by
  rw [singleHeadError_smul_windowNormal_eq_projection_tail M hM]
  have ht := (hilbertTailShiftLinear 1).map_sub (finiteHeadIndicator 1)
    ((finiteSpace M).starProjection (finiteHeadIndicator 1))
  change hilbertTailShift (_ - _) 1 =
    hilbertTailShift (finiteHeadIndicator 1) 1 -
    hilbertTailShift ((finiteSpace M).starProjection (finiteHeadIndicator 1)) 1 at ht
  rw [ht, finiteHeadIndicator_tail_zero, zero_sub, neg_neg]

/-- Exact identification of the moving signed gain source with the finite
first-coordinate projection residual. No limiting cancellation is asserted. -/
theorem singleHead_normalized_source_eq_residual_pairing
    (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError M * inner ℝ (windowStepTail 1 M) (windowNormal 1 M (by omega)) =
      -inner ℝ (windowStepTail 1 M)
        (hilbertTailShift
          (finiteHeadIndicator 1 - (finiteSpace M).starProjection (finiteHeadIndicator 1)) 1) := by
  rw [← inner_smul_right, singleHeadError_smul_windowNormal_eq_neg_residual_tail M hM,
    inner_neg_right]


end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
