/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ScreeningSourceMass
import RiemannResearch.RH.CanonicalMobiusFullEnergy

/-!
# The actual signed source as the next residue prediction error

Source: direct projection algebra extending the source identity in
CanonicalMobiusSourceProjection, following the user-provided power-damping
handoff of 24 September 2026. The exact old-atom moment is retained as 1/2.
The final RH implication assumes nonsummability of the actual normalized
prediction errors; no lower accumulation estimate is claimed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open ArithmeticCumulative

/-- The actual signed source is the next adjacent-residue moment of the actual
finite first-head projection. No accumulation estimate is assumed. -/
theorem firstHeadSignedSource_eq_projection_pairing (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError M * firstHeadSignedSource M =
      inner ℝ (consecutiveResidueHilbert M)
        ((finiteSpace M).starProjection (finiteHeadIndicator 1)) := by
  let v := consecutiveResidueHilbert M
  let p := (finiteSpace M).starProjection (finiteHeadIndicator 1)
  have hvseq : hilbertSequence v 1 = 0 :=
    consecutiveResidueHilbert_head_zero M 1 hM
  have hvhead : ∀ n < 1, v n = 0 := by
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    have hw : Real.sqrt (paretoWeight 0) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      unfold paretoWeight
      positivity
    change v 0 / Real.sqrt (paretoWeight 0) = 0 at hvseq
    exact (div_eq_zero_iff.mp hvseq).resolve_right hw
  change singleHeadError M *
    inner ℝ (hilbertTailShift v 1) (windowNormal 1 M (by omega)) = inner ℝ v p
  rw [← inner_smul_right, singleHeadError_smul_windowNormal_eq_projection_tail M hM]
  change inner ℝ (hilbertTailShift v 1) (hilbertTailShift p 1) = inner ℝ v p
  calc
    _ = inner ℝ (hilbertTailShift p 1) (hilbertTailShift v 1) := real_inner_comm _ _
    _ = inner ℝ p v := hilbertTailShift_inner p v 1 hvhead
    _ = inner ℝ v p := real_inner_comm _ _

/-- Exact next-atom prediction error. The previous atom belongs to the actual
finite legal space, so its projected first-head moment is exactly 1/2. -/
theorem firstHeadSignedSource_eq_next_atom_prediction (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError M * firstHeadSignedSource M =
      ((M + 2 : ℕ) : ℝ) *
        inner ℝ (normalizedResidueHilbert (M + 2) (by omega))
          ((finiteSpace M).starProjection (finiteHeadIndicator 1)) - 1 / 2 := by
  let p := (finiteSpace M).starProjection (finiteHeadIndicator 1)
  let a := normalizedResidueHilbert (M + 1) (by omega)
  have ha : a ∈ finiteSpace M :=
    normalizedResidueHilbert_mem_finiteSpace M (M + 1) (by omega) le_rfl
  have ho := ((finiteSpace M).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal (finiteHeadIndicator 1)) a ha
  have hpa : inner ℝ a p = inner ℝ a (finiteHeadIndicator 1) := by
    change inner ℝ a (finiteHeadIndicator 1 - p) = 0 at ho
    rw [inner_sub_right] at ho
    linarith
  have hprev : ((M + 1 : ℕ) : ℝ) * inner ℝ a p = 1 / 2 := by
    rw [hpa, inner_singleHeadIndicator]
    change ((M + 1 : ℕ) : ℝ) *
      ((1 / 2 : ℝ) * hilbertSequence (normalizedResidueHilbert (M + 1) _) 1) = _
    rw [normalizedResidueHilbert_sequence]
    simp only [residueFraction, Nat.mod_eq_of_lt (by omega : 1 < M + 1), Nat.cast_one]
    have hne : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [firstHeadSignedSource_eq_projection_pairing M hM,
    consecutiveResidueHilbert, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  change ((M + 2 : ℕ) : ℝ) * inner ℝ _ p -
    ((M + 1 : ℕ) : ℝ) * inner ℝ a p = _
  rw [hprev]

/-- The arithmetic prediction error before normalization by the actual defect. -/
def firstHeadPredictionError (M : ℕ) : ℝ :=
  ((M + 2 : ℕ) : ℝ) *
    inner ℝ (normalizedResidueHilbert (M + 2) (by omega))
      ((finiteSpace M).starProjection (finiteHeadIndicator 1)) - 1 / 2

theorem firstHeadPredictionError_eq_mul_source (M : ℕ) (hM : 1 ≤ M) :
    firstHeadPredictionError M = singleHeadError M * firstHeadSignedSource M :=
  (firstHeadSignedSource_eq_next_atom_prediction M hM).symm

theorem firstHeadPredictionError_div_error (M : ℕ) (hM : 1 ≤ M) :
    firstHeadPredictionError M / singleHeadError M = firstHeadSignedSource M := by
  rw [firstHeadPredictionError_eq_mul_source M hM]
  field_simp [ne_of_gt (singleHeadError_pos M hM)]

/-- Conditional research reduction. Nonsummability for these actual
projection prediction errors remains an open arithmetic obligation. -/
theorem riemannHypothesis_of_firstHead_prediction_not_summable
    (h : ¬ Summable (fun j : ℕ =>
      (firstHeadPredictionError (1 + j) / singleHeadError (1 + j)) ^ 2 /
        (harmonic (1 + j + 1) : ℝ))) : RiemannHypothesis := by
  apply riemannHypothesis_of_firstHead_harmonic_source_not_summable
  intro hs
  apply h
  exact hs.congr (fun j => by
    rw [firstHeadPredictionError_div_error (1 + j) (by omega)])

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
