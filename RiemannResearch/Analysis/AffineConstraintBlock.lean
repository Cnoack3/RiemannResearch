import RiemannResearch.Analysis.MultipleAffineObservationProjection
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact cost of adding a block of affine constraints

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
The screened source is the actual discrepancy of the old optimizer at the
new observations. The new correction preserves every old observation and
pays precisely its full Schur inverse-Gram cost.
-/

noncomputable section
namespace RiemannResearch.Analysis.AffineConstraintBlock
open FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity
open MultipleAffineObservationProjection

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def unmet (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H)
    (f : H) (t : ι → ℝ) (s : κ → ℝ) (j : κ) : ℝ :=
  s j - inner ℝ (w j) (affineCandidate K hu f t)

theorem affineMismatch_sum (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (u : ι → H) (w : κ → H) (f : H) (t : ι → ℝ) (s : κ → ℝ) :
    affineMismatch K (Sum.elim u w) f (Sum.elim t s) =
      Sum.elim (affineMismatch K u f t) (affineMismatch K w f s) := by
  funext i
  cases i <;> rfl

theorem screenedMismatch_eq (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H)
    (f : H) (t : ι → ℝ) (s : κ → ℝ) :
    screenedSource hu w (affineMismatch K u f t) (affineMismatch K w f s) =
      unmet K hu w f t s := by
  funext j
  simp only [screenedSource, affineMismatch, unmet, affineCandidate, inner_add_right]
  ring

/-- Full block correction of the actual affine optimizer. -/
theorem candidate_update (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H)
    (hall : LinearIndependent ℝ (Sum.elim u w)) (f : H) (t : ι → ℝ) (s : κ → ℝ) :
    affineCandidate K hall f (Sum.elim t s) = affineCandidate K hu f t +
      minimumVector (screened_linearIndependent hu w hall) (unmet K hu w f t s) := by
  unfold affineCandidate
  rw [affineMismatch_sum, minimumVector_screened_sum hu w
    (screened_linearIndependent hu w hall) hall, screenedMismatch_eq]
  abel

theorem correction_old_observation_zero (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H)
    (hall : LinearIndependent ℝ (Sum.elim u w)) (f : H) (t : ι → ℝ) (s : κ → ℝ) (i : ι) :
    inner ℝ (u i) (affineCandidate K hall f (Sum.elim t s) - affineCandidate K hu f t) = 0 := by
  rw [candidate_update, add_sub_cancel_left]
  exact inner_old_screened_minimumVector hu w (screened_linearIndependent hu w hall) _ i

/-- Added constraints increase the minimum error by exactly the actual Schur capacity. -/
theorem error_update (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H)
    (hall : LinearIndependent ℝ (Sum.elim u w))
    (huK : ∀ i, u i ∈ K) (hwK : ∀ j, w j ∈ K)
    (f : H) (t : ι → ℝ) (s : κ → ℝ) :
    ‖f - affineCandidate K hall f (Sum.elim t s)‖ ^ 2 =
      ‖f - affineCandidate K hu f t‖ ^ 2 +
        capacity (screened_linearIndependent hu w hall) (unmet K hu w f t s) := by
  have hmem : ∀ i, Sum.elim u w i ∈ K := by
    intro i
    cases i with
    | inl i => exact huK i
    | inr j => exact hwK j
  rw [affineCandidate_energy K hall hmem, affineCandidate_energy K hu huK,
    affineMismatch_sum, capacity_screened_add hu w
      (screened_linearIndependent hu w hall) hall, screenedMismatch_eq]
  ring

theorem error_update_displacement (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H)
    (hall : LinearIndependent ℝ (Sum.elim u w))
    (huK : ∀ i, u i ∈ K) (hwK : ∀ j, w j ∈ K)
    (f : H) (t : ι → ℝ) (s : κ → ℝ) :
    ‖f - affineCandidate K hall f (Sum.elim t s)‖ ^ 2 =
      ‖f - affineCandidate K hu f t‖ ^ 2 +
        ‖affineCandidate K hall f (Sum.elim t s) - affineCandidate K hu f t‖ ^ 2 := by
  rw [error_update K hu w hall huK hwK f t s, candidate_update, add_sub_cancel_left,
    capacity_eq_norm_sq]

/-- No extra cost occurs exactly when every new constraint already holds. -/
theorem error_equal_iff (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H)
    (hall : LinearIndependent ℝ (Sum.elim u w))
    (huK : ∀ i, u i ∈ K) (hwK : ∀ j, w j ∈ K)
    (f : H) (t : ι → ℝ) (s : κ → ℝ) :
    ‖f - affineCandidate K hall f (Sum.elim t s)‖ ^ 2 =
      ‖f - affineCandidate K hu f t‖ ^ 2 ↔
      ∀ j, inner ℝ (w j) (affineCandidate K hu f t) = s j := by
  constructor
  · intro he
    have hc := error_update K hu w hall huK hwK f t s
    have hz : capacity (screened_linearIndependent hu w hall) (unmet K hu w f t s) = 0 := by linarith
    have hb : unmet K hu w f t s = 0 := by
      by_contra hne
      have hp := capacity_pos (screened_linearIndependent hu w hall) _ hne
      linarith
    intro j
    have hj := congrFun hb j
    change s j - inner ℝ (w j) (affineCandidate K hu f t) = 0 at hj
    exact (sub_eq_zero.mp hj).symm
  · intro h
    have hb : unmet K hu w f t s = 0 := by
      funext j
      simp only [unmet, h, sub_self, Pi.zero_apply]
    rw [error_update K hu w hall huK hwK f t s, hb]
    simp [capacity, inverseSource]

end RiemannResearch.Analysis.AffineConstraintBlock
