/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RandomSubspaceProjection
import RiemannResearch.Analysis.FiniteAtomSelection
import RiemannResearch.Probability.FiniteDeterminantalLaw

/-!
# Exact atom-selection errors for a finite DPP

Source: user-provided conductor-sampling question, 14 October 2026.
The existing finiteLaw constructs the actual PMF for every positive contraction.
Here its sites index dictionary atoms, rather than coordinates of a Hilbert
basis. No identification with any wavelet-label DPP is used or asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Probability.DPP
open RiemannResearch.Analysis
open RandomSubspaceProjection FiniteAtomSelection

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι] [DecidableEq ι]
variable (v : ι → H) (V : Submodule ℝ H) [V.HasOrthogonalProjection]
variable (hv : ∀ i, v i ∈ V) (K : Matrix ι ι ℝ)
  (hK : K.PosSemidef) (hI : (1 - K).PosSemidef)

include hv in
theorem finiteLaw_expected_atom_error (x : H) :
    expectedError (selectedSpan v)
      (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) x =
      ‖x - V.starProjection x‖ ^ 2 +
        expectedGap V (selectedSpan v)
          (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) x := by
  apply expected_error_eq
  · simpa only [finiteLaw_apply_toReal] using sum_exactWeight K
  · intro J
    exact selectedSpan_le v J V (fun i _ => hv i)

include hv in
theorem finiteLaw_expected_atom_error_eq_iff (x : H) :
    expectedError (selectedSpan v)
      (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) x =
      ‖x - V.starProjection x‖ ^ 2 ↔
      ∀ J, 0 < exactWeight K J → V.starProjection x ∈ selectedSpan v J := by
  have hp : ∀ J, 0 ≤ ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hsum : ∑ J, ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal = 1 := by
    simpa only [finiteLaw_apply_toReal] using sum_exactWeight K
  simpa only [finiteLaw_apply_toReal] using
    expected_error_eq_iff V (selectedSpan v) _ hp hsum
      (fun J => selectedSpan_le v J V (fun i _ => hv i)) x

/-- An actual configuration in the DPP support attains at most the mean error. -/
theorem finiteLaw_exists_good_atom_selection (x : H) :
    ∃ J, 0 < exactWeight K J ∧
      ‖x - (selectedSpan v J).starProjection x‖ ^ 2 ≤
        expectedError (selectedSpan v)
          (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) x := by
  have hp : ∀ J, 0 ≤ ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hsum : ∑ J, ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal = 1 := by
    simpa only [finiteLaw_apply_toReal] using sum_exactWeight K
  simpa only [finiteLaw_apply_toReal] using
    exists_error_le_expected (selectedSpan v) _ hp hsum x

/-- Fixed-size (or size-capped) support gives a deterministic sparse witness. -/
theorem finiteLaw_exists_sparse_atom_selection (x : H) (k : ℕ)
    (hk : ∀ J, 0 < exactWeight K J → J.card ≤ k) :
    ∃ J, J.card ≤ k ∧ 0 < exactWeight K J ∧
      ‖x - (selectedSpan v J).starProjection x‖ ^ 2 ≤
        expectedError (selectedSpan v)
          (fun J => ((finiteLaw K (exactWeight_nonneg K hK hI)) J).toReal) x := by
  obtain ⟨J, hJ, herror⟩ := finiteLaw_exists_good_atom_selection v K hK hI x
  exact ⟨J, hk J hJ, hJ, herror⟩

end RiemannResearch.Probability.DPP
