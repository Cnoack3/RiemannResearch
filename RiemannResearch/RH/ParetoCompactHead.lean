import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.MobiusCoefficientStabilization
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Physical Pareto cutoffs

Orthogonal restriction to the actual first N physical sites. This module
contains no arithmetic convergence provider and no RH premise. It extracts
the elementary geometry needed by the signed trial and product criteria.

Source: user-provided Green-Pareto-Schur continuation, Section 18;
this supports the cutoff convention and proof strategy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Exact orthogonal restriction to physical sites 1 through N. -/
def compactHead (N : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  ∑ j ∈ Finset.range N, hilbertGibbsPhysical f j • paretoPointHilbert j

private theorem compactHead_physical_sum (s : Finset ℕ)
    (v : ℕ → ThresholdHilbert) (k : ℕ) :
    hilbertGibbsPhysical (∑ j ∈ s, v j) k =
      ∑ j ∈ s, hilbertGibbsPhysical (v j) k := by
  change hilbertSequenceLinear (∑ j ∈ s, v j) (k+1) =
    ∑ j ∈ s, hilbertSequenceLinear (v j) (k+1)
  rw [map_sum]
  simp only [Finset.sum_apply]

@[simp] theorem compactHead_coordinate (N : ℕ) (f : ThresholdHilbert) (j : ℕ) :
    hilbertGibbsPhysical (compactHead N f) j =
      if j < N then hilbertGibbsPhysical f j else 0 := by
  rw [compactHead, compactHead_physical_sum]
  simp only [hilbertGibbsPhysical_smul, hilbertGibbsPhysical_paretoPoint,
    mul_ite, mul_one, mul_zero]
  simp

theorem compactHead_sequence (N : ℕ) (f : ThresholdHilbert) (j : ℕ) :
    hilbertSequence (compactHead N f) j =
      if j ≤ N then hilbertSequence f j else 0 := by
  cases j with
  | zero => simp
  | succ k =>
    have h := compactHead_coordinate N f k
    rw [hilbertGibbsPhysical_eq, hilbertGibbsPhysical_eq] at h
    simpa only [show k < N ↔ k+1 ≤ N by omega] using h

theorem compactHead_tail_inner_head (N : ℕ) (f g : ThresholdHilbert) :
    inner ℝ (f - compactHead N f) (compactHead N g) = 0 := by
  change inner ℝ (f - compactHead N f)
    (∑ j ∈ Finset.range N, hilbertGibbsPhysical g j • paretoPointHilbert j) = 0
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [inner_smul_right, inner_paretoPoint]
  have ht : hilbertGibbsPhysical (f - compactHead N f) j = 0 := by
    rw [hilbertGibbsPhysical_eq]
    change hilbertSequenceLinear (f - compactHead N f) (j+1) = 0
    rw [map_sub]
    change hilbertSequence f (j+1) - hilbertSequence (compactHead N f) (j+1) = 0
    rw [compactHead_sequence, if_pos (by have := Finset.mem_range.mp hj; omega)]
    exact sub_self _
  rw [ht]
  simp

theorem compactHead_symmetric (N : ℕ) (f g : ThresholdHilbert) :
    inner ℝ (compactHead N f) g = inner ℝ f (compactHead N g) := by
  have hfg := compactHead_tail_inner_head N f g
  have hgf := compactHead_tail_inner_head N g f
  rw [inner_sub_left] at hfg hgf
  rw [← real_inner_comm g (compactHead N f),
    ← real_inner_comm (compactHead N g) (compactHead N f)] at hgf
  linarith

theorem compactHead_pythagoras (N : ℕ) (f : ThresholdHilbert) :
    ‖f‖^2 = ‖compactHead N f‖^2 + ‖f - compactHead N f‖^2 := by
  have h := compactHead_tail_inner_head N f f
  have h' : inner ℝ (compactHead N f) (f - compactHead N f) = 0 := by
    rw [real_inner_comm]
    exact h
  have he : f = compactHead N f + (f - compactHead N f) := by abel
  calc
    ‖f‖^2 = ‖compactHead N f + (f - compactHead N f)‖^2 := by rw [← he]
    _ = _ := by rw [norm_add_sq_real, h']; ring

theorem compactHead_idempotent (N : ℕ) (f : ThresholdHilbert) :
    compactHead N (compactHead N f) = compactHead N f := by
  apply hilbertSequence_injective
  funext j
  by_cases hj : j ≤ N <;> simp [compactHead_sequence, hj]

theorem compactHead_fixed_of_support (N : ℕ) (f : ThresholdHilbert)
    (hf : ∀ j, N < j → hilbertSequence f j = 0) :
    compactHead N f = f := by
  apply hilbertSequence_injective
  funext j
  rw [compactHead_sequence]
  by_cases hj : j ≤ N
  · rw [if_pos hj]
  · rw [if_neg hj, hf j (by omega)]

theorem compactHead_norm_le (N : ℕ) (f : ThresholdHilbert) :
    ‖compactHead N f‖ ≤ ‖f‖ := by
  nlinarith [compactHead_pythagoras N f,
    sq_nonneg ‖f - compactHead N f‖,
    norm_nonneg (compactHead N f), norm_nonneg f]

theorem compactHead_add (N : ℕ) (f g : ThresholdHilbert) :
    compactHead N (f+g) = compactHead N f + compactHead N g := by
  unfold compactHead
  simp only [hilbertGibbsPhysical_add, add_smul]
  rw [Finset.sum_add_distrib]

theorem compactHead_smul (N : ℕ) (c : ℝ) (f : ThresholdHilbert) :
    compactHead N (c • f) = c • compactHead N f := by
  unfold compactHead
  simp only [hilbertGibbsPhysical_smul, mul_smul]
  rw [Finset.smul_sum]

def compactHeadLinear (N : ℕ) : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := compactHead N
  map_add' := compactHead_add N
  map_smul' := compactHead_smul N

theorem compactHead_sub (N : ℕ) (f g : ThresholdHilbert) :
    compactHead N (f-g) = compactHead N f - compactHead N g :=
  (compactHeadLinear N).map_sub f g

theorem compactHead_observation (N : ℕ) (f u : ThresholdHilbert)
    (hu : compactHead N u = u) :
    inner ℝ (compactHead N f) u = inner ℝ f u := by
  rw [compactHead_symmetric, hu]

theorem compactHead_mobiusRiesz (N m : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
    compactHead N (mobiusRieszHilbert m) = mobiusRieszHilbert m := by
  apply compactHead_fixed_of_support
  intro j hj
  rw [mobiusRieszHilbert_sequence m j hm,
    dualCoeff_eq_zero_of_lt hm (by omega)]
  simp

/- Source: user-provided continuation, Section 25, equation (69),
6 October 2026 (endpoint support proof strategy). -/
/-- The actual orthogonal head has just its boundary coordinate when every
strictly earlier residual coordinate vanishes. -/
theorem compactHead_norm_sq_eq_endpoint (N : ℕ) (f : ThresholdHilbert)
    (hhead : ∀ j < N, hilbertSequence f j = 0) :
    ‖compactHead N f‖^2 = positiveWeight N * (hilbertSequence f N)^2 := by
  rw [hilbert_norm_weighted_sq]
  calc
    _ = positiveWeight N * (hilbertSequence (compactHead N f) N)^2 := by
      apply tsum_eq_single N
      intro j hjN
      rw [compactHead_sequence]
      by_cases hj : j ≤ N
      · rw [if_pos hj, hhead j (by omega)]
        simp
      · rw [if_neg hj]
        simp
    _ = _ := by rw [compactHead_sequence, if_pos (le_refl N)]


end RiemannResearch.RH.Pareto
