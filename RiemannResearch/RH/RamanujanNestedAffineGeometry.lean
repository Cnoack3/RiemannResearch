import RiemannResearch.RH.RamanujanMultipleAffineLimits
import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.RH.RamanujanCoordinateCapacityLimits
import RiemannResearch.Analysis.NestedAffineObservationProjection
import RiemannResearch.Analysis.FiniteGramContinuity
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Nested multiple-coordinate Ramanujan optimizers and inverse capacities

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
For fixed original coefficient constraints, enlarging the actual packet
dictionary decreases the attained constrained error by exactly the squared
optimizer displacement. The finite-to-closed error gap is equally exact.
Every direction of the full inverse source Gram decreases, with equality
precisely when the associated minimum-norm representer is unchanged.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanNestedAffineGeometry
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RamanujanCoefficientConstraints RamanujanMultipleCapacityLimits RamanujanMultipleAffineLimits
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteGramContinuity
open RiemannResearch.Analysis.MultipleAffineObservationProjection
open RiemannResearch.Analysis.NestedAffineObservationProjection
open RiemannResearch.Analysis.ExhaustiveWalk

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem finiteRows_pairing (n : ℕ) (e : κ ↪ ℕ) (j : κ)
    (x : ThresholdHilbert) (hx : x ∈ finiteSpace n) :
    inner ℝ (finiteRows n e j) x = coefficientCLM (e j + 2) x :=
  (restrictedRows_pairing (finiteSpace n) (fun j => coordinateRiesz (e j + 2)) j x hx).trans
    (coordinateRiesz_inner (e j + 2) x)

theorem finiteMismatch_eq (n : ℕ) (e : κ ↪ ℕ) (t : κ → ℝ) :
    affineMismatch (finiteSpace n) (finiteRows n e) hilbertOne t = finiteDefect n e t := by
  funext j
  change t j - inner ℝ (finiteRows n e j) (projection n) =
    t j - packetMultipleCoefficient n (e j + 2)
  have hx : projection n ∈ finiteSpace n := by
    change (finiteSpace n).starProjection hilbertOne ∈ finiteSpace n
    exact (finiteSpace n).starProjection_apply_mem hilbertOne
  have hp := finiteRows_pairing n e j (projection n) hx
  rw [hp, packetMultipleCoefficient_eq n (e j + 2) (by omega)]
  rfl

theorem affineFiniteCandidate_eq_affine (n : ℕ) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (t : κ → ℝ) :
    affineFiniteCandidate n e t =
      affineCandidate (finiteSpace n) (finiteRows_independent n e hn) hilbertOne t := by
  rw [affineFiniteCandidate, matrixMinimum_eq_minimumVector (finiteRows_independent n e hn),
    affineCandidate, finiteMismatch_eq, packetCandidate_eq_projection]
  rfl

theorem affineFiniteCandidate_mem (n : ℕ) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (t : κ → ℝ) : affineFiniteCandidate n e t ∈ finiteSpace n := by
  rw [affineFiniteCandidate_eq_affine n e hn t]
  exact affineCandidate_mem (finiteSpace n) (finiteRows_independent n e hn)
    (fun j => (finiteSpace n).starProjection_apply_mem (coordinateRiesz (e j + 2))) hilbertOne t

theorem affineFiniteCandidate_coordinates (n : ℕ) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (t : κ → ℝ) (j : κ) :
    coefficientCLM (e j + 2) (affineFiniteCandidate n e t) = t j := by
  rw [affineFiniteCandidate_eq_stage n e hn t]
  exact RamanujanMultipleConstraints.candidate_coordinates n (stageEmbedding n e hn) t j

/-- Enlarging a packet stage under fixed simultaneous constraints retains
the complete squared displacement as the exact improvement. -/
theorem affine_stage_error_exact (n k : ℕ) (hnk : n ≤ k) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (t : κ → ℝ) :
    ‖hilbertOne - affineFiniteCandidate n e t‖ ^ 2 =
      ‖hilbertOne - affineFiniteCandidate k e t‖ ^ 2 +
        ‖affineFiniteCandidate n e t - affineFiniteCandidate k e t‖ ^ 2 := by
  have hk : ∀ j, e j < k := fun j => lt_of_lt_of_le (hn j) hnk
  rw [affineFiniteCandidate_eq_affine n e hn t, affineFiniteCandidate_eq_affine k e hk t]
  exact nested_affine_error_exact (finiteSpace n) (finiteSpace k)
    (walkSpan_mono residueAtom id hnk) (fun j => coordinateRiesz (e j + 2))
    (finiteRows_independent n e hn) (finiteRows_independent k e hk) hilbertOne t

theorem affine_stage_error_le (n k : ℕ) (hnk : n ≤ k) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (t : κ → ℝ) :
    ‖hilbertOne - affineFiniteCandidate k e t‖ ^ 2 ≤
      ‖hilbertOne - affineFiniteCandidate n e t‖ ^ 2 := by
  rw [affine_stage_error_exact n k hnk e hn t]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem affine_stage_error_equal_iff (n k : ℕ) (hnk : n ≤ k) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (t : κ → ℝ) :
    ‖hilbertOne - affineFiniteCandidate n e t‖ ^ 2 =
      ‖hilbertOne - affineFiniteCandidate k e t‖ ^ 2 ↔
      affineFiniteCandidate n e t = affineFiniteCandidate k e t := by
  constructor
  · intro he
    have h := affine_stage_error_exact n k hnk e hn t
    have hz : ‖affineFiniteCandidate n e t - affineFiniteCandidate k e t‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro he
    rw [he]

/-- The exact distance to the full closed affine optimizer is its entire
finite-stage excess error, including the unresolved canonical residual. -/
theorem affine_limit_error_exact (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) (t : κ → ℝ) :
    ‖hilbertOne - affineFiniteCandidate n e t‖ ^ 2 = limitEnergy + limitCost e t +
      ‖affineFiniteCandidate n e t - affineLimitCandidate e t‖ ^ 2 := by
  exact affineLimitCandidate_completion e t (affineFiniteCandidate n e t)
    (finiteSpace_le_closedSpace n (affineFiniteCandidate_mem n e hn t))
    (affineFiniteCandidate_coordinates n e hn t)

/-- Every source direction of the actual inverse coordinate Gram. -/
def inverseCapacity (n : ℕ) (e : κ ↪ ℕ) (b : κ → ℝ) : ℝ :=
  ∑ i, ((finiteGram n e)⁻¹.mulVec b) i * b i

theorem inverseCapacity_eq (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) (b : κ → ℝ) :
    inverseCapacity n e b = capacity (finiteRows_independent n e hn) b := by
  rw [inverseCapacity, finiteGram, gramMatrix_inverseSource (finiteRows_independent n e hn)]
  rfl

theorem inverseCapacity_stage_exact (n k : ℕ) (hnk : n ≤ k) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (b : κ → ℝ) :
    inverseCapacity n e b = inverseCapacity k e b +
      ‖matrixMinimum (finiteRows n e) b - matrixMinimum (finiteRows k e) b‖ ^ 2 := by
  have hk : ∀ j, e j < k := fun j => lt_of_lt_of_le (hn j) hnk
  rw [inverseCapacity_eq n e hn b, inverseCapacity_eq k e hk b,
    matrixMinimum_eq_minimumVector (finiteRows_independent n e hn),
    matrixMinimum_eq_minimumVector (finiteRows_independent k e hk)]
  exact nested_capacity_exact (finiteSpace n) (finiteSpace k)
    (walkSpan_mono residueAtom id hnk) (fun j => coordinateRiesz (e j + 2))
    (finiteRows_independent n e hn) (finiteRows_independent k e hk) b

theorem inverseCapacity_limit_exact (n : ℕ) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (b : κ → ℝ) :
    inverseCapacity n e b = capacity (limitRows_independent e) b +
      ‖matrixMinimum (finiteRows n e) b - minimumVector (limitRows_independent e) b‖ ^ 2 := by
  rw [inverseCapacity_eq n e hn b,
    matrixMinimum_eq_minimumVector (finiteRows_independent n e hn)]
  exact nested_capacity_exact (finiteSpace n) closedSpace (finiteSpace_le_closedSpace n)
    (fun j => coordinateRiesz (e j + 2)) (finiteRows_independent n e hn)
    (limitRows_independent e) b

theorem inverseCapacity_stage_le (n k : ℕ) (hnk : n ≤ k) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (b : κ → ℝ) : inverseCapacity k e b ≤ inverseCapacity n e b := by
  rw [inverseCapacity_stage_exact n k hnk e hn b]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem inverseCapacity_limit_equal_iff (n : ℕ) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (b : κ → ℝ) :
    inverseCapacity n e b = capacity (limitRows_independent e) b ↔
      matrixMinimum (finiteRows n e) b = minimumVector (limitRows_independent e) b := by
  constructor
  · intro he
    have h := inverseCapacity_limit_exact n e hn b
    have hz : ‖matrixMinimum (finiteRows n e) b - minimumVector (limitRows_independent e) b‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro he
    rw [inverseCapacity_limit_exact n e hn b, he, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

end RiemannResearch.RH.RamanujanNestedAffineGeometry
