import RiemannResearch.RH.RamanujanMultipleAffineLimits
import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.Analysis.AffineConstraintBlock
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import RiemannResearch.Analysis.FiniteHilbertGramMatrix

/-!
# Exact block extension of Ramanujan affine coefficient constraints

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
New original coefficients are prescribed simultaneously after screening
their full limiting Riesz rows against all old rows. The Schur Gram is
automatically positive definite. Every old coefficient is preserved, and
the added error is exactly the complete inverse-Schur cost of the still
unmet new requests. This is a constraint enlargement, not a replacement
of the original packet dictionary.
-/

noncomputable section
namespace RiemannResearch.RH.RamanujanConstraintBlocks
open Pareto Pareto.CoefficientStabilization RamanujanCoefficientConstraints
open RamanujanMultipleCapacityLimits RamanujanMultipleAffineLimits
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.MultipleAffineObservationProjection
open RiemannResearch.Analysis.AffineConstraintBlock

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def oldEmbedding (e : (ι ⊕ κ) ↪ ℕ) : ι ↪ ℕ where
  toFun i := e (Sum.inl i)
  inj' := by intro i j h; exact Sum.inl.inj (e.injective h)

def newEmbedding (e : (ι ⊕ κ) ↪ ℕ) : κ ↪ ℕ where
  toFun j := e (Sum.inr j)
  inj' := by intro i j h; exact Sum.inr.inj (e.injective h)

theorem joinedRows_eq (e : (ι ⊕ κ) ↪ ℕ) :
    Sum.elim (limitRows (oldEmbedding e)) (limitRows (newEmbedding e)) = limitRows e := by
  funext j
  cases j <;> rfl

theorem joined_independent (e : (ι ⊕ κ) ↪ ℕ) :
    LinearIndependent ℝ (Sum.elim (limitRows (oldEmbedding e)) (limitRows (newEmbedding e))) := by
  rw [joinedRows_eq]
  exact limitRows_independent e

def screenedRows (e : (ι ⊕ κ) ↪ ℕ) : κ → ThresholdHilbert :=
  screened (limitRows_independent (oldEmbedding e)) (limitRows (newEmbedding e))

theorem screenedRows_independent (e : (ι ⊕ κ) ↪ ℕ) : LinearIndependent ℝ (screenedRows e) :=
  screened_linearIndependent (limitRows_independent (oldEmbedding e))
    (limitRows (newEmbedding e)) (joined_independent e)

theorem screenedRows_det_pos (e : (ι ⊕ κ) ↪ ℕ) :
    0 < (gramMatrix (screenedRows e)).det := gramMatrix_det_pos (screenedRows_independent e)

def newDefect (e : (ι ⊕ κ) ↪ ℕ) (t : ι → ℝ) (s : κ → ℝ) (j : κ) : ℝ :=
  s j - coefficientCLM (e (Sum.inr j) + 2) (affineLimitCandidate (oldEmbedding e) t)

theorem unmet_eq (e : (ι ⊕ κ) ↪ ℕ) (t : ι → ℝ) (s : κ → ℝ) :
    unmet closedSpace (limitRows_independent (oldEmbedding e)) (limitRows (newEmbedding e))
      hilbertOne t s = newDefect e t s := by
  funext j
  rw [unmet, ← affineLimitCandidate_eq]
  change s j - inner ℝ (coordinateLimitRepresenter (e (Sum.inr j) + 2))
    (affineLimitCandidate (oldEmbedding e) t) = _
  rw [coordinateLimitRepresenter_inner _ _ (affineLimitCandidate_mem (oldEmbedding e) t)]
  rfl

theorem fullCandidate_eq_affine (e : (ι ⊕ κ) ↪ ℕ) (t : ι → ℝ) (s : κ → ℝ) :
    affineLimitCandidate e (Sum.elim t s) =
      affineCandidate closedSpace (joined_independent e) hilbertOne (Sum.elim t s) := by
  simpa only [joinedRows_eq] using affineLimitCandidate_eq e (Sum.elim t s)

/-- The whole screened source, including every interaction with old constraints. -/
theorem candidate_block_update (e : (ι ⊕ κ) ↪ ℕ) (t : ι → ℝ) (s : κ → ℝ) :
    affineLimitCandidate e (Sum.elim t s) = affineLimitCandidate (oldEmbedding e) t +
      minimumVector (screenedRows_independent e) (newDefect e t s) := by
  have h := candidate_update closedSpace (limitRows_independent (oldEmbedding e))
    (limitRows (newEmbedding e)) (joined_independent e) hilbertOne t s
  rw [← fullCandidate_eq_affine e t s, ← affineLimitCandidate_eq, unmet_eq] at h
  exact h

theorem error_block_update (e : (ι ⊕ κ) ↪ ℕ) (t : ι → ℝ) (s : κ → ℝ) :
    ‖hilbertOne - affineLimitCandidate e (Sum.elim t s)‖ ^ 2 =
      ‖hilbertOne - affineLimitCandidate (oldEmbedding e) t‖ ^ 2 +
        capacity (screenedRows_independent e) (newDefect e t s) := by
  have h := error_update closedSpace (limitRows_independent (oldEmbedding e))
    (limitRows (newEmbedding e)) (joined_independent e)
    (limitRows_mem (oldEmbedding e)) (limitRows_mem (newEmbedding e)) hilbertOne t s
  rw [← fullCandidate_eq_affine e t s, ← affineLimitCandidate_eq, unmet_eq] at h
  exact h

theorem error_block_displacement (e : (ι ⊕ κ) ↪ ℕ) (t : ι → ℝ) (s : κ → ℝ) :
    ‖hilbertOne - affineLimitCandidate e (Sum.elim t s)‖ ^ 2 =
      ‖hilbertOne - affineLimitCandidate (oldEmbedding e) t‖ ^ 2 +
        ‖affineLimitCandidate e (Sum.elim t s) - affineLimitCandidate (oldEmbedding e) t‖ ^ 2 := by
  have h := error_update_displacement closedSpace (limitRows_independent (oldEmbedding e))
    (limitRows (newEmbedding e)) (joined_independent e)
    (limitRows_mem (oldEmbedding e)) (limitRows_mem (newEmbedding e)) hilbertOne t s
  rw [← fullCandidate_eq_affine e t s, ← affineLimitCandidate_eq] at h
  exact h

theorem error_block_equal_iff (e : (ι ⊕ κ) ↪ ℕ) (t : ι → ℝ) (s : κ → ℝ) :
    ‖hilbertOne - affineLimitCandidate e (Sum.elim t s)‖ ^ 2 =
      ‖hilbertOne - affineLimitCandidate (oldEmbedding e) t‖ ^ 2 ↔
      ∀ j, coefficientCLM (e (Sum.inr j) + 2) (affineLimitCandidate (oldEmbedding e) t) = s j := by
  have h := error_equal_iff closedSpace (limitRows_independent (oldEmbedding e))
    (limitRows (newEmbedding e)) (joined_independent e)
    (limitRows_mem (oldEmbedding e)) (limitRows_mem (newEmbedding e)) hilbertOne t s
  rw [← fullCandidate_eq_affine e t s, ← affineLimitCandidate_eq] at h
  have hp (j : κ) : inner ℝ (limitRows (newEmbedding e) j)
      (affineLimitCandidate (oldEmbedding e) t) =
      coefficientCLM (e (Sum.inr j) + 2) (affineLimitCandidate (oldEmbedding e) t) :=
    coordinateLimitRepresenter_inner _ _ (affineLimitCandidate_mem (oldEmbedding e) t)
  simpa only [hp] using h

end RiemannResearch.RH.RamanujanConstraintBlocks
