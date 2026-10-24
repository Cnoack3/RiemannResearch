import RiemannResearch.RH.RamanujanNestedAffineGeometry
import RiemannResearch.RH.RamanujanMultipleAffineLimits
import RiemannResearch.Analysis.AffineObservationSensitivity
import RiemannResearch.Analysis.FiniteGramContinuity

/-!
# Sharp target sensitivity of finite and closed Ramanujan optimizers

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
Prescribed original coefficient vectors carry the full inverse source-Gram
metric. Optimizer displacement equals that metric exactly. The minimum
error is strictly convex in the requested coefficient vector, with its
entire curvature term explicit. Sensitivity improves as the packet stage
grows, and its finite-to-closed gap is another full norm-square remainder.
-/

noncomputable section
namespace RiemannResearch.RH.RamanujanTargetSensitivity
open Pareto Pareto.CoefficientStabilization
open RamanujanMultipleCapacityLimits RamanujanMultipleAffineLimits RamanujanNestedAffineGeometry
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteGramContinuity
open RiemannResearch.Analysis.AffineObservationSensitivity

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem finite_candidate_sub (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) (t s : κ → ℝ) :
    affineFiniteCandidate n e t - affineFiniteCandidate n e s = matrixMinimum (finiteRows n e) (t - s) := by
  rw [affineFiniteCandidate_eq_affine n e hn t, affineFiniteCandidate_eq_affine n e hn s,
    matrixMinimum_eq_minimumVector (finiteRows_independent n e hn)]
  exact affineCandidate_sub (finiteSpace n) (finiteRows_independent n e hn) hilbertOne t s

theorem limit_candidate_sub (e : κ ↪ ℕ) (t s : κ → ℝ) :
    affineLimitCandidate e t - affineLimitCandidate e s = minimumVector (limitRows_independent e) (t - s) := by
  rw [affineLimitCandidate_eq, affineLimitCandidate_eq]
  exact affineCandidate_sub closedSpace (limitRows_independent e) hilbertOne t s

/-- Full inverse-Gram distance; no diagonal or coordinatewise upper replacement. -/
theorem finite_candidate_distance (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) (t s : κ → ℝ) :
    ‖affineFiniteCandidate n e t - affineFiniteCandidate n e s‖ ^ 2 = inverseCapacity n e (t - s) := by
  rw [finite_candidate_sub n e hn t s, inverseCapacity_eq n e hn,
    matrixMinimum_eq_minimumVector (finiteRows_independent n e hn), capacity_eq_norm_sq]

theorem limit_candidate_distance (e : κ ↪ ℕ) (t s : κ → ℝ) :
    ‖affineLimitCandidate e t - affineLimitCandidate e s‖ ^ 2 = capacity (limitRows_independent e) (t - s) := by
  rw [limit_candidate_sub, capacity_eq_norm_sq]

theorem finite_error_interpolation (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n)
    (t s : κ → ℝ) (θ : ℝ) :
    ‖hilbertOne - affineFiniteCandidate n e ((1 - θ) • t + θ • s)‖ ^ 2 =
      (1 - θ) * ‖hilbertOne - affineFiniteCandidate n e t‖ ^ 2 +
        θ * ‖hilbertOne - affineFiniteCandidate n e s‖ ^ 2 -
          θ * (1 - θ) * inverseCapacity n e (t - s) := by
  simp only [affineFiniteCandidate_eq_affine n e hn, inverseCapacity_eq n e hn]
  exact affine_error_interpolation (finiteSpace n) (finiteRows_independent n e hn) hilbertOne t s θ

theorem finite_error_strict_convex (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n)
    (t s : κ → ℝ) (hts : t ≠ s) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ‖hilbertOne - affineFiniteCandidate n e ((1 - θ) • t + θ • s)‖ ^ 2 <
      (1 - θ) * ‖hilbertOne - affineFiniteCandidate n e t‖ ^ 2 +
        θ * ‖hilbertOne - affineFiniteCandidate n e s‖ ^ 2 := by
  simp only [affineFiniteCandidate_eq_affine n e hn]
  exact affine_error_strict_convex (finiteSpace n) (finiteRows_independent n e hn) hilbertOne t s hts θ hθ hθ1

theorem limit_error_interpolation (e : κ ↪ ℕ) (t s : κ → ℝ) (θ : ℝ) :
    ‖hilbertOne - affineLimitCandidate e ((1 - θ) • t + θ • s)‖ ^ 2 =
      (1 - θ) * ‖hilbertOne - affineLimitCandidate e t‖ ^ 2 +
        θ * ‖hilbertOne - affineLimitCandidate e s‖ ^ 2 -
          θ * (1 - θ) * capacity (limitRows_independent e) (t - s) := by
  simp only [affineLimitCandidate_eq]
  exact affine_error_interpolation closedSpace (limitRows_independent e) hilbertOne t s θ

theorem limit_error_strict_convex (e : κ ↪ ℕ) (t s : κ → ℝ)
    (hts : t ≠ s) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ‖hilbertOne - affineLimitCandidate e ((1 - θ) • t + θ • s)‖ ^ 2 <
      (1 - θ) * ‖hilbertOne - affineLimitCandidate e t‖ ^ 2 +
        θ * ‖hilbertOne - affineLimitCandidate e s‖ ^ 2 := by
  simp only [affineLimitCandidate_eq]
  exact affine_error_strict_convex closedSpace (limitRows_independent e) hilbertOne t s hts θ hθ hθ1

/-- Enlarging the legal dictionary improves every prescribed-target sensitivity direction. -/
theorem sensitivity_stage_le (n k : ℕ) (hnk : n ≤ k) (e : κ ↪ ℕ)
    (hn : ∀ j, e j < n) (t s : κ → ℝ) :
    ‖affineFiniteCandidate k e t - affineFiniteCandidate k e s‖ ^ 2 ≤
      ‖affineFiniteCandidate n e t - affineFiniteCandidate n e s‖ ^ 2 := by
  have hk : ∀ j, e j < k := fun j => lt_of_lt_of_le (hn j) hnk
  rw [finite_candidate_distance k e hk, finite_candidate_distance n e hn]
  exact inverseCapacity_stage_le n k hnk e hn (t - s)

/-- Exact sensitivity gap to the full closed-space optimizer. -/
theorem sensitivity_limit_exact (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) (t s : κ → ℝ) :
    ‖affineFiniteCandidate n e t - affineFiniteCandidate n e s‖ ^ 2 =
      ‖affineLimitCandidate e t - affineLimitCandidate e s‖ ^ 2 +
        ‖(affineFiniteCandidate n e t - affineFiniteCandidate n e s) -
          (affineLimitCandidate e t - affineLimitCandidate e s)‖ ^ 2 := by
  rw [finite_candidate_distance n e hn, limit_candidate_distance,
    finite_candidate_sub n e hn, limit_candidate_sub]
  exact inverseCapacity_limit_exact n e hn (t - s)

end RiemannResearch.RH.RamanujanTargetSensitivity
