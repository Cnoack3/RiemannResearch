import RiemannResearch.Analysis.AffineObservationProjection
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact affine projection with finitely many prescribed observations

Source: user-requested fourth Ramanujan dual continuation, 23 October 2026.
The scalar affine observation theorem is strengthened to arbitrary finite
independent observations inside an orthogonally complemented subspace.
The whole inverse observation Gram and the complete norm-square remainder
are retained. The ambient subspace need not be finite dimensional.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.MultipleAffineObservationProjection
open FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity
open SingleObservationProjection

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def affineMismatch (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (v : ι → H) (f : H) (t : ι → ℝ) (i : ι) : ℝ :=
  t i - inner ℝ (v i) (K.starProjection f)

def affineCandidate (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t : ι → ℝ) : H :=
  K.starProjection f + minimumVector hv (affineMismatch K v f t)

theorem minimumVector_mem (K : Submodule ℝ H) {v : ι → H}
    (hv : LinearIndependent ℝ v) (hmem : ∀ i, v i ∈ K) (b : ι → ℝ) :
    minimumVector hv b ∈ K := by
  rw [minimumVector, Fintype.linearCombination_apply]
  apply K.sum_mem
  intro i _
  exact K.smul_mem _ (hmem i)

theorem affineCandidate_mem (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (hmem : ∀ i, v i ∈ K)
    (f : H) (t : ι → ℝ) : affineCandidate K hv f t ∈ K :=
  K.add_mem (K.starProjection_apply_mem f) (minimumVector_mem K hv hmem _)

theorem affineCandidate_observation (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t : ι → ℝ) (i : ι) :
    inner ℝ (v i) (affineCandidate K hv f t) = t i := by
  rw [affineCandidate, inner_add_right, minimumVector_observation]
  unfold affineMismatch
  ring

theorem affineCandidate_energy (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (hmem : ∀ i, v i ∈ K)
    (f : H) (t : ι → ℝ) :
    ‖f - affineCandidate K hv f t‖ ^ 2 =
      ‖f - K.starProjection f‖ ^ 2 + capacity hv (affineMismatch K v f t) := by
  rw [affine_target_error_split K f _ (affineCandidate_mem K hv hmem f t)]
  have hd : affineCandidate K hv f t - K.starProjection f =
      minimumVector hv (affineMismatch K v f t) := by
    unfold affineCandidate
    abel
  rw [hd, ← capacity_eq_norm_sq]

/-- Full minimization over the entire affine slice of the closed legal space. -/
theorem affineCandidate_completion (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t : ι → ℝ)
    (x : H) (hx : x ∈ K) (hobs : ∀ i, inner ℝ (v i) x = t i) :
    ‖f - x‖ ^ 2 = ‖f - K.starProjection f‖ ^ 2 +
      capacity hv (affineMismatch K v f t) + ‖x - affineCandidate K hv f t‖ ^ 2 := by
  have hdx : ∀ i, inner ℝ (v i) (x - K.starProjection f) = affineMismatch K v f t i := by
    intro i
    rw [inner_sub_right, hobs]
    rfl
  have he := feasible_norm_sq_completion hv (affineMismatch K v f t)
    (x - K.starProjection f) hdx
  have hd : x - K.starProjection f - minimumVector hv (affineMismatch K v f t) =
      x - affineCandidate K hv f t := by
    unfold affineCandidate
    abel
  rw [hd, ← capacity_eq_norm_sq] at he
  rw [affine_target_error_split K f x hx, he]
  ring

theorem affineCandidate_optimal_iff (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (hmem : ∀ i, v i ∈ K)
    (f : H) (t : ι → ℝ) (x : H) (hx : x ∈ K)
    (hobs : ∀ i, inner ℝ (v i) x = t i) :
    ‖f - x‖ ^ 2 = ‖f - K.starProjection f‖ ^ 2 +
      capacity hv (affineMismatch K v f t) ↔ x = affineCandidate K hv f t := by
  constructor
  · intro he
    have hc := affineCandidate_completion K hv f t x hx hobs
    have hz : ‖x - affineCandidate K hv f t‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · rintro rfl
    exact affineCandidate_energy K hv hmem f t

end RiemannResearch.Analysis.MultipleAffineObservationProjection
