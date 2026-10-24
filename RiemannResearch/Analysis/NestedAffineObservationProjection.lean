import RiemannResearch.Analysis.MultipleAffineObservationProjection
import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.Tactic.Linarith

/-!
# Nested legal spaces with fixed simultaneous affine observations

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
Enlarging the legal space decreases both constrained approximation error
and every inverse observation-Gram quadratic form. The decrease is exactly
the squared displacement of the corresponding minimizers, with sharp
equality criteria. The finite observation rows are projected actual vectors.
-/

noncomputable section
namespace RiemannResearch.Analysis.NestedAffineObservationProjection
open FiniteHilbertConstraints FiniteGramCapacity MultipleAffineObservationProjection

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def restrictedRows (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (r : ι → H) (i : ι) : H := K.starProjection (r i)

theorem restrictedRows_mem (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (r : ι → H) (i : ι) : restrictedRows K r i ∈ K := K.starProjection_apply_mem (r i)

theorem restrictedRows_pairing (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (r : ι → H) (i : ι) (x : H) (hx : x ∈ K) :
    inner ℝ (restrictedRows K r i) x = inner ℝ (r i) x := by
  have h : inner ℝ (r i - K.starProjection (r i)) x = 0 := by
    rw [real_inner_comm]
    exact (K.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal (r i)) _ hx
  rw [inner_sub_left] at h
  exact (sub_eq_zero.mp h).symm

/-- The full constrained error decrease for two nested legal spaces. -/
theorem nested_affine_error_exact (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L)
    (r : ι → H) (hK : LinearIndependent ℝ (restrictedRows K r))
    (hL : LinearIndependent ℝ (restrictedRows L r)) (f : H) (t : ι → ℝ) :
    ‖f - affineCandidate K hK f t‖ ^ 2 =
      ‖f - affineCandidate L hL f t‖ ^ 2 +
        ‖affineCandidate K hK f t - affineCandidate L hL f t‖ ^ 2 := by
  have hm := affineCandidate_mem K hK (restrictedRows_mem K r) f t
  have ho : ∀ i, inner ℝ (restrictedRows L r i) (affineCandidate K hK f t) = t i := by
    intro i
    rw [restrictedRows_pairing L r i _ (hKL hm),
      ← restrictedRows_pairing K r i _ hm]
    exact affineCandidate_observation K hK f t i
  have he := affineCandidate_completion L hL f t _ (hKL hm) ho
  rw [← affineCandidate_energy L hL (restrictedRows_mem L r) f t] at he
  exact he

theorem nested_affine_equal_iff (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L)
    (r : ι → H) (hK : LinearIndependent ℝ (restrictedRows K r))
    (hL : LinearIndependent ℝ (restrictedRows L r)) (f : H) (t : ι → ℝ) :
    ‖f - affineCandidate K hK f t‖ ^ 2 = ‖f - affineCandidate L hL f t‖ ^ 2 ↔
      affineCandidate K hK f t = affineCandidate L hL f t := by
  constructor
  · intro he
    have h := nested_affine_error_exact K L hKL r hK hL f t
    have hz : ‖affineCandidate K hK f t - affineCandidate L hL f t‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro he
    rw [he]

/-- Exact inverse-Gram Loewner monotonicity, expressed in every source direction. -/
theorem nested_capacity_exact (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L)
    (r : ι → H) (hK : LinearIndependent ℝ (restrictedRows K r))
    (hL : LinearIndependent ℝ (restrictedRows L r)) (b : ι → ℝ) :
    capacity hK b = capacity hL b + ‖minimumVector hK b - minimumVector hL b‖ ^ 2 := by
  have hm := minimumVector_mem K hK (restrictedRows_mem K r) b
  have ho : ∀ i, inner ℝ (restrictedRows L r i) (minimumVector hK b) = b i := by
    intro i
    rw [restrictedRows_pairing L r i _ (hKL hm),
      ← restrictedRows_pairing K r i _ hm]
    exact minimumVector_observation hK b i
  have h := feasible_norm_sq_completion hL b (minimumVector hK b) ho
  simpa only [← capacity_eq_norm_sq] using h

theorem nested_capacity_equal_iff (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L)
    (r : ι → H) (hK : LinearIndependent ℝ (restrictedRows K r))
    (hL : LinearIndependent ℝ (restrictedRows L r)) (b : ι → ℝ) :
    capacity hK b = capacity hL b ↔ minimumVector hK b = minimumVector hL b := by
  constructor
  · intro he
    have h := nested_capacity_exact K L hKL r hK hL b
    have hz : ‖minimumVector hK b - minimumVector hL b‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro he
    rw [capacity_eq_norm_sq, capacity_eq_norm_sq, he]

end RiemannResearch.Analysis.NestedAffineObservationProjection
