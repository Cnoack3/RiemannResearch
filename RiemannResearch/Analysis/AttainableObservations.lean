import RiemannResearch.Analysis.FiniteRegularizedConstraints
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Attainable observations and irreducible inconsistency

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
No independence or consistency of the observation rows is assumed. Orthogonal
projection of the requested data onto the actual observation range separates
an exactly attainable request from a fixed, irreducible squared residual.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.AttainableObservations
open FiniteHilbertGram FiniteRegularizedConstraints
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Observation columns as vectors in the actual Euclidean data space. -/
def column (B : Matrix κ ι ℝ) (i : ι) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun j => B j i)

def observationSpace (B : Matrix κ ι ℝ) : Submodule ℝ (EuclideanSpace ℝ κ) :=
  (Fintype.linearCombination ℝ (column B)).range

def projectedTarget (B : Matrix κ ι ℝ) (t : κ → ℝ) : κ → ℝ :=
  ((observationSpace B).starProjection (WithLp.toLp 2 t)).ofLp

/-- The part of a requested observation vector that no legal coefficients attain. -/
def inconsistency (B : Matrix κ ι ℝ) (t : κ → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 t : EuclideanSpace ℝ κ) -
    (observationSpace B).starProjection (WithLp.toLp 2 t)‖ ^ 2

private def dataCoordinate (j : κ) : EuclideanSpace ℝ κ →ₗ[ℝ] ℝ where
  toFun x := x.ofLp j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem column_synthesis (B : Matrix κ ι ℝ) (a : ι → ℝ) :
    Fintype.linearCombination ℝ (column B) a = WithLp.toLp 2 (observe B a) := by
  apply WithLp.ofLp_injective 2
  funext j
  change dataCoordinate j (Fintype.linearCombination ℝ (column B) a) = observe B a j
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, dataCoordinate,
    column, WithLp.ofLp_toLp, observe, smul_eq_mul]
  rfl

theorem observation_mem (B : Matrix κ ι ℝ) (a : ι → ℝ) :
    (WithLp.toLp 2 (observe B a) : EuclideanSpace ℝ κ) ∈ observationSpace B := by
  rw [← column_synthesis]
  exact ⟨a, rfl⟩

theorem projectedTarget_feasible (B : Matrix κ ι ℝ) (t : κ → ℝ) :
    ∃ a : ι → ℝ, ∀ j, observe B a j = projectedTarget B t j := by
  obtain ⟨a, ha⟩ := (observationSpace B).starProjection_apply_mem (WithLp.toLp 2 t)
  refine ⟨a, fun j => ?_⟩
  rw [column_synthesis] at ha
  exact congrArg (fun x : EuclideanSpace ℝ κ => x.ofLp j) ha

private theorem data_norm_sq (x : EuclideanSpace ℝ κ) :
    ‖x‖ ^ 2 = ∑ j, (x.ofLp j) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp [RCLike.inner_apply', pow_two]

private theorem mismatch_as_norm (B : Matrix κ ι ℝ) (t : κ → ℝ) (a : ι → ℝ) :
    mismatchEnergy B t a =
      ‖(WithLp.toLp 2 t : EuclideanSpace ℝ κ) - WithLp.toLp 2 (observe B a)‖ ^ 2 := by
  rw [data_norm_sq]
  unfold mismatchEnergy
  apply Finset.sum_congr rfl
  intro j _
  change (observe B a j - t j) ^ 2 = (t j - observe B a j) ^ 2
  ring

/-- Full Pythagorean separation of attainable mismatch and inconsistent data. -/
theorem mismatch_decomposition (B : Matrix κ ι ℝ) (t : κ → ℝ) (a : ι → ℝ) :
    mismatchEnergy B t a = inconsistency B t +
      mismatchEnergy B (projectedTarget B t) a := by
  let K := observationSpace B
  let y : EuclideanSpace ℝ κ := WithLp.toLp 2 t
  let z : EuclideanSpace ℝ κ := WithLp.toLp 2 (observe B a)
  have hz : z ∈ K := observation_mem B a
  have hp : K.starProjection y - z ∈ K := K.sub_mem (K.starProjection_apply_mem y) hz
  have ho : inner ℝ (y - K.starProjection y) (K.starProjection y - z) = 0 := by
    rw [real_inner_comm]
    exact (K.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal y) _ hp
  rw [mismatch_as_norm, mismatch_as_norm]
  change ‖y - z‖ ^ 2 = ‖y - K.starProjection y‖ ^ 2 + ‖K.starProjection y - z‖ ^ 2
  rw [show y - z = (y - K.starProjection y) + (K.starProjection y - z) by abel,
    norm_add_sq_real, ho, mul_zero, add_zero]

theorem inconsistency_nonneg (B : Matrix κ ι ℝ) (t : κ → ℝ) :
    0 ≤ inconsistency B t := sq_nonneg _

theorem inconsistency_le_mismatch (B : Matrix κ ι ℝ) (t : κ → ℝ) (a : ι → ℝ) :
    inconsistency B t ≤ mismatchEnergy B t a := by
  rw [mismatch_decomposition]
  exact le_add_of_nonneg_right (mismatchEnergy_nonneg _ _ _)

/-- Zero inconsistency is exactly simultaneous feasibility, including redundant rows. -/
theorem inconsistency_zero_iff (B : Matrix κ ι ℝ) (t : κ → ℝ) :
    inconsistency B t = 0 ↔ ∃ a : ι → ℝ, ∀ j, observe B a j = t j := by
  constructor
  · intro h
    have hp : (observationSpace B).starProjection (WithLp.toLp 2 t) =
        (WithLp.toLp 2 t : EuclideanSpace ℝ κ) := by
      exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h))).symm
    obtain ⟨a, ha⟩ := projectedTarget_feasible B t
    refine ⟨a, fun j => ?_⟩
    rw [ha, projectedTarget, hp]
  · rintro ⟨a, ha⟩
    have hm : (WithLp.toLp 2 t : EuclideanSpace ℝ κ) ∈ observationSpace B := by
      rw [← show observe B a = t from funext ha]
      exact observation_mem B a
    unfold inconsistency
    rw [Submodule.starProjection_eq_self_iff.mpr hm, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Inconsistent requests alter the objective by an exact coefficient-independent constant. -/
theorem objective_decomposition (v : ι → H) (B : Matrix κ ι ℝ)
    (f : H) (t : κ → ℝ) (ρ : ℝ) (a : ι → ℝ) :
    objective v B f t ρ a = objective v B f (projectedTarget B t) ρ a +
      ρ ^ 2 * inconsistency B t := by
  unfold objective
  rw [mismatch_decomposition]
  ring

/-- The optimizer discards exactly the impossible component of the observations. -/
theorem coefficients_projectedTarget {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    coefficients hv B f t ρ = coefficients hv B f (projectedTarget B t) ρ := by
  apply (coefficients_optimal_iff hv B f (projectedTarget B t) ρ _).mp
  have h₁ := coefficients_minimizes hv B f t ρ (coefficients hv B f (projectedTarget B t) ρ)
  have h₂ := coefficients_minimizes hv B f (projectedTarget B t) ρ (coefficients hv B f t ρ)
  rw [objective_decomposition v B f t ρ (coefficients hv B f t ρ),
    objective_decomposition v B f t ρ (coefficients hv B f (projectedTarget B t) ρ)] at h₁
  linarith

/-- Exact consistency correction and a uniform finite comparator bound. -/
theorem excess_objective_bounds {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (a : ι → ℝ)
    (ha : ∀ j, observe B a j = projectedTarget B t j) :
    0 ≤ objective v B f t ρ (coefficients hv B f t ρ) - ρ ^ 2 * inconsistency B t ∧
    objective v B f t ρ (coefficients hv B f t ρ) - ρ ^ 2 * inconsistency B t ≤
      ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 := by
  rw [objective_decomposition, add_sub_cancel_right, coefficients_projectedTarget]
  constructor
  · exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (mismatchEnergy_nonneg _ _ _))
  · exact feasible_comparator hv B f (projectedTarget B t) ρ a ha

end RiemannResearch.Analysis.AttainableObservations
