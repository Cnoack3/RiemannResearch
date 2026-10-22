import RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual finite weighted quotient defect has complementary rank

Source: user-provided `RH_Two_Seed_Threshold.tex`, September 8, 2026,
Section 10, Proposition `prop:crt-defect`. The averaging map and repetition
are built from the finite quotient weights, rather than supplied as abstract
projections. Nonzero fiber mass supplies their exact right inverse. The
defect has range equal to the kernel of averaging, and therefore rank equal
to fine cardinality minus coarse cardinality.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.WeightedFiniteQuotient

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem pushforward_add (q : ι → κ) (z z' : ι → ℝ) (b : κ) :
    pushforward q (fun i => z i + z' i) b =
      pushforward q z b + pushforward q z' b := by
  unfold pushforward
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i = b <;> simp [h]

theorem pushforward_smul (q : ι → κ) (z : ι → ℝ) (c : ℝ) (b : κ) :
    pushforward q (fun i => c * z i) b = c * pushforward q z b := by
  unfold pushforward
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q i = b <;> simp [h]

/-- The true finite weighted conditional operator as a linear map. -/
def averageLinearMap (q : ι → κ) (w : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) where
  toFun := average q w
  map_add' := by
    intro x y
    funext b
    change pushforward q (fun i => w i * (x i + y i)) b / pushforward q w b =
      pushforward q (fun i => w i * x i) b / pushforward q w b +
      pushforward q (fun i => w i * y i) b / pushforward q w b
    simp only [mul_add, pushforward_add, add_div]
  map_smul' := by
    intro c x
    funext b
    change pushforward q (fun i => w i * (c * x i)) b / pushforward q w b =
      c * (pushforward q (fun i => w i * x i) b / pushforward q w b)
    have he : (fun i => w i * (c * x i)) = (fun i => c * (w i * x i)) := by
      funext i
      ring
    rw [he, pushforward_smul]
    ring

/-- Quotient repetition as an injective linear map when all fibers have mass. -/
def repeatLinearMap (q : ι → κ) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := fun g => g ∘ q
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

/-- The complete projection defect, including all weighted coordinates. -/
def defectLinearMap (q : ι → κ) (w : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.id - (repeatLinearMap q).comp (averageLinearMap q w)

theorem averageLinearMap_surjective (q : ι → κ) (w : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    Function.Surjective (averageLinearMap q w) := by
  intro g
  exact ⟨g ∘ q, average_pullback q w hW g⟩

theorem defectLinearMap_apply (q : ι → κ) (w x : ι → ℝ) :
    defectLinearMap q w x = x - average q w x ∘ q := rfl

/-- Exact identification of unresolved fine directions. -/
theorem defect_range_eq_average_ker (q : ι → κ) (w : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    LinearMap.range (defectLinearMap q w) = LinearMap.ker (averageLinearMap q w) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change averageLinearMap q w (y - average q w y ∘ q) = 0
    rw [map_sub]
    change average q w y - average q w (average q w y ∘ q) = 0
    rw [average_pullback q w hW, sub_self]
  · intro hx
    have hz : average q w x = 0 := hx
    refine ⟨x, ?_⟩
    rw [defectLinearMap_apply, hz]
    simp

/-- The defect rank is exactly the number of fine coordinates lost on quotienting. -/
theorem defect_finrank (q : ι → κ) (w : ι → ℝ)
    (hW : ∀ b, pushforward q w b ≠ 0) :
    Module.finrank ℝ (LinearMap.range (defectLinearMap q w)) =
      Fintype.card ι - Fintype.card κ := by
  rw [defect_range_eq_average_ker q w hW]
  have hr : LinearMap.range (averageLinearMap q w) = ⊤ :=
    LinearMap.range_eq_top.mpr (averageLinearMap_surjective q w hW)
  have h := LinearMap.finrank_range_add_finrank_ker (averageLinearMap q w)
  rw [hr] at h
  have hh : Fintype.card κ + Module.finrank ℝ (LinearMap.ker (averageLinearMap q w)) =
      Fintype.card ι := by simpa using h
  omega

end
end RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
