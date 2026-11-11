import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import RiemannResearch.LinearAlgebra.ObliqueBlockElimination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Screened coordinates for finite accretive collocation

Source: CanonicalPrimePowerUpdatesResearch20261107.md, Section 3.
The physical Gram form and the nonsymmetric difference-test system are
distinct. All inverses below are constructed from independence and strict
accretivity; the exact signed energy retains the old-vector cross term.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteScreenedCollocation
open FiniteHilbertGram FiniteGramCapacity

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual difference-test observations, linear in the response. -/
def observe (D : H →ₗ[ℝ] H) (v : ι → H) : H →ₗ[ℝ] (ι → ℝ) where
  toFun f i := inner ℝ f (D (v i))
  map_add' f g := by ext i; exact inner_add_left _ _ _
  map_smul' r f := by ext i; exact real_inner_smul_left _ _ _

/-- Rows are tests, columns are synthesized vectors; this need not be symmetric. -/
def block (D : H →ₗ[ℝ] H) (v : ι → H) (w : κ → H) :
    (κ → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (observe D v).comp (Fintype.linearCombination ℝ w)

omit [Fintype ι] in
theorem block_apply (D : H →ₗ[ℝ] H) (v : ι → H) (w : κ → H)
    (c : κ → ℝ) (i : ι) :
    block D v w c i = ∑ j, c j * inner ℝ (w j) (D (v i)) :=
  inner_synthesis_left w c _

theorem diagonal_pairing (D : H →ₗ[ℝ] H) (v : ι → H) (c : ι → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ v c)
      (D (Fintype.linearCombination ℝ v c)) =
        ∑ i, c i * block D v v c i := by
  rw [Fintype.linearCombination_apply, map_sum]
  simp only [map_smul, inner_sum, inner_smul_right]
  rfl

theorem collocation_injective (D : H →ₗ[ℝ] H)
    (hD : ∀ f, inner ℝ f (D f) = 0 → f = 0)
    {v : ι → H} (hv : LinearIndependent ℝ v) :
    Function.Injective (block D v v) := by
  intro c d hcd
  have hz : block D v v (c - d) = 0 := by rw [map_sub, hcd, sub_self]
  have hs : Fintype.linearCombination ℝ v (c - d) = 0 := by
    apply hD
    rw [diagonal_pairing, hz]
    simp
  apply sub_eq_zero.mp
  apply hv.fintypeLinearCombination_injective
  simpa only [map_zero] using hs

/-- The actual nonsymmetric collocation inverse, with no invertibility assumption. -/
def collocationEquiv (D : H →ₗ[ℝ] H)
    (hD : ∀ f, inner ℝ f (D f) = 0 → f = 0)
    {v : ι → H} (hv : LinearIndependent ℝ v) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofInjectiveEndo (block D v v) (collocation_injective D hD hv)

/-- Coefficients computed from the prescribed test source. -/
def solution (D : H →ₗ[ℝ] H)
    (hD : ∀ f, inner ℝ f (D f) = 0 → f = 0)
    {v : ι → H} (hv : LinearIndependent ℝ v) (h : H) : ι → ℝ :=
  (collocationEquiv D hD hv).symm (observe D v h)

theorem solution_match (D : H →ₗ[ℝ] H)
    (hD : ∀ f, inner ℝ f (D f) = 0 → f = 0)
    {v : ι → H} (hv : LinearIndependent ℝ v) (h : H) :
    block D v v (solution D hD hv h) = observe D v h :=
  (collocationEquiv D hD hv).apply_symm_apply _

/-- Identifies the inverse-system synthesis with any finite trial vector
having the prescribed observations. -/
theorem solution_synthesis_eq (D : H →ₗ[ℝ] H)
    (hD : ∀ f, inner ℝ f (D f) = 0 → f = 0)
    {v : ι → H} (hv : LinearIndependent ℝ v) (h f : H)
    (hf : f ∈ Submodule.span ℝ (Set.range v))
    (hm : observe D v f = observe D v h) :
    Fintype.linearCombination ℝ v (solution D hD hv h) = f := by
  have hr : f ∈ (Fintype.linearCombination ℝ v).range := by
    rw [Fintype.range_linearCombination]
    exact hf
  obtain ⟨c, hc⟩ := hr
  have he : solution D hD hv h = c := by
    apply collocation_injective D hD hv
    rw [solution_match]
    change observe D v h = observe D v (Fintype.linearCombination ℝ v c)
    rw [hc, hm]
  rw [he, hc]

theorem synthesis_join (u : ι → H) (w : κ → H)
    (x : ι → ℝ) (y : κ → ℝ) :
    Fintype.linearCombination ℝ (Sum.elim u w) (Sum.elim x y) =
      Fintype.linearCombination ℝ u x + Fintype.linearCombination ℝ w y := by
  simp only [Fintype.linearCombination_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]

/-- The full collocation kernel is trivial, so Schur inversion adds no hypothesis. -/
theorem block_kernel (D : H →ₗ[ℝ] H)
    (hD : ∀ f, inner ℝ f (D f) = 0 → f = 0)
    (u : ι → H) (w : κ → H)
    (hall : LinearIndependent ℝ (Sum.elim u w))
    (x : ι → ℝ) (y : κ → ℝ)
    (h0 : block D u u x + block D u w y = 0)
    (h1 : block D w u x + block D w w y = 0) : y = 0 := by
  have hz : block D (Sum.elim u w) (Sum.elim u w) (Sum.elim x y) = 0 := by
    ext k
    change inner ℝ (Fintype.linearCombination ℝ (Sum.elim u w) (Sum.elim x y))
      (D (Sum.elim u w k)) = 0
    rw [synthesis_join, inner_add_left]
    cases k with
    | inl i => exact congrFun h0 i
    | inr j => exact congrFun h1 j
  have hc : Sum.elim x y = 0 := (collocation_injective D hD hall)
    (by simpa only [map_zero] using hz)
  ext j
  exact congrFun hc (Sum.inr j)

theorem synthesis_screened_orthogonal {u : ι → H} (hu : LinearIndependent ℝ u)
    (v : κ → H) (x : ι → ℝ) (y : κ → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ u x)
      (Fintype.linearCombination ℝ (screened hu v) y) = 0 := by
  rw [inner_synthesis_left]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fintype.linearCombination_apply, inner_sum]
  simp only [inner_smul_right, inner_old_screened, mul_zero,
    Finset.sum_const_zero]

theorem joined_screened_independent {u : ι → H} (hu : LinearIndependent ℝ u)
    (v : κ → H) (hall : LinearIndependent ℝ (Sum.elim u v)) :
    LinearIndependent ℝ (Sum.elim u (screened hu v)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  let x : ι → ℝ := fun i => c (Sum.inl i)
  let y : κ → ℝ := fun j => c (Sum.inr j)
  have hsplit : c = Sum.elim x y := by ext k; cases k <;> rfl
  have he : Fintype.linearCombination ℝ u x +
      Fintype.linearCombination ℝ (screened hu v) y = 0 := by
    have hh : Fintype.linearCombination ℝ (Sum.elim u (screened hu v)) c = 0 := hc
    rw [hsplit, synthesis_join] at hh
    exact hh
  have hx0 : Fintype.linearCombination ℝ u x = 0 := by
    have hh := congrArg (fun z => inner ℝ (Fintype.linearCombination ℝ u x) z) he
    rw [inner_add_right, synthesis_screened_orthogonal, add_zero,
      inner_zero_right, real_inner_self_eq_norm_sq] at hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
  have hy0 : Fintype.linearCombination ℝ (screened hu v) y = 0 := by
    simpa only [hx0, zero_add] using he
  have hx : x = 0 := hu.fintypeLinearCombination_injective (by simpa using hx0)
  have hy : y = 0 := (screened_linearIndependent hu v hall).fintypeLinearCombination_injective
    (by simpa using hy0)
  cases k with
  | inl i => exact congrFun hx i
  | inr j => exact congrFun hy j

omit [Fintype κ] in
/-- Orthogonal screening is a change of coordinates in the same finite space. -/
theorem span_screened {u : ι → H} (hu : LinearIndependent ℝ u) (v : κ → H) :
    Submodule.span ℝ (Set.range (Sum.elim u (screened hu v))) =
      Submodule.span ℝ (Set.range (Sum.elim u v)) := by
  have hold (w : κ → H) (c : ι → ℝ) :
      Fintype.linearCombination ℝ u c ∈ Submodule.span ℝ (Set.range (Sum.elim u w)) := by
    rw [Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    cases k with
    | inl i => exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    | inr j =>
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        (hold v (inverseCoeff hu (v j)))
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    cases k with
    | inl i => exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    | inr j =>
      have hj : screened hu v j ∈ Submodule.span ℝ (Set.range (Sum.elim u (screened hu v))) :=
        Submodule.subset_span ⟨Sum.inr j, rfl⟩
      have h := Submodule.add_mem _ hj
        (hold (screened hu v) (inverseCoeff hu (v j)))
      have he : screened hu v j +
          Fintype.linearCombination ℝ u (inverseCoeff hu (v j)) = v j := sub_add_cancel _ _
      rw [he] at h
      exact h

omit [Fintype κ] in
/-- Screening of the tests acts on the source with the same signed coefficients. -/
theorem screened_observe (D : H →ₗ[ℝ] H) {u : ι → H}
    (hu : LinearIndependent ℝ u) (v : κ → H) (f : H) (j : κ) :
    observe D (screened hu v) f j = observe D v f j -
      ∑ i, inverseCoeff hu (v j) i * observe D u f i := by
  change inner ℝ f (D (v j - Fintype.linearCombination ℝ u (inverseCoeff hu (v j)))) = _
  rw [map_sub, inner_sub_right, Fintype.linearCombination_apply, map_sum, inner_sum]
  simp only [map_smul, inner_smul_right]
  rfl

/-- Exact physical energy; the collocation Schur source is not substituted for a Gram response. -/
theorem signed_energy {u : ι → H} (hu : LinearIndependent ℝ u)
    (v : κ → H) (c x : ι → ℝ) (y : κ → ℝ) :
    ‖Fintype.linearCombination ℝ u c + Fintype.linearCombination ℝ u x +
        Fintype.linearCombination ℝ (screened hu v) y‖ ^ 2 -
      ‖Fintype.linearCombination ℝ u c‖ ^ 2 =
        2 * (∑ i, c i * gram u x i) +
          (∑ i, x i * gram u x i) +
          (∑ j, y j * gram (screened hu v) y j) := by
  rw [norm_add_sq_real, inner_add_left,
    synthesis_screened_orthogonal, synthesis_screened_orthogonal,
    norm_add_sq_real, inner_synthesis_left, gram_quadratic, gram_quadratic]
  rw [gram_quadratic]
  simp only [gram, LinearMap.coe_mk, AddHom.coe_mk]
  ring

end RiemannResearch.Analysis.FiniteScreenedCollocation
