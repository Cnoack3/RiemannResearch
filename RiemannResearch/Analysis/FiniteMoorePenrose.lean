import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith

/-!
# Moore–Penrose inverse in a finite real inner-product space

Source: the user-provided categorical CRT and energy note (14 November 2026),
Theorem E1. This module constructs the inverse from orthogonal projections,
proves linearity and all four Penrose identities, and is used for singular
finite Gram reconstruction in the Pareto-energy research program.
-/

noncomputable section
namespace LinearMap

/-- The Moore–Penrose action of a finite-dimensional endomorphism, constructed
by first projecting the target onto the range and then selecting the unique
preimage orthogonal to the kernel. No invertibility hypothesis is needed. -/
def orthogonalGeneralizedInverse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) : E :=
  (LinearMap.ker T)ᗮ.starProjection
    (Classical.choose ((LinearMap.range T).starProjection_apply_mem b))

theorem orthogonalGeneralizedInverse_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) :
    orthogonalGeneralizedInverse T b ∈ (LinearMap.ker T)ᗮ :=
  (LinearMap.ker T)ᗮ.starProjection_apply_mem _

theorem orthogonalGeneralizedInverse_normal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) :
    T (orthogonalGeneralizedInverse T b) =
      (LinearMap.range T).starProjection b := by
  let a : E := Classical.choose ((LinearMap.range T).starProjection_apply_mem b)
  have ha : T a = (LinearMap.range T).starProjection b :=
    Classical.choose_spec ((LinearMap.range T).starProjection_apply_mem b)
  have hd : a - (LinearMap.ker T)ᗮ.starProjection a ∈
      (LinearMap.ker T)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [real_inner_comm]
    exact Submodule.starProjection_inner_eq_zero a y hy
  rw [Submodule.orthogonal_orthogonal] at hd
  change T (a - (LinearMap.ker T)ᗮ.starProjection a) = 0 at hd
  rw [map_sub] at hd
  change T ((LinearMap.ker T)ᗮ.starProjection a) = _
  exact (sub_eq_zero.mp hd).symm.trans ha

theorem orthogonalGeneralizedInverse_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b x : E)
    (hx : x ∈ (LinearMap.ker T)ᗮ)
    (hTx : T x = (LinearMap.range T).starProjection b) :
    x = orthogonalGeneralizedInverse T b := by
  have hd : x - orthogonalGeneralizedInverse T b ∈ LinearMap.ker T := by
    change T (x - orthogonalGeneralizedInverse T b) = 0
    rw [map_sub, hTx, orthogonalGeneralizedInverse_normal, sub_self]
  have ho := (LinearMap.ker T)ᗮ.sub_mem hx
    (orthogonalGeneralizedInverse_mem T b)
  have hi := (Submodule.mem_orthogonal (LinearMap.ker T) _).mp ho _ hd
  rw [real_inner_self_eq_norm_sq] at hi
  have hz : x - orthogonalGeneralizedInverse T b = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (x - orthogonalGeneralizedInverse T b)]
  exact sub_eq_zero.mp hz


/-- The characterized generalized inverse is linear: both the range projection
and the unique kernel-orthogonal preimage respect the vector operations. -/
def moorePenrose
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) : E →ₗ[ℝ] E where
  toFun := orthogonalGeneralizedInverse T
  map_add' b c := by
    symm
    apply orthogonalGeneralizedInverse_unique
    · exact (LinearMap.ker T)ᗮ.add_mem
        (orthogonalGeneralizedInverse_mem T b) (orthogonalGeneralizedInverse_mem T c)
    · rw [map_add, orthogonalGeneralizedInverse_normal,
        orthogonalGeneralizedInverse_normal, map_add]
  map_smul' a b := by
    symm
    apply orthogonalGeneralizedInverse_unique
    · exact (LinearMap.ker T)ᗮ.smul_mem a (orthogonalGeneralizedInverse_mem T b)
    · rw [map_smul, orthogonalGeneralizedInverse_normal, map_smul]
      rfl

theorem moorePenrose_normal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) :
    T (moorePenrose T b) = (LinearMap.range T).starProjection b :=
  orthogonalGeneralizedInverse_normal T b

theorem moorePenrose_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) :
    moorePenrose T b ∈ (LinearMap.ker T)ᗮ :=
  orthogonalGeneralizedInverse_mem T b

theorem moorePenrose_apply_map
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) :
    moorePenrose T (T b) = (LinearMap.ker T)ᗮ.starProjection b := by
  symm
  apply orthogonalGeneralizedInverse_unique
  · exact (LinearMap.ker T)ᗮ.starProjection_apply_mem b
  · have hd := Submodule.sub_starProjection_mem_orthogonal
        (K := (LinearMap.ker T)ᗮ) b
    rw [Submodule.orthogonal_orthogonal] at hd
    change T (b - (LinearMap.ker T)ᗮ.starProjection b) = 0 at hd
    rw [map_sub] at hd
    rw [Submodule.starProjection_eq_self_iff.mpr (show T b ∈ LinearMap.range T from ⟨b, rfl⟩)]
    exact (sub_eq_zero.mp hd).symm

/-- First Penrose identity, pointwise. -/
theorem map_moorePenrose_map
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) :
    T (moorePenrose T (T b)) = T b := by
  rw [moorePenrose_normal]
  exact Submodule.starProjection_eq_self_iff.mpr ⟨b, rfl⟩

/-- Second Penrose identity, pointwise. -/
theorem moorePenrose_map_moorePenrose
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (b : E) :
    moorePenrose T (T (moorePenrose T b)) = moorePenrose T b := by
  rw [moorePenrose_apply_map]
  exact Submodule.starProjection_eq_self_iff.mpr (moorePenrose_mem T b)

private theorem projection_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x y : E) :
    inner ℝ (K.starProjection x) y = inner ℝ x (K.starProjection y) := by
  have hx := Submodule.starProjection_inner_eq_zero x
    (K.starProjection y) (K.starProjection_apply_mem y)
  have hy := Submodule.starProjection_inner_eq_zero y
    (K.starProjection x) (K.starProjection_apply_mem x)
  rw [inner_sub_left] at hx hy
  have h₁ := real_inner_comm y (K.starProjection x)
  have h₂ := real_inner_comm (K.starProjection y) (K.starProjection x)
  linarith

/-- Third Penrose identity: the range composite is self-adjoint. -/
theorem map_moorePenrose_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (x y : E) :
    inner ℝ (T (moorePenrose T x)) y = inner ℝ x (T (moorePenrose T y)) := by
  rw [moorePenrose_normal, moorePenrose_normal]
  exact projection_symmetric _ x y

/-- Fourth Penrose identity: the source composite is self-adjoint. -/
theorem moorePenrose_map_symmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (x y : E) :
    inner ℝ (moorePenrose T (T x)) y = inner ℝ x (moorePenrose T (T y)) := by
  rw [moorePenrose_apply_map, moorePenrose_apply_map]
  exact projection_symmetric _ x y

end LinearMap
