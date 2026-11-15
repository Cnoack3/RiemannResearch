import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Operator variance of an orthogonal compression

Source: Christian Noack's variance observation, 15 November 2026.
The terminology and positivity principle are the compression case of
R. V. Kadison, "A generalized Schwarz inequality and algebraic invariants for
operator algebras", Ann. of Math. 56 (1952), 494-503, Theorem 1.
See also R. Sharma and A. Thakur, "More inequalities for positive linear maps",
J. Math. Inequal. 7 (2013), 1-9, equation (1.1), doi:10.7153/jmi-07-01.
These references support the terminology and general perspective.
The proofs below use orthogonal projection and the Hilbert-space adjoint directly.

The concrete RH consumer is QDensityCouplingVariance: its V is the actual
full-conductor closure and its T is the density multiplier B = dQ/dP.
The existing CompressionProductDefect file proves ambient ring identities;
here compression and leakage have their actual subspace domains and codomains.

All energy decompositions are exact. Vanishing is proved equivalent to invariance;
neither positivity nor compactness is used to assert that the variance vanishes.
-/

noncomputable section
namespace Submodule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (V : Submodule ℝ H) [CompleteSpace V]
/-- Compress an operator to the closed subspace. -/
def operatorCompression (T : H →L[ℝ] H) : V →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp (T.comp V.subtypeL)
/-- The orthogonal component of the image that leaves the subspace. -/
def operatorLeakage (T : H →L[ℝ] H) : V →L[ℝ] Vᗮ :=
  Vᗮ.orthogonalProjectionOnto.comp (T.comp V.subtypeL)
omit [CompleteSpace H] in
/-- Exact ambient-vector formula for the leakage. -/
theorem operatorLeakage_coe (T : H →L[ℝ] H) (v : V) :
    (V.operatorLeakage T v : H) = T (v : H) - V.starProjection (T v) :=
  V.starProjection_orthogonal_val (T v)
/-- The reverse off-diagonal block is the adjoint for a symmetric operator. -/
theorem operatorLeakage_adjoint_of_symmetric (T : H →L[ℝ] H)
    (hT : ∀ x y : H, inner ℝ (T x) y = inner ℝ x (T y)) :
    (V.operatorLeakage T).adjoint =
      V.orthogonalProjectionOnto.comp (T.comp Vᗮ.subtypeL) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro w v
  change inner ℝ (V.orthogonalProjectionOnto (T (w : H))) v =
    inner ℝ w (Vᗮ.orthogonalProjectionOnto (T (v : H)))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact hT _ _
/-- Operator-valued variance, represented as the complete leakage Gram operator. -/
def compressionVariance (T : H →L[ℝ] H) : V →L[ℝ] V :=
  (V.operatorLeakage T).adjoint.comp (V.operatorLeakage T)
/-- For a symmetric operator this is compressed second moment minus squared first moment. -/
theorem compressionVariance_eq_square_defect (T : H →L[ℝ] H)
    (hT : ∀ x y : H, inner ℝ (T x) y = inner ℝ x (T y)) :
    V.compressionVariance T =
      V.operatorCompression (T.comp T) -
        (V.operatorCompression T).comp (V.operatorCompression T) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [compressionVariance, operatorLeakage_adjoint_of_symmetric V T hT,
    ContinuousLinearMap.comp_apply, sub_apply]
  change V.orthogonalProjectionOnto (T (V.operatorLeakage T v : H)) =
    V.orthogonalProjectionOnto (T (T (v : H))) -
      V.orthogonalProjectionOnto (T (V.starProjection (T (v : H))))
  rw [operatorLeakage_coe, map_sub, map_sub]

/-- Polarized variance: all mixed leakage pairings are retained. -/
theorem compressionVariance_inner (T : H →L[ℝ] H) (v u : V) :
    inner ℝ (V.compressionVariance T v) u =
      inner ℝ (V.operatorLeakage T v) (V.operatorLeakage T u) := by
  exact ContinuousLinearMap.adjoint_inner_left (V.operatorLeakage T) u
    (V.operatorLeakage T v)

/-- A variance quadratic form is the squared norm of the omitted component. -/
theorem compressionVariance_quadratic (T : H →L[ℝ] H) (v : V) :
    inner ℝ (V.compressionVariance T v) v = ‖V.operatorLeakage T v‖ ^ 2 := by
  rw [compressionVariance_inner, real_inner_self_eq_norm_sq]

/-- The compression case of the Kadison inequality, proved directly. -/
theorem compressionVariance_nonneg (T : H →L[ℝ] H) (v : V) :
    0 ≤ inner ℝ (V.compressionVariance T v) v := by
  rw [compressionVariance_quadratic]
  exact sq_nonneg _

/-- Operator variance is self-adjoint, even when the original operator is not. -/
theorem compressionVariance_self_adjoint (T : H →L[ℝ] H) :
    (V.compressionVariance T).adjoint = V.compressionVariance T := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v u
  rw [compressionVariance_inner]
  exact (ContinuousLinearMap.adjoint_inner_right (V.operatorLeakage T) v
    (V.operatorLeakage T u)).symm

omit [CompleteSpace H] in
/-- Pointwise zero leakage is membership of the complete image in the subspace. -/
theorem operatorLeakage_eq_zero_iff (T : H →L[ℝ] H) (v : V) :
    V.operatorLeakage T v = 0 ↔ T (v : H) ∈ V := by
  change Vᗮ.orthogonalProjectionOnto (T (v : H)) = 0 ↔ _
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, V.orthogonal_orthogonal]

/-- The variance kernel consists exactly of vectors whose images stay in the subspace. -/
theorem compressionVariance_apply_eq_zero_iff (T : H →L[ℝ] H) (v : V) :
    V.compressionVariance T v = 0 ↔ T (v : H) ∈ V := by
  rw [← operatorLeakage_eq_zero_iff]
  constructor
  · intro h
    have he := V.compressionVariance_quadratic T v
    rw [h, inner_zero_left] at he
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (V.operatorLeakage T v)]
  · intro h
    change (V.operatorLeakage T).adjoint (V.operatorLeakage T v) = 0
    rw [h, map_zero]

/-- Global zero variance is exactly subspace invariance. -/
theorem compressionVariance_zero_iff_invariant (T : H →L[ℝ] H) :
    V.compressionVariance T = 0 ↔ ∀ x ∈ V, T x ∈ V := by
  constructor
  · intro h x hx
    apply (V.compressionVariance_apply_eq_zero_iff T ⟨x, hx⟩).mp
    rw [h]
    rfl
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    exact (V.compressionVariance_apply_eq_zero_iff T v).mpr (h v v.property)

omit [CompleteSpace H] in
/-- Exact least-squares identity for every approximant in the subspace. -/
theorem operatorCompression_best_approximation (T : H →L[ℝ] H) (v u : V) :
    ‖T (v : H) - (u : H)‖ ^ 2 =
      ‖V.operatorLeakage T v‖ ^ 2 + ‖V.operatorCompression T v - u‖ ^ 2 := by
  have horth : inner ℝ
      ((V.operatorCompression T v : H) - (u : H))
      (V.operatorLeakage T v : H) = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (V.sub_mem (V.operatorCompression T v).property u.property)
      (V.operatorLeakage T v).property
  have he : T (v : H) - (u : H) =
      ((V.operatorCompression T v : H) - (u : H)) +
        (V.operatorLeakage T v : H) := by
    rw [operatorLeakage_coe]
    change T (v : H) - (u : H) =
      (V.starProjection (T (v : H)) - (u : H)) +
        (T (v : H) - V.starProjection (T (v : H)))
    abel
  rw [he, norm_add_sq_real, horth]
  change _ = ‖(V.operatorLeakage T v : H)‖ ^ 2 +
    ‖((V.operatorCompression T v : H) - (u : H))‖ ^ 2
  ring

/-- Total centered energy splits into leakage variance and retained centered energy. -/
theorem compressionVariance_total (T : H →L[ℝ] H) (v : V) (μ : ℝ) :
    ‖T (v : H) - μ • (v : H)‖ ^ 2 =
      inner ℝ (V.compressionVariance T v) v +
        ‖V.operatorCompression T v - μ • v‖ ^ 2 := by
  rw [compressionVariance_quadratic]
  exact V.operatorCompression_best_approximation T v (μ • v)

/-- Every scalar centering gives an upper bound on the leakage variance. -/
theorem compressionVariance_le_centered_energy (T : H →L[ℝ] H) (v : V) (μ : ℝ) :
    inner ℝ (V.compressionVariance T v) v ≤
      ‖T (v : H) - μ • (v : H)‖ ^ 2 := by
  rw [compressionVariance_total]
  exact le_add_of_nonneg_right (sq_nonneg _)

omit [CompleteSpace H] in
/-- Adding a scalar identity creates no leakage; scaling scales the leakage. -/
theorem operatorLeakage_affine (T : H →L[ℝ] H) (a b : ℝ) :
    V.operatorLeakage (a • T + b • ContinuousLinearMap.id ℝ H) =
      a • V.operatorLeakage T := by
  apply ContinuousLinearMap.ext
  intro v
  change Vᗮ.orthogonalProjectionOnto (a • T (v : H) + b • (v : H)) =
    a • Vᗮ.orthogonalProjectionOnto (T (v : H))
  have hv : (v : H) ∈ Vᗮᗮ := by
    rw [V.orthogonal_orthogonal]
    exact v.property
  rw [map_add, map_smul, map_smul,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv, smul_zero, add_zero]

/-- Variance scales quadratically and is unchanged by scalar translation. -/
theorem compressionVariance_affine_quadratic (T : H →L[ℝ] H)
    (a b : ℝ) (v : V) :
    inner ℝ (V.compressionVariance (a • T + b • ContinuousLinearMap.id ℝ H) v) v =
      a ^ 2 * inner ℝ (V.compressionVariance T v) v := by
  rw [compressionVariance_quadratic, operatorLeakage_affine,
    compressionVariance_quadratic]
  change ‖a • V.operatorLeakage T v‖ ^ 2 = a ^ 2 * _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

end Submodule
