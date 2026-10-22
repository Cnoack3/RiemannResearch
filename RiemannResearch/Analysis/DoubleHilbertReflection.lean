import RiemannResearch.Analysis.ReflectedProjection
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A concrete Hilbert-space realization of reflected projection completion

Source: user-provided reciprocal Mellin construction (2026-09-20).

The two copies use the Hilbert product norm. Reflection swaps the coordinates;
the original projection occupies the first coordinate. Thus the key condition
`P * J * P = 0` is proved, not assumed. The projection onto the original closed
legal space is the existing `Submodule.starProjection`.
-/

noncomputable section

namespace RiemannResearch.Analysis.DoubleHilbertReflection

abbrev DoubleHilbert (H : Type*) := WithLp 2 (H × H)

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

def coordinates : DoubleHilbert H ≃L[𝕜] H × H :=
  WithLp.prodContinuousLinearEquiv 2 𝕜 H H

def transport (T : (H × H) →L[𝕜] H × H) :
    DoubleHilbert H →L[𝕜] DoubleHilbert H :=
  (coordinates (𝕜 := 𝕜) (H := H)).symm.toContinuousLinearMap.comp
    (T.comp (coordinates (𝕜 := 𝕜) (H := H)).toContinuousLinearMap)

@[simp] theorem transport_apply (T : (H × H) →L[𝕜] H × H) (x : DoubleHilbert H) :
    transport T x = WithLp.toLp 2 (T x.ofLp) := rfl

def reflection : DoubleHilbert H →L[𝕜] DoubleHilbert H :=
  transport (ContinuousLinearEquiv.prodComm 𝕜 H H).toContinuousLinearMap

@[simp] theorem reflection_apply (x : DoubleHilbert H) :
    reflection (𝕜 := 𝕜) x = WithLp.toLp 2 (x.ofLp.2, x.ofLp.1) := rfl

theorem reflection_reflection (x : DoubleHilbert H) :
    reflection (𝕜 := 𝕜) (reflection (𝕜 := 𝕜) x) = x := by
  apply WithLp.ofLp_injective 2
  rfl

theorem reflection_sq :
    reflection (𝕜 := 𝕜) (H := H) * reflection = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact reflection_reflection x

theorem reflection_inner (x y : DoubleHilbert H) :
    inner 𝕜 (reflection (𝕜 := 𝕜) x) (reflection (𝕜 := 𝕜) y) = inner 𝕜 x y := by
  simp only [WithLp.prod_inner_apply, reflection_apply, WithLp.ofLp_toLp]
  exact add_comm _ _

theorem reflection_inner_left_eq_right (x y : DoubleHilbert H) :
    inner 𝕜 (reflection (𝕜 := 𝕜) x) y = inner 𝕜 x (reflection (𝕜 := 𝕜) y) := by
  simp only [WithLp.prod_inner_apply, reflection_apply, WithLp.ofLp_toLp]
  exact add_comm _ _

variable (S : Submodule 𝕜 H) [S.HasOrthogonalProjection]

def leftProjection : DoubleHilbert H →L[𝕜] DoubleHilbert H :=
  transport (S.starProjection.prodMap (0 : H →L[𝕜] H))

def rightProjection : DoubleHilbert H →L[𝕜] DoubleHilbert H :=
  transport ((0 : H →L[𝕜] H).prodMap S.starProjection)

@[simp] theorem leftProjection_apply (x : DoubleHilbert H) :
    leftProjection S x = WithLp.toLp 2 (S.starProjection x.ofLp.1, (0 : H)) := rfl

@[simp] theorem rightProjection_apply (x : DoubleHilbert H) :
    rightProjection S x = WithLp.toLp 2 ((0 : H), S.starProjection x.ofLp.2) := rfl

theorem leftProjection_sq : leftProjection S * leftProjection S = leftProjection S := by
  apply ContinuousLinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  change (S.starProjection (S.starProjection x.ofLp.1), (0 : H)) =
    (S.starProjection x.ofLp.1, (0 : H))
  exact Prod.ext
    (Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x.ofLp.1)) rfl

/-- The support-separation hypothesis of reflected completion holds concretely. -/
theorem leftProjection_reflection_leftProjection :
    leftProjection S * reflection (𝕜 := 𝕜) * leftProjection S = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  change (S.starProjection (0 : H), (0 : H)) = ((0 : H), (0 : H))
  simp

theorem conjugate_leftProjection :
    reflection (𝕜 := 𝕜) * leftProjection S * reflection = rightProjection S := by
  apply ContinuousLinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

theorem inner_left_right_zero (x y : DoubleHilbert H) :
    inner 𝕜 (leftProjection S x) (rightProjection S y) = 0 := by
  simp [WithLp.prod_inner_apply]

theorem leftProjection_inner_left_eq_right (x y : DoubleHilbert H) :
    inner 𝕜 (leftProjection S x) y = inner 𝕜 x (leftProjection S y) := by
  simpa only [WithLp.prod_inner_apply, leftProjection_apply, WithLp.ofLp_toLp,
    inner_zero_left, inner_zero_right, add_zero] using
    S.inner_starProjection_left_eq_right x.ofLp.1 y.ofLp.1

def completed : DoubleHilbert H →L[𝕜] DoubleHilbert H :=
  ReflectedProjection.completion (leftProjection S) (reflection (𝕜 := 𝕜))

@[simp] theorem completed_apply (x : DoubleHilbert H) :
    completed S x =
      WithLp.toLp 2 (S.starProjection x.ofLp.1, S.starProjection x.ofLp.2) := by
  apply WithLp.ofLp_injective 2
  change (S.starProjection x.ofLp.1 + 0, 0 + S.starProjection x.ofLp.2) =
    (S.starProjection x.ofLp.1, S.starProjection x.ofLp.2)
  simp only [add_zero, zero_add]

theorem completed_sq : completed S * completed S = completed S :=
  ReflectedProjection.completion_idempotent _ _ (leftProjection_sq S)
    reflection_sq (leftProjection_reflection_leftProjection S)

theorem completed_commutes :
    completed S * reflection (𝕜 := 𝕜) = reflection * completed S :=
  ReflectedProjection.completion_commutes _ _ reflection_sq

/-- Completion preserves the full-space condition in the doubled relative ambient. -/
theorem completed_eq_one_iff : completed S = 1 ↔ S = ⊤ := by
  constructor
  · intro h
    apply le_antisymm le_top
    intro x _
    have hp := congrArg
      (fun T : DoubleHilbert H →L[𝕜] DoubleHilbert H =>
        (T (WithLp.toLp 2 (x, (0 : H)))).ofLp.1) h
    change (completed S (WithLp.toLp 2 (x, (0 : H)))).ofLp.1 = x at hp
    rw [completed_apply] at hp
    exact Submodule.starProjection_eq_self_iff.mp hp
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    rw [completed_apply]
    apply WithLp.ofLp_injective 2
    change (S.starProjection x.ofLp.1, S.starProjection x.ofLp.2) = x.ofLp
    have h₁ : S.starProjection x.ofLp.1 = x.ofLp.1 :=
      Submodule.starProjection_eq_self_iff.mpr (by rw [h]; trivial)
    have h₂ : S.starProjection x.ofLp.2 = x.ofLp.2 :=
      Submodule.starProjection_eq_self_iff.mpr (by rw [h]; trivial)
    rw [h₁, h₂]

section Complete
variable [CompleteSpace H]

theorem reflection_selfAdjoint :
    star (reflection (𝕜 := 𝕜) (H := H)) = reflection := by
  change IsSelfAdjoint (reflection (𝕜 := 𝕜) (H := H))
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact reflection_inner_left_eq_right x y

theorem leftProjection_selfAdjoint : star (leftProjection S) = leftProjection S := by
  change IsSelfAdjoint (leftProjection S)
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact leftProjection_inner_left_eq_right S x y

theorem completed_selfAdjoint : star (completed S) = completed S :=
  ReflectedProjection.completion_selfAdjoint _ _ (leftProjection_selfAdjoint S)
    reflection_selfAdjoint

theorem completed_isStarProjection : IsStarProjection (completed S) := by
  exact isStarProjection_iff'.mpr ⟨completed_sq S, completed_selfAdjoint S⟩

end Complete
end RiemannResearch.Analysis.DoubleHilbertReflection
