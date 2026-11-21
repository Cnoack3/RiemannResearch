import RiemannResearch.RH.MixedConductorPrimeSupport
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Connecting maps between successive prime-support sequences

Compute the module snake boundary of two consecutive split support rows. We
identify the cokernel of the left vertical inclusion with the upper layer by
its orthogonal quotient map. For the natural inclusions the boundary is the
identity. A comparison that carries the chosen upper section to zero has zero
boundary. These statements use the sign convention of Mathlib.Algebra.Module.SnakeLemma
(Stacks Project, Tag 07JV, https://stacks.math.columbia.edu/tag/07JV).
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

/-- Inclusion into the next closed support stage. -/
abbrev supportStageInclusion (k : ℕ) : supportSpace k →ₗ[ℝ] supportSpace (k + 1) :=
  Submodule.inclusion (supportSpace_mono (Nat.le_succ k))

/-- Projection back onto the preceding closed stage. -/
abbrev supportStageRetraction (k : ℕ) : supportSpace (k + 1) →ₗ[ℝ] supportSpace k :=
  (supportSpace k).orthogonalProjectionOnto.toLinearMap.comp (supportSpace (k + 1)).subtype

/-- The layer projection realizes the quotient by the previous stage. -/
abbrev supportLayerQuotient (k : ℕ) : supportSpace (k + 1) →ₗ[ℝ] supportLayer k :=
  (supportLayer k).orthogonalProjectionOnto.toLinearMap.comp (supportSpace (k + 1)).subtype

/-- Orthogonal section of the layer quotient. -/
abbrev supportLayerSection (k : ℕ) : supportLayer k →ₗ[ℝ] supportSpace (k + 1) :=
  Submodule.inclusion (show supportLayer k ≤ supportSpace (k + 1) from inf_le_left)

private theorem quotient_inclusion (k : ℕ) (x : supportSpace k) :
    supportLayerQuotient k (supportStageInclusion k x) = 0 := by
  apply Subtype.ext
  change (supportLayer k).starProjection (x : mixedClosure) = 0
  rw [supportLayer_projection,
    Submodule.starProjection_eq_self_iff.mpr (supportSpace_mono (Nat.le_succ k) x.property),
    Submodule.starProjection_mem_subspace_eq_self, sub_self]

private theorem layerRow_exact (k : ℕ) :
    Function.Exact (supportStageInclusion k) (supportLayerQuotient k) := by
  intro x
  constructor
  · intro hx
    have h := congrArg Subtype.val hx
    change (supportLayer k).starProjection (x : mixedClosure) = 0 at h
    rw [supportLayer_projection, Submodule.starProjection_mem_subspace_eq_self, sub_eq_zero] at h
    have hx' : (x : mixedClosure) ∈ supportSpace k := Submodule.starProjection_eq_self_iff.mp h.symm
    exact ⟨⟨x.val, hx'⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact quotient_inclusion k y

private theorem quotient_section (k : ℕ) (x : supportLayer k) :
    supportLayerQuotient k (supportLayerSection k x) = x :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x

private theorem retraction_inclusion (k : ℕ) (x : supportSpace k) :
    supportStageRetraction k (supportStageInclusion k x) = x :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x

private theorem comparison_left_square (k : ℕ)
    (T : supportSpace (k + 1) →ₗ[ℝ] supportSpace (k + 1))
    (hT : ∀ x : supportSpace k, T (supportStageInclusion k x) = supportStageInclusion k x) :
    (supportStageInclusion (k + 1)).comp (supportStageInclusion k) =
      ((supportStageInclusion (k + 1)).comp T).comp (supportStageInclusion k) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, hT]

private theorem comparison_right_square (k : ℕ)
    (T : supportSpace (k + 1) →ₗ[ℝ] supportSpace (k + 1)) :
    (supportLayerQuotient (k + 1)).comp ((supportStageInclusion (k + 1)).comp T) =
      (0 : supportLayer k →ₗ[ℝ] supportLayer (k + 1)).comp (supportLayerQuotient k) := by
  apply LinearMap.ext
  intro x
  exact quotient_inclusion (k + 1) (T x)

private theorem zero_right_exact (k : ℕ) :
    Function.Exact (LinearMap.id : supportLayer k →ₗ[ℝ] supportLayer k)
      (0 : supportLayer k →ₗ[ℝ] supportLayer (k + 1)) :=
  (LinearMap.exact_zero_iff_surjective _ _).mpr Function.surjective_id

/-- Compare the rows at k and k+1. The left vertical map is inclusion, the
right one is zero, and the middle one sends x to the inclusion of T x.
The upper layer represents both the kernel on the right and the cokernel on the left. -/
def supportComparisonBoundary (k : ℕ) (T : supportSpace (k + 1) →ₗ[ℝ] supportSpace (k + 1))
    (hT : ∀ x : supportSpace k, T (supportStageInclusion k x) = supportStageInclusion k x) :
    supportLayer k →ₗ[ℝ] supportLayer k :=
  SnakeLemma.δ (supportStageInclusion k) ((supportStageInclusion (k + 1)).comp T)
    (0 : supportLayer k →ₗ[ℝ] supportLayer (k + 1))
    (supportStageInclusion k) (supportLayerQuotient k) (layerRow_exact k)
    (supportStageInclusion (k + 1)) (supportLayerQuotient (k + 1)) (layerRow_exact (k + 1))
    (comparison_left_square k T hT) (comparison_right_square k T)
    (supportLayerSection k) (funext (quotient_section k))
    (supportStageRetraction (k + 1)) (funext (retraction_inclusion (k + 1)))
    LinearMap.id (zero_right_exact k)
    (supportLayerQuotient k) (layerRow_exact k)

theorem supportComparisonBoundary_apply (k : ℕ)
    (T : supportSpace (k + 1) →ₗ[ℝ] supportSpace (k + 1)) (hT) (x : supportLayer k) :
    supportComparisonBoundary k T hT x = supportLayerQuotient k (T (supportLayerSection k x)) := by
  change supportLayerQuotient k
    (supportStageRetraction (k + 1) (supportStageInclusion (k + 1) _)) = _
  rw [retraction_inclusion, LinearMap.id_apply]

/-- This right-hand vertical map is zero. Compatibility of sections therefore
sends each upper section vector to zero and kills the boundary. -/
theorem supportComparisonBoundary_eq_zero_of_compatible (k : ℕ)
    (T : supportSpace (k + 1) →ₗ[ℝ] supportSpace (k + 1)) (hT)
    (h : ∀ x : supportLayer k, T (supportLayerSection k x) = 0) :
    supportComparisonBoundary k T hT = 0 := by
  apply LinearMap.ext
  intro x
  rw [supportComparisonBoundary_apply, h, map_zero, LinearMap.zero_apply]

/-- Truncating to the old stage before including into the next row respects the sections. -/
theorem truncatedLayerBoundary_eq_zero (k : ℕ) :
    supportComparisonBoundary k ((supportStageInclusion k).comp (supportStageRetraction k))
      (fun x => congrArg (supportStageInclusion k) (retraction_inclusion k x)) = 0 := by
  apply supportComparisonBoundary_eq_zero_of_compatible
  intro x
  change supportStageInclusion k ((supportSpace k).orthogonalProjectionOnto (x : mixedClosure)) = 0
  rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal x.property.2, map_zero]

/-- For the actual inclusion of consecutive filtration rows, the snake map is the identity. -/
theorem successiveLayerBoundary_eq_id (k : ℕ) :
    supportComparisonBoundary k LinearMap.id (fun _ => rfl) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact (supportComparisonBoundary_apply k _ _ x).trans (quotient_section k x)

theorem successiveLayerBoundary_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    supportComparisonBoundary k LinearMap.id (fun _ => rfl) ≠ 0 := by
  rw [successiveLayerBoundary_eq_id]
  intro h
  apply supportLayer_ne_bot k hk
  apply bot_unique
  intro m hm
  have he := DFunLike.congr_fun h (⟨m, hm⟩ : supportLayer k)
  exact (Submodule.mem_bot ℝ).mpr (congrArg Subtype.val he)

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
