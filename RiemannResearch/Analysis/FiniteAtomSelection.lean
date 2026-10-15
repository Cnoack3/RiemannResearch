/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.NestedProjectionEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Literal finite selections of Hilbert-space atoms

Source: user-provided legal-conductor subset question, 14 October 2026.
A selected span contains only the chosen atoms. Its finite dimensionality
supplies an actual orthogonal projection, including for an empty selection.
The concrete full and squarefree Q dictionaries are supplied separately.
-/

noncomputable section

namespace RiemannResearch.Analysis.FiniteAtomSelection
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
def selectedSpan (v : ι → H) (J : Finset ι) : Submodule ℝ H :=
  Submodule.span ℝ (v '' (J : Set ι))
instance selectedSpan_finiteDimensional (v : ι → H) (J : Finset ι) :
    FiniteDimensional ℝ (selectedSpan v J) :=
  FiniteDimensional.span_of_finite ℝ (J.finite_toSet.image v)

theorem selectedSpan_le (v : ι → H) (J : Finset ι)
    (V : Submodule ℝ H) (hv : ∀ i ∈ J, v i ∈ V) : selectedSpan v J ≤ V := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  exact hv i hi

theorem selectedSpan_mono (v : ι → H) {I J : Finset ι} (hIJ : I ⊆ J) :
    selectedSpan v I ≤ selectedSpan v J :=
  Submodule.span_mono (Set.image_mono hIJ)

@[simp] theorem selectedSpan_empty (v : ι → H) : selectedSpan v ∅ = ⊥ := by
  simp [selectedSpan]

theorem selected_trial_error (v : ι → H) (J : Finset ι)
    (V : Submodule ℝ H) [V.HasOrthogonalProjection]
    (hv : ∀ i ∈ J, v i ∈ V) (x : H) :
    ‖x - (selectedSpan v J).starProjection x‖ ^ 2 =
      ‖x - V.starProjection x‖ ^ 2 +
        ‖V.starProjection x - (selectedSpan v J).starProjection x‖ ^ 2 :=
  NestedProjectionEnergy.residual_energy_eq_add_gap (selectedSpan_le v J V hv) x
end RiemannResearch.Analysis.FiniteAtomSelection
