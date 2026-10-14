/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Invariance of an atom span under nonzero coordinate weights

Source: elementary module algebra, used for the user's zero-phase proposal
on 14 October 2026. The Q legal projection consumer is QLegalResidueDPP.
The lemma applies over every division ring, in particular over R and C.
-/

namespace RiemannResearch.Analysis.AtomSpanReweighting

/-- Every atom may be multiplied by its own nonzero scalar without changing the span. -/
theorem span_range_smul_eq {𝕜 H ι : Type*} [DivisionRing 𝕜]
    [AddCommGroup H] [Module 𝕜 H] (v : ι → H) (a : ι → 𝕜)
    (ha : ∀ i, a i ≠ 0) :
    Submodule.span 𝕜 (Set.range (fun i => a i • v i)) =
      Submodule.span 𝕜 (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    change v i ∈ Submodule.span 𝕜 (Set.range (fun i => a i • v i))
    have h := Submodule.smul_mem
      (Submodule.span 𝕜 (Set.range (fun i => a i • v i)))
      (a i)⁻¹ (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [smul_smul, inv_mul_cancel₀ (ha i), one_smul] using h

end RiemannResearch.Analysis.AtomSpanReweighting
