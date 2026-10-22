/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The scaled surjectivity criterion

Exact declaration extracted from upstream `Spectra/Operator/KatoRellich.lean`.
The declaration name, all hypotheses, conclusion, and proof are preserved.
See `../PROVENANCE.md` for the pinned source and dependency-pruning details.
-/
open Complex Filter InnerProductSpace

namespace Spectra.Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **von Neumann's criterion at height `μ`.**  A densely defined symmetric
operator `B` with `ran (B + iμ) = ran (B − iμ) = H` is self-adjoint. -/
lemma isSelfAdjoint_of_surjective_addSub_smul
    (B : H →ₗ.[ℂ] H) (hsym : B.IsFormalAdjoint B)
    (hdense : Dense (B.domain : Set H)) (μ : ℝ)
    (hplus : ∀ φ : H, ∃ ψ : B.domain, B ψ + (I * (μ : ℂ)) • (ψ : H) = φ)
    (hminus : ∀ φ : H, ∃ ψ : B.domain, B ψ - (I * (μ : ℂ)) • (ψ : H) = φ) :
    IsSelfAdjoint B := by
  have hconj : (starRingEnd ℂ) (I * (μ : ℂ)) = -(I * (μ : ℂ)) := by
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ (hsym.le_adjoint hdense)
  -- ⊢ B† ≤ B.  First: ker(B† − iμ) = 0, using surjectivity of B + iμ.
  have hker : ∀ w : (B.adjoint).domain,
      B.adjoint w = (I * (μ : ℂ)) • (w : H) → (w : H) = 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hplus (w : H)        -- hv : B v + iμ•(v:H) = (w:H)
    have hadj : ⟪B.adjoint w, (v : H)⟫_ℂ = ⟪(w : H), B v⟫_ℂ :=
      LinearPMap.adjoint_isFormalAdjoint hdense w v
    rw [hw, inner_smul_left, hconj] at hadj
    -- hadj : -(iμ) * ⟪w,v⟫ = ⟪w, B v⟫
    have key : ⟪(w : H), B v⟫_ℂ + (I * (μ : ℂ)) * ⟪(w : H), (v : H)⟫_ℂ
        = ⟪(w : H), (w : H)⟫_ℂ := by
      rw [← inner_smul_right, ← inner_add_right, hv]
    have hww : ⟪(w : H), (w : H)⟫_ℂ = 0 := by rw [← key, ← hadj]; ring
    exact inner_self_eq_zero.mp hww
  -- Now B† ≤ B via eqLocus.
  apply LinearPMap.le_of_eqLocus_ge
  intro w hw                                -- hw : w ∈ (B.adjoint).domain
  set W : (B.adjoint).domain := ⟨w, hw⟩ with hWdef
  obtain ⟨x, hx⟩ := hminus (B.adjoint W - (I * (μ : ℂ)) • (W : H))
  -- hx : B x - iμ•(x:H) = B† W - iμ•(W:H)
  have hxin : (x : H) ∈ (B.adjoint).domain := (hsym.le_adjoint hdense).1 x.2
  have hxeq : B.adjoint (⟨(x : H), hxin⟩ : (B.adjoint).domain) = B x :=
    ((hsym.le_adjoint hdense).2 (x := x) (y := ⟨(x : H), hxin⟩) rfl).symm
  set W' : (B.adjoint).domain := W - ⟨(x : H), hxin⟩ with hW'def
  have hW'val : (W' : H) = (W : H) - (x : H) := rfl
  have hrearr : B.adjoint W - B x
      = (I * (μ : ℂ)) • (W : H) - (I * (μ : ℂ)) • (x : H) := by
    have h2 : B.adjoint W
        = B x - (I * (μ : ℂ)) • (x : H) + (I * (μ : ℂ)) • (W : H) := by
      rw [hx]; abel
    rw [h2]; abel
  have hAW' : B.adjoint W' = (I * (μ : ℂ)) • (W' : H) := by
    have e1 : B.adjoint W' = B.adjoint W - B x := by
      rw [hW'def, LinearPMap.map_sub, hxeq]
    rw [e1, hrearr, hW'val, smul_sub]
  have hWx : (W : H) = (x : H) := sub_eq_zero.mp (hW'val ▸ hker W' hAW')
  have hwx : w = (x : H) := by
    have hWcoe : (W : H) = w := by rw [hWdef]
    rw [← hWcoe]; exact hWx
  subst hwx
  exact ⟨hw, x.2, hxeq⟩

end Spectra.Operator
