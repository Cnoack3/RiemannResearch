/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic.Abel

/-!
# The range of an off-axis operator shift

Exact declaration extracted from upstream `Spectra/Resolvent/Range/Surjectivity.lean`.
The declaration name, carrier, and submodule closure proofs are preserved.
See `../PROVENANCE.md` for the pinned source and dependency-pruning details.
-/
open Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Spectra.Resolvent

/-- The range of (A - zI) forms a submodule. -/
def rangeSubmodule {A : H →ₗ.[ℂ] H} (z : ℂ) : Submodule ℂ H where
  carrier := Set.range (fun (ψ : A.domain) => A ψ - z • (ψ : H))
  add_mem' := by
    intro a b ha hb
    obtain ⟨ψa, hψa⟩ := ha
    obtain ⟨ψb, hψb⟩ := hb
    refine ⟨⟨(ψa : H) + (ψb : H), A.domain.add_mem ψa.property ψb.property⟩, ?_⟩
    have op_add : A ⟨(ψa : H) + (ψb : H), A.domain.add_mem ψa.property ψb.property⟩
        = A ψa + A ψb := A.map_add ψa ψb
    simp only [← hψa, ← hψb]
    calc A ⟨(ψa : H) + (ψb : H), _⟩ - z • ((ψa : H) + (ψb : H))
        = (A ψa + A ψb) - z • ((ψa : H) + (ψb : H)) := by rw [op_add]
      _ = (A ψa + A ψb) - (z • (ψa : H) + z • (ψb : H)) := by rw [smul_add]
      _ = (A ψa - z • (ψa : H)) + (A ψb - z • (ψb : H)) := by abel
  zero_mem' := ⟨⟨0, A.domain.zero_mem⟩, by simp only [smul_zero, sub_zero]; exact A.map_zero⟩
  smul_mem' := by
    intro c a ha
    obtain ⟨ψ, hψ⟩ := ha
    refine ⟨⟨c • (ψ : H), A.domain.smul_mem c ψ.property⟩, ?_⟩
    have op_smul : A ⟨c • (ψ : H), A.domain.smul_mem c ψ.property⟩ = c • A ψ := A.map_smul c ψ
    simp only [← hψ]
    calc A ⟨c • (ψ : H), _⟩ - z • (c • (ψ : H))
        = c • A ψ - z • (c • (ψ : H)) := by rw [op_smul]
      _ = c • A ψ - c • (z • (ψ : H)) := by rw [smul_comm z c]
      _ = c • (A ψ - z • (ψ : H)) := by rw [smul_sub]

end Spectra.Resolvent
