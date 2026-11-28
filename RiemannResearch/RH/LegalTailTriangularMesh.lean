/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailNymanMesh

/-!
# Finite triangular meshes at a common legal stage

Source: Christian Noack, November 2026. Row N consists of the parameters
a/b with 1 ≤ a < b ≤ N. A single physical stage N! realizes the whole row.
-/

noncomputable section
open Set
namespace RiemannResearch.RH.Burnol.ContinuousNyman

def triangularMeshRow (N : ℕ) : Finset ℝ := by
  classical
  exact (((Finset.range (N+1)) ×ˢ (Finset.range (N+1))).filter
    (fun p : ℕ × ℕ => 0 < p.1 ∧ p.1 < p.2)).image (fun p => (p.1 : ℝ) / p.2)

theorem mem_triangularMeshRow {N : ℕ} {x : ℝ} :
    x ∈ triangularMeshRow N ↔ ∃ a b : ℕ, 0 < a ∧ a < b ∧ b ≤ N ∧ x = (a : ℝ)/b := by
  classical
  simp only [triangularMeshRow, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨a,b⟩, ⟨⟨_,hb⟩,ha,hab⟩, rfl⟩
    exact ⟨a,b,ha,hab,by omega,rfl⟩
  · rintro ⟨a,b,ha,hab,hb,rfl⟩
    exact ⟨(a,b), ⟨⟨by dsimp; omega, by dsimp; omega⟩,ha,hab⟩,rfl⟩

theorem triangularMeshRow_mono : Monotone triangularMeshRow := by
  intro N M h x hx
  obtain ⟨a,b,ha,hab,hb,rfl⟩ := mem_triangularMeshRow.mp hx
  exact mem_triangularMeshRow.mpr ⟨a,b,ha,hab,hb.trans h,rfl⟩

theorem triangularMeshRow_subset_factorial (N : ℕ) :
    (↑(triangularMeshRow N) : Set ℝ) ⊆ scaleMeshParameters N.factorial := by
  intro x hx
  obtain ⟨a,b,ha,hab,hb,rfl⟩ := mem_triangularMeshRow.mp hx
  obtain ⟨q,hq⟩ := Nat.dvd_factorial ha (hab.le.trans hb)
  have hqpos : 0 < q := by
    by_contra! h
    have : q = 0 := by omega
    simp [this, Nat.factorial_ne_zero] at hq
  refine ⟨b*q, ?_, ?_⟩
  · rw [hq]; exact (Nat.mul_lt_mul_right hqpos).mpr hab
  · rw [hq]; push_cast
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ha.trans hab).ne'
    field_simp

theorem iUnion_triangularMeshRow_eq_rational :
    (⋃ N, (↑(triangularMeshRow N) : Set ℝ)) = rationalParameters := by
  rw [← factorialMeshParameters_eq_rationalParameters]
  ext x
  constructor
  · intro h
    obtain ⟨N,hN⟩ := mem_iUnion.mp h
    exact ⟨N, triangularMeshRow_subset_factorial (N+1) (triangularMeshRow_mono (Nat.le_succ N) hN)⟩
  · rintro ⟨n,d,hd,rfl⟩
    exact mem_iUnion.mpr ⟨d, mem_triangularMeshRow.mpr
      ⟨(n+1).factorial,d,Nat.factorial_pos _,hd,le_rfl,rfl⟩⟩

theorem triangularMesh_closedSpan :
    (Submodule.span ℂ (generator '' (⋃ N, (↑(triangularMeshRow N) : Set ℝ)))).topologicalClosure =
      closedSpace := by
  rw [iUnion_triangularMeshRow_eq_rational]
  exact rationalClosedSpace_eq_closedSpace

open RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.PrimePowerSchur

theorem triangularMeshRow_legal_witness {N : ℕ} {x : ℝ} (hx : x ∈ triangularMeshRow N) :
    ∃ f ∈ legalHeadKernel (N.factorial-1),
      ∀ t : ℝ, 0 < t → hilbertSequence f ⌊(N.factorial : ℝ)/t⌋₊ = realGenerator x t := by
  obtain ⟨d,hd,rfl⟩ := triangularMeshRow_subset_factorial N hx
  have hm := Nat.factorial_pos N
  refine ⟨_, rational_residue_pair_mem_legalHeadKernel _ _ hm hd.le, ?_⟩
  intro t ht
  rw [realGenerator_eq_neg_divisorAnchor _ _ hm (hm.trans hd) t ht,
    hilbertSequence_sub, hilbertSequence_smul, Pi.sub_apply, Pi.smul_apply,
    normalizedResidueHilbert_sequence, normalizedResidueHilbert_sequence]
  unfold RiemannResearch.RH.Pareto.divisorAnchorDirection
  simp only [smul_eq_mul]
  ring

end RiemannResearch.RH.Burnol.ContinuousNyman
