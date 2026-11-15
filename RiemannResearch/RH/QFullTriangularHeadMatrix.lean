/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullTriangularMobiusRepair
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Nonsingularity of the fixed full-conductor head matrix

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 2.
The explicit triangular repair proves surjectivity for the actual square
physical head matrix. Mathlib then supplies its nonsingularity and coefficient
uniqueness. There is no numerical invertibility assumption.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFullTriangularMobiusRepair
open ZetaTwoHilbert

def fixedSynthesis (N : ℕ) (c : Fin N → ℝ) : QHilbert :=
  ∑ j : Fin N, c j • qResidue (j.val + 2)

def physicalHeadMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => qSequence (qResidue (j.val + 2)) (i.val + 1)

theorem fixedSynthesis_head (N : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    qSequence (fixedSynthesis N c) (i.val + 1) =
      (physicalHeadMatrix N).mulVec c i := by
  change qSequenceLinear (∑ j : Fin N, c j • qResidue (j.val + 2)) (i.val + 1) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold Matrix.mulVec dotProduct physicalHeadMatrix
  apply Finset.sum_congr rfl
  intro j hj
  change c j * qSequence (qResidue (j.val + 2)) (i.val + 1) =
    qSequence (qResidue (j.val + 2)) (i.val + 1) * c j
  ring

private theorem bounded_span_le_fixed_span (N : ℕ) :
    Submodule.span ℝ (qResidue '' Set.Icc 1 (N + 1)) ≤
      Submodule.span ℝ (Set.range (fun j : Fin N => qResidue (j.val + 2))) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, rfl⟩
  have hd1 : 1 ≤ d := hd.1
  have hdN : d ≤ N + 1 := hd.2
  by_cases h1 : d = 1
  · rw [h1, qResidue_one]
    exact Submodule.zero_mem _
  · have hd2 : 2 ≤ d := by omega
    let j : Fin N := ⟨d - 2, by omega⟩
    apply Submodule.subset_span
    refine ⟨j, ?_⟩
    have hj : j.val + 2 = d := by dsimp only [j]; omega
    change qResidue (j.val + 2) = qResidue d
    rw [hj]

private theorem fixed_span_expansion (N : ℕ) (x : QHilbert)
    (hx : x ∈ Submodule.span ℝ (Set.range (fun j : Fin N => qResidue (j.val + 2)))) :
    ∃ c : Fin N → ℝ, x = fixedSynthesis N c := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨fun j => if j = i then 1 else 0, ?_⟩
      simp [fixedSynthesis]
  | zero => exact ⟨fun _ => 0, by simp [fixedSynthesis]⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨c, rfl⟩ := ihx
      obtain ⟨d, rfl⟩ := ihy
      exact ⟨fun j => c j + d j, by
        simp only [fixedSynthesis, add_smul, Finset.sum_add_distrib]⟩
  | smul a x hx ihx =>
      obtain ⟨c, rfl⟩ := ihx
      exact ⟨fun j => a * c j, by
        simp only [fixedSynthesis, Finset.smul_sum, smul_smul]⟩

/-- Every physical head is reached by the exact square dictionary. -/
theorem physicalHeadMatrix_mulVec_surjective (N : ℕ) :
    Function.Surjective (physicalHeadMatrix N).mulVec := by
  classical
  intro b
  let u : ℕ → ℝ := fun n =>
    if h : 0 < n ∧ n ≤ N then b ⟨n - 1, by omega⟩ else 0
  have hu0 : u 0 = 0 := by simp [u]
  have hmem := bounded_span_le_fixed_span N
    (triangularRepair_mem_bounded_span N u)
  obtain ⟨c, hc⟩ := fixed_span_expansion N (triangularRepair N u) hmem
  refine ⟨c, ?_⟩
  funext i
  rw [← fixedSynthesis_head, ← hc,
    triangularRepair_head N u hu0 (i.val + 1) (Nat.succ_pos i.val) (by omega)]
  have h : 0 < i.val + 1 ∧ i.val + 1 ≤ N := ⟨Nat.succ_pos _, by omega⟩
  dsimp only [u]
  rw [dif_pos h]
  congr 1

/-- Nonsingularity is proved for every stage, including the empty matrix. -/
theorem physicalHeadMatrix_isUnit (N : ℕ) : IsUnit (physicalHeadMatrix N) :=
  Matrix.mulVec_surjective_iff_isUnit.mp (physicalHeadMatrix_mulVec_surjective N)

theorem physicalHeadMatrix_det_ne_zero (N : ℕ) : (physicalHeadMatrix N).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (physicalHeadMatrix_isUnit N)).ne_zero

/-- Exact physical head agreement uniquely determines all dictionary coefficients. -/
theorem fixedSynthesis_coefficients_unique (N : ℕ) (c d : Fin N → ℝ)
    (hhead : ∀ i : Fin N,
      qSequence (fixedSynthesis N c) (i.val + 1) =
        qSequence (fixedSynthesis N d) (i.val + 1)) : c = d := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr (physicalHeadMatrix_isUnit N))
  funext i
  rw [← fixedSynthesis_head, ← fixedSynthesis_head]
  exact hhead i

/-- The explicit triangular repair is the unique interpolant in its fixed dictionary. -/
theorem triangularRepair_unique (N : ℕ) (u : ℕ → ℝ) (hu0 : u 0 = 0)
    (F : QHilbert)
    (hF : F ∈ Submodule.span ℝ (qResidue '' Set.Icc 1 (N + 1)))
    (hhead : ∀ n, 0 < n → n ≤ N → qSequence F n = u n) :
    F = triangularRepair N u := by
  obtain ⟨c, hc⟩ := fixed_span_expansion N F (bounded_span_le_fixed_span N hF)
  obtain ⟨d, hd⟩ := fixed_span_expansion N (triangularRepair N u)
    (bounded_span_le_fixed_span N (triangularRepair_mem_bounded_span N u))
  have hcd : c = d := fixedSynthesis_coefficients_unique N c d (by
    intro i
    rw [← hc, ← hd, hhead (i.val + 1) (Nat.succ_pos _) (by omega),
      triangularRepair_head N u hu0 (i.val + 1) (Nat.succ_pos _) (by omega)])
  rw [hc, hd, hcd]

end RiemannResearch.RH.QFullTriangularMobiusRepair
