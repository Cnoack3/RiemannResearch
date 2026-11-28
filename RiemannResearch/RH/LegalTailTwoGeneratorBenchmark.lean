/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailMeanCapacityDilation
import RiemannResearch.RH.ResidueSmallGram
import RiemannResearch.RH.ResidueProjectionSchur

/-!
# Exact two-generator energy on every legal mesh

Source: Christian Noack, legal tail-capacity handoff, November 2026.
Use the normalized atoms for conductors two and three. Their span has the
same energy under scaling of either generator.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization CoefficientStabilization.ProjectionSchur
open RiemannResearch.Analysis.FiniteHilbertGram
open CoefficientStabilization.GramMobiusCorrection TailCapacity
open IntegerDPP (fullGram)

/-- With g the exact cross-Gram entry and v the squared norm of the third-conductor atom,
this is the energy of the two-generator projection. -/
theorem twoGeneratorMesh_energy :
    let g := Real.log 2/6 + Real.log 3/12 - Real.pi/(18*Real.sqrt 3)
    let v := 2*Real.log 3/9 - Real.pi/(27*Real.sqrt 3)
    0 < v - g^2/(Real.log 2/4) ∧
      captured 2 = Real.log 2 + (Real.log 3/3 - 2*g)^2 / (v - g^2/(Real.log 2/4)) := by
  let g := inner ℝ (residueAtom 0) (residueAtom 1)
  let A := Real.log 2 / 4
  have hA : 0 < A := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have he : eliminated 1 = inverseCoeff (finiteAtom_independent 1) (residueAtom 1) := by
    rw [eliminated,fullGram,gramMatrix_inverseSource]
    rfl
  have h := inverseCoeff_normal (finiteAtom_independent 1) (residueAtom 1) (0 : Fin 1)
  rw [← he,Fintype.linearCombination_apply] at h
  simp only [Fin.sum_univ_one,Fin.val_zero,real_inner_smul_right,real_inner_self_eq_norm_sq,
    residueAtom_zero_norm_sq] at h
  have hc : eliminated 1 0 = g/A := (eq_div_iff hA.ne').mpr h
  have hs : schurSigma 1 = ‖residueAtom 1‖^2-g^2/A := by
    rw [sigma_eq_gram_schur]
    simp only [dotProduct,Fin.sum_univ_one,coupling,cross,Fin.val_zero,hc]
    dsimp only [g]
    ring
  have hη : schurEta 1 = Real.log 3/3 - 2*g := by
    rw [eta_eq_gram_schur]
    norm_num [dotProduct,Fin.sum_univ_one,coupling,cross,canonicalVector_one,g,mul_comm]
  have hE := captured_schur_step 1
  rw [captured_one,hs,hη] at hE
  have hspos := sigma_pos 1
  rw [hs] at hspos
  simp only [g,A,residueAtom_inner_zero_one,residueAtom_one_norm_sq] at hE hspos
  exact ⟨hspos,hE⟩

/-- The benchmark is available at the base stage and hence at every scale. -/
theorem twoGeneratorMesh_le_normalizedCapacity (K : ℕ) :
    captured 2 ≤ normalizedLegalTailMeanCapacity K := by
  have h₁ := error_eq_one_sub_captured 2
  change energy 2 = 1-captured 2 at h₁
  have h₂ := energy_eq_limit_add 2
  have h₃ := normalizedLegalTailMeanCapacity_mono_of_dvd (K := 0) (L := K)
    (by simp)
  rw [normalizedLegalTailMeanCapacity_zero] at h₃
  linarith [sq_nonneg ‖limitProjection - projection 2‖]

end RiemannResearch.RH.Pareto.PrimePowerSchur
