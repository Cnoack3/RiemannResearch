/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import RiemannResearch.Analysis.ContractionScreening
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QFloorDilationEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Complete-Q contraction control of screened CRT carry energy

Source: user-directed CRT carry continuation, 22 October 2026, with the
ordinary derivation and the open RH obligation recorded in the sibling
QCarryContractionResearch20261022.md. The existing exact floor-dilation atom
identity and sharp complete-Q block-energy theorem supply all arithmetic
input. The carry formulation accepts an exact real decomposition L - C;
the existing QPrimeCRTCarries and Analysis/ScreenedCarry modules supply
floor-defined CRT decompositions and representative invariance.

Every finite positive-index, zero-charge paired sum is covered. Squarefree
support and prime-coprimality are needed for the RH legal interpretation,
but are unnecessary for these exact identities and energy bounds.
-/

noncomputable section

namespace RiemannResearch.RH.QCarryContraction
open scoped BigOperators
open ZetaTwoHilbert QFloorDilation
open RiemannResearch.Analysis.ContractionScreening

variable {ι : Type*} [Fintype ι]

def sourceVector (e : ι → ℕ) (a : ι → ℝ) : QHilbert :=
  ∑ i, a i • qResidue (e i)

def pairedVector (p : ℕ) (e : ι → ℕ) (a : ι → ℝ) : QHilbert :=
  ∑ i, a i • (qResidue (p * e i) - qResidue (e i))

theorem pairedVector_eq_floor_sub (p : ℕ) (hp : 0 < p)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (a : ι → ℝ)
    (hcharge : (∑ i, a i / (e i : ℝ)) = 0) :
    pairedVector p e a =
      floorDilation p hp (sourceVector e a) - sourceVector e a := by
  have ht : floorDilation p hp (sourceVector e a) =
      ∑ i, a i • qResidue (p * e i) := by
    have hi (i : ι) := floorDilation_qResidue p (e i) hp (he i)
    simp only [sourceVector, map_sum, map_smul, hi, smul_sub, smul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    have hz : (∑ i, a i * (1 / (e i : ℝ))) = 0 := by
      simpa only [div_eq_mul_inv, one_mul, mul_one] using hcharge
    rw [hz, zero_smul, sub_zero]
  rw [ht]
  simp only [pairedVector, sourceVector, smul_sub, Finset.sum_sub_distrib]

theorem floor_screening_identity (p : ℕ) (hp : 0 < p)
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (f : QHilbert) (hf : f ∈ V) :
    (1 / (p : ℝ)) * ‖floorDilation p hp f-f‖ ^ 2 =
      ‖floorDilation p hp f-f-V.starProjection (floorDilation p hp f-f)‖ ^ 2 +
      ‖V.starProjection (floorDilation p hp f) - (1 / (p : ℝ)) • f‖ ^ 2 +
      (1 - 1 / (p : ℝ)) * ((1 / (p : ℝ))*‖f‖ ^ 2-‖floorDilation p hp f‖ ^ 2) :=
  screening_identity V (1 / (p : ℝ)) f (floorDilation p hp f) hf

theorem paired_screened_sq_le (p : ℕ) (hp : 0 < p)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (a : ι → ℝ)
    (hcharge : (∑ i, a i / (e i : ℝ)) = 0)
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hf : sourceVector e a ∈ V) :
    ‖pairedVector p e a-V.starProjection (pairedVector p e a)‖ ^ 2 ≤
      (1 / (p : ℝ)) * ‖pairedVector p e a‖ ^ 2 := by
  rw [pairedVector_eq_floor_sub p hp e he a hcharge]
  have hpr : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : 1 / (p : ℝ) ≤ 1 := (div_le_one hpr).mpr hp1
  have hv : ‖floorDilation p hp (sourceVector e a)‖ ^ 2 ≤
      (1 / (p : ℝ))*‖sourceVector e a‖ ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      floorDilation_norm_sq_le_sharp p hp (sourceVector e a)
  exact screened_sq_le V (1 / (p : ℝ)) hq _ _ hf hv

theorem paired_total_sq_le_retained (p : ℕ) (hp : 1 < p)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (a : ι → ℝ)
    (hcharge : (∑ i, a i / (e i : ℝ)) = 0)
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hf : sourceVector e a ∈ V) :
    ‖pairedVector p e a‖ ^ 2 ≤
      ‖V.starProjection (pairedVector p e a)‖ ^ 2 / (1 - 1 / (p : ℝ)) := by
  have hp0 : 0 < p := lt_trans Nat.zero_lt_one hp
  rw [pairedVector_eq_floor_sub p hp0 e he a hcharge]
  have hpr : (0 : ℝ) < p := Nat.cast_pos.mpr hp0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hq : 1 / (p : ℝ) < 1 := (div_lt_one hpr).mpr hp1
  have hv : ‖floorDilation p hp0 (sourceVector e a)‖ ^ 2 ≤
      (1 / (p : ℝ))*‖sourceVector e a‖ ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      floorDilation_norm_sq_le_sharp p hp0 (sourceVector e a)
  exact retained_energy_controls_total V (1 / (p : ℝ)) hq _ _ hf hv


theorem carry_screened_sq_le (p : ℕ) (hp : 0 < p)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (a : ι → ℝ)
    (hcharge : (∑ i, a i / (e i : ℝ)) = 0)
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hf : sourceVector e a ∈ V) (L C : QHilbert) (hL : L ∈ V)
    (hrep : pairedVector p e a = L - C) :
    ‖C-V.starProjection C‖ ^ 2 ≤
      (1 / (p : ℝ)) * ‖pairedVector p e a‖ ^ 2 := by
  have hs : pairedVector p e a-V.starProjection (pairedVector p e a) =
      -(C-V.starProjection C) := by
    rw [hrep, map_sub, Submodule.starProjection_eq_self_iff.mpr hL]
    abel
  have h := paired_screened_sq_le p hp e he a hcharge V hf
  simpa only [hs, norm_neg] using h

theorem carry_total_sq_le_retained (p : ℕ) (hp : 1 < p)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (a : ι → ℝ)
    (hcharge : (∑ i, a i / (e i : ℝ)) = 0)
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hf : sourceVector e a ∈ V) (L C : QHilbert) (hL : L ∈ V)
    (hrep : pairedVector p e a = L - C) :
    ‖pairedVector p e a‖ ^ 2 ≤
      ‖L-V.starProjection C‖ ^ 2 / (1 - 1 / (p : ℝ)) := by
  have hproj : V.starProjection (pairedVector p e a) = L-V.starProjection C := by
    rw [hrep, map_sub, Submodule.starProjection_eq_self_iff.mpr hL]
  simpa only [hproj] using paired_total_sq_le_retained p hp e he a hcharge V hf


end RiemannResearch.RH.QCarryContraction

end
