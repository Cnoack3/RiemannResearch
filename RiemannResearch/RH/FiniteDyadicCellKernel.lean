/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.Analysis.FiniteCellKernel
import RiemannResearch.RH.FiniteDyadicHaarCompression

/-!
# Actual dyadic cell integrals in Haar coordinates
Define equal Ioc cells on [-R,R], width 2R/2^m, and form the actual double
cell integrals of any continuous real kernel. The existing literal Haar
matrix produces mean-zero integrable steps and the exact quadratic form.
The anchored screw-kernel form agrees with the convolution-cell compression.

Source: user-provided RH handoff v15 and proof-first continuation, Section 5,
support the construction. Suzuki (2023), equation (1.4),
https://arxiv.org/abs/2206.03682, supports the screw-kernel convention.
The arithmetic function g, its Weil-distribution identity, density, all-window
positivity, and RH remain separate obligations. R=0 and m=0 are included.
-/

open scoped BigOperators
open MeasureTheory Set
open RiemannResearch.Analysis

namespace RiemannResearch.RH.PrimeGapCurvature
noncomputable section

def dyadicCellWidth (R : ℝ) (m : ℕ) : ℝ := 2 * R / (2 ^ m : ℝ)
def dyadicCellLeft (R : ℝ) (m : ℕ) (j : Fin (2 ^ m)) : ℝ :=
  -R + dyadicCellWidth R m * j.val
def dyadicCellRight (R : ℝ) (m : ℕ) (j : Fin (2 ^ m)) : ℝ :=
  dyadicCellLeft R m j + dyadicCellWidth R m

theorem dyadicCellWidth_nonneg {R : ℝ} (hR : 0 ≤ R) (m : ℕ) :
    0 ≤ dyadicCellWidth R m := by
  unfold dyadicCellWidth
  positivity

theorem dyadicCell_ordered {R : ℝ} (hR : 0 ≤ R) (m : ℕ) (j : Fin (2 ^ m)) :
    dyadicCellLeft R m j ≤ dyadicCellRight R m j :=
  le_add_of_nonneg_right (dyadicCellWidth_nonneg hR m)

def dyadicHaarStep (R : ℝ) (m : ℕ) (c : FiniteDyadicHaarIndex m → ℝ) : ℝ → ℝ :=
  finiteCellStep (dyadicCellLeft R m) (dyadicCellRight R m)
    ((finiteDyadicHaarMatrix m).mulVec c)

theorem integrable_dyadicHaarStep_mul_continuous
    (R : ℝ) (m : ℕ) (c : FiniteDyadicHaarIndex m → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun x => dyadicHaarStep R m c x * f x) := by
  unfold dyadicHaarStep
  simpa only [mul_comm] using
    integrable_mul_finiteCellStep (dyadicCellLeft R m) (dyadicCellRight R m)
      ((finiteDyadicHaarMatrix m).mulVec c) f hf

theorem finiteDyadicHaarMatrix_mulVec_sum_zero (m : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    ∑ j, (finiteDyadicHaarMatrix m).mulVec c j = 0 := by
  unfold Matrix.mulVec dotProduct finiteDyadicHaarMatrix
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp only [finiteDyadicHaarAtom_sum_zero m _ (Fin.isLt _) _, zero_mul,
    Finset.sum_const_zero]

theorem dyadicHaarStep_integral_zero {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x) = 0 := by
  have h := integral_mul_finiteCellStep (dyadicCellLeft R m) (dyadicCellRight R m)
    ((finiteDyadicHaarMatrix m).mulVec c) (dyadicCell_ordered hR m)
    (fun _ => (1 : ℝ)) continuous_const
  simp only [one_mul] at h
  change (∫ x, finiteCellStep _ _ _ x) = 0
  rw [h]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one,
    dyadicCellRight, add_sub_cancel_left]
  rw [← Finset.sum_mul, finiteDyadicHaarMatrix_mulVec_sum_zero, zero_mul]

def dyadicCellKernel (R : ℝ) (m : ℕ) (k : ℝ → ℝ → ℝ) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ :=
  fun i j => ∫ x in dyadicCellLeft R m i..dyadicCellRight R m i,
    ∫ y in dyadicCellLeft R m j..dyadicCellRight R m j, k x y

theorem dyadicHaarStep_quadratic_reconstruction {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k))
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, k x y * dyadicHaarStep R m c y)) =
    dotProduct c ((finiteDyadicHaarCompression m (dyadicCellKernel R m k)).mulVec c) := by
  rw [dyadicHaarStep, finiteCellKernel_quadratic_reconstruction _ _ _
    (dyadicCell_ordered hR m) k hk]
  change (∑ i, ∑ j, (finiteDyadicHaarMatrix m).mulVec c i *
    dyadicCellKernel R m k i j * (finiteDyadicHaarMatrix m).mulVec c j) = _
  have hex : (∑ i, ∑ j, (finiteDyadicHaarMatrix m).mulVec c i *
      dyadicCellKernel R m k i j * (finiteDyadicHaarMatrix m).mulVec c j) =
      dotProduct ((finiteDyadicHaarMatrix m).mulVec c)
        ((dyadicCellKernel R m k).mulVec ((finiteDyadicHaarMatrix m).mulVec c)) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [hex, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rfl


/-- Exact connection of the full anchored kernel to the convolution-cell
Haar compression. This theorem does not assert arithmetic positivity. -/
theorem dyadicHaarStep_screw_compression {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (g : ℝ → ℝ) (hg : Continuous g)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, (g (x-y) - g x - g (-y) + g 0) * dyadicHaarStep R m c y)) =
      dotProduct c ((finiteDyadicHaarCompression m
        (dyadicCellKernel R m (fun x y => g (x-y)))).mulVec c) := by
  calc
    _ = (∫ x, dyadicHaarStep R m c x *
        (∫ y, g (x-y) * dyadicHaarStep R m c y)) :=
      finiteCellKernel_screw_reconstruction _ _ _ (dyadicCell_ordered hR m)
        g hg (dyadicHaarStep_integral_zero hR m c)
    _ = _ := dyadicHaarStep_quadratic_reconstruction hR m
      (fun x y => g (x-y)) (hg.comp (continuous_fst.sub continuous_snd)) c

end
end RiemannResearch.RH.PrimeGapCurvature

namespace RiemannResearch.RH.PrimeGapCurvature
open MeasureTheory Set
noncomputable section

theorem dyadicCellWidth_mul_count (R : ℝ) (m : ℕ) :
    dyadicCellWidth R m * (2 : ℝ)^m = 2*R := by
  unfold dyadicCellWidth
  field_simp

theorem dyadicCell_endpoints_bounds {R : ℝ} (hR : 0 ≤ R) (m : ℕ) (j : Fin (2^m)) :
    -R ≤ dyadicCellLeft R m j ∧ dyadicCellRight R m j ≤ R := by
  have hw := dyadicCellWidth_nonneg hR m
  have hj : (j.val : ℝ)+1 ≤ (2 : ℝ)^m := by
    exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hm := mul_le_mul_of_nonneg_left hj hw
  rw [dyadicCellWidth_mul_count] at hm
  have hz := mul_nonneg hw (Nat.cast_nonneg (α := ℝ) j.val)
  dsimp [dyadicCellLeft, dyadicCellRight]
  constructor <;> nlinarith

theorem abs_le_of_mem_dyadicCell {R : ℝ} (hR : 0 ≤ R) (m : ℕ) (j : Fin (2^m))
    {x : ℝ} (hx : x ∈ uIcc (dyadicCellLeft R m j) (dyadicCellRight R m j)) :
    |x| ≤ R := by
  rw [uIcc_of_le (dyadicCell_ordered hR m j)] at hx
  have hb := dyadicCell_endpoints_bounds hR m j
  exact abs_le.mpr ⟨hb.1.trans hx.1, hx.2.trans hb.2⟩

end
end RiemannResearch.RH.PrimeGapCurvature
