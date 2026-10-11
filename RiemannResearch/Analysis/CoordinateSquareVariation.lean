/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- The Apache-specific header convention does not determine project licensing.
set_option linter.style.header false

/-!
# Sharp variation bound for coordinate-square laws

Source: user-provided DPP residual-law continuation, equation (4),
October 2026. This isolates the coordinate Hilbert-space argument. There
are no arithmetic, approximation, or RH assumptions here.

-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.Analysis.CoordinateSquareVariation

variable {ι : Type*}

/-- Finite coordinate Cauchy--Schwarz before any norm or probability input. -/
theorem finite_l1_square_difference_sq_le
    (A : Finset ι) (u v : ι → ℝ) :
    (∑ i ∈ A, |(u i) ^ 2-(v i) ^ 2|) ^ 2 ≤
      (∑ i ∈ A, (u i-v i) ^ 2) * (∑ i ∈ A, (u i+v i) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq A
    (fun i => |u i-v i|) (fun i => |u i+v i|)
  have hterm (i : ι) : |u i-v i| * |u i+v i| = |(u i) ^ 2-(v i) ^ 2| := by
    rw [← abs_mul]
    congr 1
    ring
  simpa only [hterm, sq_abs] using h

abbrev RealL2 (ι : Type*) := lp (fun _ : ι => ℝ) 2

theorem coordinate_square_summable (x : RealL2 ι) :
    Summable (fun i => (x i) ^ 2) := by
  have hs := Memℓp.summable
    (show 0 < (2 : ENNReal).toReal by norm_num) x.property
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs

theorem norm_sq_eq_coordinate_tsum (x : RealL2 ι) :
    ‖x‖ ^ 2 = ∑' i, (x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  congr 1
  funext i
  simp [Real.norm_eq_abs, sq_abs]

theorem finite_coordinate_square_le_norm_sq (x : RealL2 ι) (A : Finset ι) :
    (∑ i ∈ A, (x i) ^ 2) ≤ ‖x‖ ^ 2 := by
  rw [norm_sq_eq_coordinate_tsum]
  exact (coordinate_square_summable x).sum_le_tsum A (fun i _ => sq_nonneg _)

/-- The finite total coordinate variation is controlled by the whole Hilbert
angle. The bound is independent of the chosen finite set. -/
theorem finite_coordinate_variation_sq_le
    (u v : RealL2 ι) (hu : ‖u‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1)
    (A : Finset ι) :
    (∑ i ∈ A, |(u i) ^ 2-(v i) ^ 2|) ^ 2 ≤
      4*(1-(inner ℝ u v) ^ 2) := by
  have hminus := finite_coordinate_square_le_norm_sq (u-v) A
  have hplus := finite_coordinate_square_le_norm_sq (u+v) A
  change (∑ i ∈ A, (u i-v i) ^ 2) ≤ ‖u-v‖ ^ 2 at hminus
  change (∑ i ∈ A, (u i+v i) ^ 2) ≤ ‖u+v‖ ^ 2 at hplus
  calc
    _ ≤ (∑ i ∈ A, (u i-v i) ^ 2) * (∑ i ∈ A, (u i+v i) ^ 2) :=
      finite_l1_square_difference_sq_le A u v
    _ ≤ ‖u-v‖ ^ 2 * ‖u+v‖ ^ 2 := mul_le_mul hminus hplus
      (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
    _ = _ := by
      rw [norm_sub_sq_real, norm_add_sq_real, hu, hv]
      ring

theorem coordinate_square_difference_abs_summable (u v : RealL2 ι) :
    Summable (fun i => |(u i) ^ 2-(v i) ^ 2|) := by
  apply Summable.of_nonneg_of_le (fun i => abs_nonneg _)
    (fun i => ?_) ((coordinate_square_summable u).add (coordinate_square_summable v))
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (u i), sq_nonneg (v i)]

theorem coordinate_variation_sq_le
    (u v : RealL2 ι) (hu : ‖u‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1) :
    (∑' i, |(u i) ^ 2-(v i) ^ 2|) ^ 2 ≤ 4*(1-(inner ℝ u v) ^ 2) := by
  classical
  have hs := (coordinate_square_difference_abs_summable u v).hasSum
  change Tendsto (fun A : Finset ι => ∑ i ∈ A, |(u i) ^ 2-(v i) ^ 2|)
    atTop (𝓝 (∑' i, |(u i) ^ 2-(v i) ^ 2|)) at hs
  exact le_of_tendsto (hs.pow 2)
    (Eventually.of_forall (fun A => finite_coordinate_variation_sq_le u v hu hv A))

/-- Half the full absolute coordinate-square difference is the ordinary
total variation of the unit-vector sampling laws. -/
def coordinateTV (u v : RealL2 ι) : ℝ :=
  (∑' i, |(u i) ^ 2-(v i) ^ 2|)/2

theorem coordinateTV_nonneg (u v : RealL2 ι) : 0 ≤ coordinateTV u v := by
  exact div_nonneg (tsum_nonneg (fun i => abs_nonneg _)) (by norm_num)

/-- Sharp squared form of the real pure-state coordinate variation bound. -/
theorem coordinateTV_sq_le
    (u v : RealL2 ι) (hu : ‖u‖ ^ 2 = 1) (hv : ‖v‖ ^ 2 = 1) :
    (coordinateTV u v) ^ 2 ≤ 1-(inner ℝ u v) ^ 2 := by
  have h := coordinate_variation_sq_le u v hu hv
  unfold coordinateTV
  nlinarith

end RiemannResearch.Analysis.CoordinateSquareVariation
