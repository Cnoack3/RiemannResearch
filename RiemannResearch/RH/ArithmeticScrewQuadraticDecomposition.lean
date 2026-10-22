/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ArithmeticScrewCellBounds
import RiemannResearch.RH.ScrewPolarQuadratic

/-!
# Exact signed arithmetic screw quadratic decomposition

Combine the polar hyperbolic identity, all von Mangoldt prime-power hinges
below an exact support cutoff, the signed cumulative-primitive energy, and
the complete infinite archimedean Volterra Gram series. The same identity
holds for the exact arithmetic Haar matrix.

Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05 and
canonical continuation handoff v34 support this component-assembly target.
All component normalizations are inherited without alteration from their
defining modules. This identifies the defined elementary arithmetic function,
not a completed Weil distribution. The signed prime-power hinge quadratics
and negative cosh and linear contributions remain present; all-window
positivity, source-normalization agreement, density, and RH remain open.
-/

namespace RiemannResearch.RH
open MeasureTheory Set RiemannResearch.Analysis PrimeGapCurvature
open scoped BigOperators
noncomputable section

/-- Exact signed dyadic decomposition of the defined arithmetic screw function.
The prime-power hinge quadratics retain their signs; no Weil identification
or positivity of the complete expression is asserted. -/
theorem dyadicHaarStep_arithmeticScrewFunction_quadratic_decomposition
    {R : ℝ} (hR : 0 ≤ R) (m N : ℕ) (hN : Real.exp (2 * R) < N)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    (∫ x, dyadicHaarStep R m c x *
      (∫ y, arithmeticScrewFunction (x-y) * dyadicHaarStep R m c y)) =
      -8 * (∫ x, dyadicHaarStep R m c x * Real.cosh (x / 2)) ^ 2 +
      8 * (∫ x, dyadicHaarStep R m c x * Real.sinh (x / 2)) ^ 2 +
      (∑ n ∈ Finset.range N, primePowerWeight n *
        (∫ x, dyadicHaarStep R m c x *
          (∫ y, hingeKernel (Real.log n) (x-y) * dyadicHaarStep R m c y))) -
      2 * screwLinearCoefficient *
        (∫ t, (∫ x in Iic t, dyadicHaarStep R m c x) ^ 2) +
      ∑' k : ℕ, 8 * archimedeanWeight k * archimedeanRate k *
        (∫ z, (∫ x, dyadicHaarStep R m c x *
          exponentialVolterraFeature (archimedeanRate k) x z) ^ 2) := by
  let u := dyadicHaarStep R m c
  let q : (ℝ → ℝ) → ℝ :=
    fun f => ∫ x, u x * (∫ y, f (x-y) * u y)
  have hu : Integrable u := by
    simpa only [u, mul_one] using
      integrable_dyadicHaarStep_mul_continuous R m c (fun _ => (1 : ℝ)) continuous_const
  have hqi (f : ℝ → ℝ) (hf : Continuous f) :
      (∀ x, Integrable (fun y => f (x-y) * u y)) ∧
      Integrable (fun x => u x * (∫ y, f (x-y) * u y)) :=
    finiteCellKernel_integrable _ _ _ (dyadicCell_ordered hR m) _
      (hf.comp (continuous_fst.sub continuous_snd))
  have hqadd (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
      q (fun t => f t + g t) = q f + q g := by
    dsimp [q]
    simp_rw [add_mul, integral_add ((hqi f hf).1 _) ((hqi g hg).1 _), mul_add]
    exact integral_add (hqi f hf).2 (hqi g hg).2
  have hqscale (A : ℝ) (f : ℝ → ℝ) :
      q (fun t => A * f t) = A * q f := by
    dsimp [q]
    simp_rw [mul_assoc, integral_const_mul]
    have h := integral_const_mul (μ := volume) A
      (fun x => u x * (∫ y, f (x-y) * u y))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hqsum :
      q (fun t => ∑ n ∈ Finset.range N, primePowerHingeTerm n t) =
        ∑ n ∈ Finset.range N, q (primePowerHingeTerm n) := by
    dsimp [q]
    simp_rw [Finset.sum_mul, integral_finsetSum (Finset.range N)
      (fun n _ => (hqi (primePowerHingeTerm n) (continuous_primePowerHingeTerm n)).1 _),
      Finset.mul_sum]
    exact integral_finsetSum (Finset.range N)
      (fun n _ => (hqi (primePowerHingeTerm n) (continuous_primePowerHingeTerm n)).2)
  have hterm (n : ℕ) :
      q (primePowerHingeTerm n) = primePowerWeight n *
        q (hingeKernel (Real.log n)) := hqscale _ _
  have hfinite : Continuous (fun t => ∑ n ∈ Finset.range N, primePowerHingeTerm n t) :=
    continuous_finsetSum _ (fun n _ => continuous_primePowerHingeTerm n)
  have happrox : q (arithmeticScrewApprox N 0) =
      q screwPolarPart +
        (∑ n ∈ Finset.range N, primePowerWeight n * q (hingeKernel (Real.log n))) +
        screwLinearCoefficient * q (fun t => |t|) := by
    have hdef : arithmeticScrewApprox N 0 =
        fun t => (screwPolarPart t + ∑ n ∈ Finset.range N, primePowerHingeTerm n t) +
          screwLinearCoefficient * |t| := by
      funext t
      simp [arithmeticScrewApprox]
    rw [hdef, hqadd (fun t => screwPolarPart t + ∑ n ∈ Finset.range N, primePowerHingeTerm n t)
      (fun t => screwLinearCoefficient * |t|) (continuous_screwPolarPart.add hfinite)
      (continuous_const.mul continuous_abs),
      hqadd screwPolarPart (fun t => ∑ n ∈ Finset.range N, primePowerHingeTerm n t)
        continuous_screwPolarPart hfinite,
      hqsum, hqscale]
    simp_rw [hterm]
  have htail : q (fun t => -archimedeanScrewTail 0 t) =
      ∑' k : ℕ, 8 * archimedeanWeight k * archimedeanRate k *
        (∫ z, (∫ x, u x * exponentialVolterraFeature (archimedeanRate k) x z) ^ 2) := by
    dsimp [q]
    rw [neg_archimedeanScrewTail_integral_eq_tsum 0 u hu]
    apply tsum_congr
    intro k
    simp only [Nat.add_zero]
    dsimp [u]
    rw [neg_archimedeanScrewTerm_dyadic_integral_eq hR m k c,
      dyadicHaarStep_exponentialKernel_integral_gram (archimedeanRate_pos k) R m c]
    ring
  have hpolar := dyadicHaarStep_screwPolarPart_quadratic_hyperbolic hR m c
  change q screwPolarPart =
    -8 * (∫ x, u x * Real.cosh (x / 2)) ^ 2 +
      8 * (∫ x, u x * Real.sinh (x / 2)) ^ 2 at hpolar
  have hprimitive := dyadicHaarStep_absKernel_integral_eq hR m c
  change q (fun t => |t|) =
    -2 * (∫ t, (∫ x in Iic t, u x) ^ 2) at hprimitive
  have he := arithmeticScrewFunction_sub_approx_dyadic_integral_eq_tail hR m N 0 hN c
  change q arithmeticScrewFunction - q (arithmeticScrewApprox N 0) =
    q (fun t => -archimedeanScrewTail 0 t) at he
  calc
    _ = q (arithmeticScrewApprox N 0) + q (fun t => -archimedeanScrewTail 0 t) := by
      change q arithmeticScrewFunction = _
      linarith
    _ = _ := by
      rw [happrox, htail, hpolar, hprimitive]
      dsimp [q, u]
      ring

/-- The same complete signed decomposition for the exact arithmetic Haar matrix. -/
theorem arithmeticScrewHaarMatrix_quadratic_decomposition
    {R : ℝ} (hR : 0 ≤ R) (m N : ℕ) (hN : Real.exp (2 * R) < N)
    (c : FiniteDyadicHaarIndex m → ℝ) :
    dotProduct c ((arithmeticScrewHaarMatrix R m).mulVec c) =
      -8 * (∫ x, dyadicHaarStep R m c x * Real.cosh (x / 2)) ^ 2 +
      8 * (∫ x, dyadicHaarStep R m c x * Real.sinh (x / 2)) ^ 2 +
      (∑ n ∈ Finset.range N, primePowerWeight n *
        (∫ x, dyadicHaarStep R m c x *
          (∫ y, hingeKernel (Real.log n) (x-y) * dyadicHaarStep R m c y))) -
      2 * screwLinearCoefficient *
        (∫ t, (∫ x in Iic t, dyadicHaarStep R m c x) ^ 2) +
      ∑' k : ℕ, 8 * archimedeanWeight k * archimedeanRate k *
        (∫ z, (∫ x, dyadicHaarStep R m c x *
          exponentialVolterraFeature (archimedeanRate k) x z) ^ 2) := by
  have h := dyadicHaarStep_arithmeticScrewFunction_quadratic_decomposition hR m N hN c
  rw [dyadicHaarStep_quadratic_reconstruction hR m
    (fun x y => arithmeticScrewFunction (x-y))
    (continuous_arithmeticScrewFunction.comp (continuous_fst.sub continuous_snd)) c] at h
  exact h

end
end RiemannResearch.RH
