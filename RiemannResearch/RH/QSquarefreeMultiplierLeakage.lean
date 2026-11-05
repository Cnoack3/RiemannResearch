/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.ApproximateSquareTests
import RiemannResearch.RH.QSquarefreePrimeLocalTests
import RiemannResearch.RH.CRTCarryArithmetic
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Scaled residue-multiplier leakage
Source: the user-directed four-criteria continuation, 4 November 2026.
The product is an actual Hilbert vector. Its leakage is exactly the infimum
of distances to the squarefree closure. All vanishing-leakage hypotheses
remain open arithmetic obligations.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeMultiplierLeakage
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open ArithmeticCumulative SquarefreeRadicalDifference
open RiemannResearch.NumberTheory.ApproximateSquareTests

theorem product_summable (m : ℕ) (f : QHilbert) :
    Summable (fun k => positiveQWeight k *
      (qSequence f k * residueFraction m k) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _)) _
    (qSequence_square_summable f)
  intro k
  have hb := CRTCarryArithmetic.residueFraction_abs_le_one m k
  have hs : (residueFraction m k) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (residueFraction m k), abs_nonneg (residueFraction m k)]
  rw [mul_pow]
  have hh := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg (qSequence f k)))
  nlinarith

def product (m : ℕ) (f : QHilbert) : QHilbert :=
  encodeQ (fun k => qSequence f k * residueFraction m k) (product_summable m f)

theorem product_physical (m : ℕ) (f : QHilbert) (k : ℕ) :
    qSequence (product m f) k = qSequence f k * residueFraction m k := by
  exact congrFun (qSequence_encodeQ _ _ (by simp)) k

def leakage (m : ℕ) : ℝ :=
  ‖product m displacement - closure.starProjection (product m displacement)‖

theorem leakage_eq_distance (m : ℕ) :
    leakage m = ⨅ v : closure, ‖product m displacement - (v : QHilbert)‖ :=
  Submodule.starProjection_minimal (product m displacement)

def scaledError (m : ℕ) : QHilbert :=
  (m : ℝ) • (product m displacement - closure.starProjection (product m displacement))

theorem scaledError_norm (m : ℕ) :
    ‖scaledError m‖ = (m : ℝ) * leakage m := by
  rw [scaledError, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)]
  rfl

def fourSite (f : QHilbert) (n : ℕ) : ℝ :=
  qSequence f (n ^ 2) - qSequence f (n ^ 2 - 1) -
    qSequence f n + qSequence f (n - 1)

theorem continuous_fourSite (n : ℕ) : Continuous (fun f => fourSite f n) :=
  (((continuous_qSequence (n ^ 2)).sub (continuous_qSequence (n ^ 2 - 1))).sub
    (continuous_qSequence n)).add (continuous_qSequence (n - 1))

theorem fourSite_zero (n : ℕ) : fourSite 0 n = 0 := by
  have hh (k : ℕ) : qSequence (0 : QHilbert) k = 0 :=
    congrFun (map_zero qSequenceLinear) k
  simp only [fourSite, hh, sub_self, sub_zero, add_zero]

theorem scaledError_fourSite (n m : ℕ) (hn : 2 ≤ n) (hm : n ^ 2 < m) :
    fourSite (scaledError m) n = weightedTest (qSequence displacement) n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hnlt : n < m := by nlinarith
  have hhead (k : ℕ) (hk : k < m) :
      (m : ℝ) * qSequence (product m displacement) k =
        (k : ℝ) * qSequence displacement k := by
    rw [product_physical, residueFraction, Nat.mod_eq_of_lt hk]
    field_simp [hm0]
  have hphys (k : ℕ) (hk : k < m) :
      qSequence (scaledError m) k =
        (k : ℝ) * qSequence displacement k -
          (m : ℝ) * qSequence (closure.starProjection (product m displacement)) k
        := by
    change qSequenceLinear ((m : ℝ) •
        (product m displacement - closure.starProjection (product m displacement))) k = _
    rw [map_smul, map_sub]
    change (m : ℝ) * (qSequence (product m displacement) k -
        qSequence (closure.starProjection (product m displacement)) k) = _
    rw [mul_sub, hhead k hk]
  have hz := QSquarefreeMultiplierRigidity.closure_difference_square
    (closure.starProjection_apply_mem (product m displacement)) n hn
  change qSequence _ (n ^ 2) - qSequence _ (n ^ 2 - 1) =
    qSequence _ n - qSequence _ (n - 1) at hz
  unfold fourSite weightedTest
  rw [hphys (n ^ 2) hm, hphys (n ^ 2 - 1) (by omega),
    hphys n hnlt, hphys (n - 1) (by omega)]
  rw [Nat.cast_pow, Nat.cast_sub hn2, Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num only [Nat.cast_one, Nat.cast_pow]
  linear_combination -(m : ℝ) * hz

theorem riemannHypothesis_of_scaled_leakage_sequence
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (he : Tendsto (fun j => (m j : ℝ) * leakage (m j)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hnorm : Tendsto (fun j => ‖scaledError (m j)‖) atTop (𝓝 0) := by
    simpa only [scaledError_norm] using he
  have hzero : Tendsto (fun j => scaledError (m j)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  apply QSquarefreePrimeLocalTests.riemannHypothesis_of_weighted_local_tests
  intro n hn
  have ht := ((continuous_fourSite n).tendsto (0 : QHilbert)).comp hzero
  rw [fourSite_zero] at ht
  have hc : Tendsto (fun _ : ℕ => weightedTest (qSequence displacement) n)
      atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [hm.eventually (eventually_gt_atTop (n ^ 2))] with j hj
    exact scaledError_fourSite n (m j) hn hj
  exact tendsto_nhds_unique tendsto_const_nhds hc
end RiemannResearch.RH.QSquarefreeMultiplierLeakage
