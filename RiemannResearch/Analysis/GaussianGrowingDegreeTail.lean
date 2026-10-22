/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Growing-degree Gaussian tail envelopes.

Source: independently developed quantitative bound for the user-provided
Gaussian interpolation argument. The paper derivation and remaining actual
counting/shell providers are in RH/InfiniteGaussianAnalyticBridge20261011.md.

The analytic limit does not assume an unknown local zero count. The final
degree hypothesis follows from a global weighted count O(T log(T+2)), once
the interpolating polynomial has at most one factor per distinct node.
-/

open Filter
open scoped Topology

noncomputable section

namespace RiemannResearch.Analysis.GaussianGrowingDegreeTail

/-- Any penalty that is o(T²) is dominated by a fixed positive Gaussian coefficient. -/
theorem tendsto_exp_gaussian_subquadratic (a : ℝ) (ha : 0 < a) (b : ℝ → ℝ)
    (hb : Tendsto (fun T : ℝ => b T / T ^ 2) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => Real.exp (-a * T ^ 2 + b T)) atTop (𝓝 0) := by
  have hcoef :
      Tendsto (fun T : ℝ => -a + b T / T ^ 2) atTop (𝓝 (-a)) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => -a) atTop (𝓝 (-a))).add hb
  have hquad : Tendsto (fun T : ℝ => T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hbot : Tendsto (fun T : ℝ => T ^ 2 * (-a + b T / T ^ 2)) atTop atBot :=
    hquad.atTop_mul_neg (neg_lt_zero.mpr ha) hcoef
  apply Real.tendsto_exp_atBot.comp
  refine hbot.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
  field_simp [hT]

/-- A quadratic Gaussian exponent dominates T(log T)^2, with either sign of C. -/
theorem tendsto_exp_gaussian_logSquared (a C : ℝ) (ha : 0 < a) :
    Tendsto (fun T : ℝ => Real.exp (-a * T ^ 2 + C * T * (Real.log T) ^ 2))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun T : ℝ => (Real.log T) ^ 2 / T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hcoef :
      Tendsto (fun T : ℝ => -a + C * ((Real.log T) ^ 2 / T)) atTop (𝓝 (-a)) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => -a) atTop (𝓝 (-a))).add
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (𝓝 C)).mul hlog)
  have hquad : Tendsto (fun T : ℝ => T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hbot :
      Tendsto (fun T : ℝ => T ^ 2 * (-a + C * ((Real.log T) ^ 2 / T)))
        atTop atBot :=
    hquad.atTop_mul_neg (neg_lt_zero.mpr ha) hcoef
  apply Real.tendsto_exp_atBot.comp
  refine hbot.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
  field_simp [hT]

/-- This envelope absorbs the polynomial prefactor in the global-count shell bound. -/
def degreeEnvelope (a : ℝ) (d : ℝ → ℕ) (T : ℝ) : ℝ :=
  (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 3) * Real.exp (-a * T ^ 2)

lemma count_prefactor_le (T : ℝ) (hT : 3 ≤ T) :
    (T + 1) * Real.log (T + 3) ≤ (T ^ 2 + 1 / 4) ^ 2 := by
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < T + 3)
  have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ T + 1)
  have hsq : 9 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 3)]
  have hquartic := mul_le_mul_of_nonneg_right hsq (sq_nonneg T)
  calc
    (T + 1) * Real.log (T + 3) ≤ (T + 1) * (T + 2) := by linarith
    _ ≤ (T ^ 2 + 1 / 4) ^ 2 := by nlinarith [sq_nonneg (T - 3)]

lemma degreeEnvelope_eq_exp (a : ℝ) (d : ℝ → ℕ) (T : ℝ) :
    degreeEnvelope a d T =
      Real.exp ((d T : ℝ) * Real.log 9 + ((d T : ℝ) + 3) *
        Real.log (T ^ 2 + 1 / 4) - a * T ^ 2) := by
  have hbase : 0 < T ^ 2 + (1 : ℝ) / 4 := by positivity
  rw [degreeEnvelope, ← Real.exp_log (by norm_num : (0 : ℝ) < 9),
    ← Real.exp_log hbase, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_add]
  simp only [Real.log_exp]
  congr 1
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

lemma degreeEnvelope_le_exp (a B T : ℝ) (d : ℝ → ℕ)
    (hT : 3 ≤ T) (hlogT : 1 ≤ Real.log T)
    (hdegree : (d T : ℝ) ≤ B * T * Real.log T) :
    degreeEnvelope a d T ≤
      Real.exp (-a * T ^ 2 + (5 * B + 9) * T * (Real.log T) ^ 2) := by
  have hTpos : 0 < T := by linarith
  have hd : 0 ≤ (d T : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ Real.log T := by linarith
  have hlog9 : Real.log 9 ≤ 2 * Real.log T := by
    calc
      Real.log 9 ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by norm_num) (by nlinarith [sq_nonneg (T - 3)])
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hbase : 0 < T ^ 2 + (1 : ℝ) / 4 := by positivity
  have hlogbase : Real.log (T ^ 2 + 1 / 4) ≤ 3 * Real.log T := by
    calc
      Real.log (T ^ 2 + 1 / 4) ≤ Real.log (T ^ 3) :=
        Real.log_le_log hbase (by
          have hprod := mul_nonneg (by linarith : 0 ≤ T - 2) (sq_nonneg T)
          nlinarith [sq_nonneg (T - 3)])
      _ = 3 * Real.log T := by rw [Real.log_pow]; norm_num
  have h1 := mul_le_mul_of_nonneg_left hlog9 hd
  have h2 := mul_le_mul_of_nonneg_left hlogbase (by positivity : 0 ≤ (d T : ℝ) + 3)
  have h3 := mul_le_mul_of_nonneg_right hdegree hL
  have hTL : 1 ≤ T * Real.log T := by nlinarith
  have h4 := mul_le_mul_of_nonneg_right hTL hL
  rw [degreeEnvelope_eq_exp]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The exact degree penalty is logarithmic in T per interpolation factor. -/
lemma degreeEnvelope_le_exp_degreePenalty (a T : ℝ) (d : ℝ → ℕ)
    (hT : 3 ≤ T) :
    degreeEnvelope a d T ≤
      Real.exp (-a * T ^ 2 + (5 * (d T : ℝ) + 9) * Real.log T) := by
  have hd : 0 ≤ (d T : ℝ) := Nat.cast_nonneg _
  have hlog9 : Real.log 9 ≤ 2 * Real.log T := by
    calc
      Real.log 9 ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by norm_num) (by nlinarith [sq_nonneg (T - 3)])
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hbase : 0 < T ^ 2 + (1 : ℝ) / 4 := by positivity
  have hlogbase : Real.log (T ^ 2 + 1 / 4) ≤ 3 * Real.log T := by
    calc
      Real.log (T ^ 2 + 1 / 4) ≤ Real.log (T ^ 3) :=
        Real.log_le_log hbase (by
          have hprod := mul_nonneg (by linarith : 0 ≤ T - 2) (sq_nonneg T)
          nlinarith [sq_nonneg (T - 3)])
      _ = 3 * Real.log T := by rw [Real.log_pow]; norm_num
  have h1 := mul_le_mul_of_nonneg_left hlog9 hd
  have h2 := mul_le_mul_of_nonneg_left hlogbase (by positivity : 0 ≤ (d T : ℝ) + 3)
  rw [degreeEnvelope_eq_exp]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The weaker condition d(T)log T=o(T²) suffices for the Gaussian envelope. -/
theorem tendsto_degreeEnvelope_subquadratic (a : ℝ) (ha : 0 < a) (d : ℝ → ℕ)
    (hdegree : Tendsto (fun T : ℝ => (d T : ℝ) * Real.log T / T ^ 2)
      atTop (𝓝 0)) :
    Tendsto (degreeEnvelope a d) atTop (𝓝 0) := by
  have hlog1 : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlog2 : Tendsto (fun T : ℝ => Real.log T / T ^ 2) atTop (𝓝 0) := by
    simpa only [div_div, id_eq, ← pow_two] using hlog1.div_atTop tendsto_id
  have hpenalty :
      Tendsto (fun T : ℝ => ((5 * (d T : ℝ) + 9) * Real.log T) / T ^ 2)
        atTop (𝓝 0) := by
    have hsum :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (5 : ℝ)) atTop (𝓝 5)).mul
        hdegree).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (9 : ℝ)) atTop (𝓝 9)).mul
        hlog2)
    have hsum0 :
        Tendsto (fun T : ℝ => 5 * ((d T : ℝ) * Real.log T / T ^ 2) +
          9 * (Real.log T / T ^ 2)) atTop (𝓝 0) := by simpa using hsum
    exact hsum0.congr (fun T => by ring)
  apply squeeze_zero'
    (Eventually.of_forall (fun T => by unfold degreeEnvelope; positivity))
    ?_ (tendsto_exp_gaussian_subquadratic a ha
      (fun T : ℝ => (5 * (d T : ℝ) + 9) * Real.log T) hpenalty)
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
  exact degreeEnvelope_le_exp_degreePenalty a T d hT

/-- A degree bound O(T log T) is enough for the full interpolation-tail envelope. -/
theorem tendsto_degreeEnvelope (a B : ℝ) (ha : 0 < a) (d : ℝ → ℕ)
    (hdegree : ∀ᶠ T in atTop, (d T : ℝ) ≤ B * T * Real.log T) :
    Tendsto (degreeEnvelope a d) atTop (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun T => by unfold degreeEnvelope; positivity))
    ?_ (tendsto_exp_gaussian_logSquared a (5 * B + 9) ha)
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)), hdegree]
    with T hT hlogT hd
  exact degreeEnvelope_le_exp a B T d hT hlogT hd

/-- A global zero-count bound naturally has log(T+2), requiring no local-count estimate. -/
theorem tendsto_degreeEnvelope_shifted (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (d : ℝ → ℕ)
    (hdegree : ∀ᶠ T in atTop, (d T : ℝ) ≤ B * T * Real.log (T + 2)) :
    Tendsto (degreeEnvelope a d) atTop (𝓝 0) := by
  apply tendsto_degreeEnvelope a (2 * B) ha d
  filter_upwards [eventually_ge_atTop (3 : ℝ), hdegree] with T hT hd
  have hlog : Real.log (T + 2) ≤ 2 * Real.log T := by
    calc
      Real.log (T + 2) ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith [sq_nonneg (T - 3)])
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hm := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB (by linarith : 0 ≤ T))
  calc
    (d T : ℝ) ≤ B * T * Real.log (T + 2) := hd
    _ ≤ (2 * B) * T * Real.log T := by nlinarith

/-- The shell-count factor from a global count bound is retained in this limit. -/
theorem tendsto_globalCountTailEnvelope (a B K : ℝ) (ha : 0 < a)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (d : ℝ → ℕ)
    (hdegree : ∀ᶠ T in atTop, (d T : ℝ) ≤ B * T * Real.log (T + 2)) :
    Tendsto
      (fun T : ℝ => K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
        Real.exp (-a * T ^ 2) * (T + 1) * Real.log (T + 3)) atTop (𝓝 0) := by
  have hlimit : Tendsto (fun T : ℝ => K * degreeEnvelope a d T) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => K) atTop (𝓝 K)).mul
        (tendsto_degreeEnvelope_shifted a B ha hB d hdegree)
  apply squeeze_zero' ?_ ?_ hlimit
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
    have hlog : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
    have hmul := mul_le_mul_of_nonneg_left (count_prefactor_le T hT)
      (by positivity :
        0 ≤ K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2))
    calc
      K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2) * (T + 1) * Real.log (T + 3) =
        (K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2)) * ((T + 1) * Real.log (T + 3)) := by ring
      _ ≤ (K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2)) * (T ^ 2 + 1 / 4) ^ 2 := hmul
      _ = K * degreeEnvelope a d T := by
        unfold degreeEnvelope
        have hdegree_add : d T + 3 = (d T + 1) + 2 := by simp [Nat.add_assoc]
        rw [hdegree_add, pow_add]
        ring

/-- The full prefactor is retained under the weaker degree-growth hypothesis. -/
theorem tendsto_globalCountTailEnvelope_subquadratic (a K : ℝ) (ha : 0 < a)
    (hK : 0 ≤ K) (d : ℝ → ℕ)
    (hdegree : Tendsto (fun T : ℝ => (d T : ℝ) * Real.log T / T ^ 2)
      atTop (𝓝 0)) :
    Tendsto
      (fun T : ℝ => K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
        Real.exp (-a * T ^ 2) * (T + 1) * Real.log (T + 3)) atTop (𝓝 0) := by
  have hlimit : Tendsto (fun T : ℝ => K * degreeEnvelope a d T) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => K) atTop (𝓝 K)).mul
        (tendsto_degreeEnvelope_subquadratic a ha d hdegree)
  apply squeeze_zero' ?_ ?_ hlimit
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
    have hlog : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with T hT
    have hmul := mul_le_mul_of_nonneg_left (count_prefactor_le T hT)
      (by positivity :
        0 ≤ K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2))
    calc
      K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2) * (T + 1) * Real.log (T + 3) =
        (K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2)) * ((T + 1) * Real.log (T + 3)) := by ring
      _ ≤ (K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
          Real.exp (-a * T ^ 2)) * (T ^ 2 + 1 / 4) ^ 2 := hmul
      _ = K * degreeEnvelope a d T := by
        unfold degreeEnvelope
        have hdegree_add : d T + 3 = (d T + 1) + 2 := by simp [Nat.add_assoc]
        rw [hdegree_add, pow_add]
        ring

end RiemannResearch.Analysis.GaussianGrowingDegreeTail
