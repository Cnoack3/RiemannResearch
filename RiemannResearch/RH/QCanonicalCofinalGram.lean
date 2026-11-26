/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMetricCorrectionBounds
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QCanonicalMetricAsymptotics
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.CanonicalMobiusMovingCovariance
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.StretchedExponentialBounds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform cofinal Gram and signed-average transfer for canonical residuals

Source: the user's request to combine both Radon--Nikodym derivatives with
the unconditional canonical discrepancy, 15 October 2026.

The complete signed difference of the Q and Pareto Gram forms is a positive
Gram form, realized by correctionVector. Its diagonal tends to zero by the
checked canonical PNT estimate. This proves uniform cofinal entry control
and absolute energy transfer for signed averages of growing dimension with
bounded l1 coefficient mass. Neither original Gram matrix is asserted to
tend to zero, and no bounded full-energy provider is assumed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QCanonicalCofinalGram
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric
open QMetricCorrectionBounds QCanonicalMovingCovariance QCanonicalMetricAsymptotics
open RiemannResearch.Analysis

/-- Exact signed difference of the two genuine canonical Gram entries. -/
def gramDiscrepancy (M N : ℕ) : ℝ :=
  zetaTwo * inner ℝ (residual M) (residual N) -
    inner ℝ (Pareto.MovingCovariance.residual M) (Pareto.MovingCovariance.residual N)

theorem gramDiscrepancy_eq (M N : ℕ) :
    gramDiscrepancy M N = metricPairing (residual M) (residual N) := by
  have h := inner_identity (residual M) (residual N)
  simp only [toPareto_residual] at h
  unfold gramDiscrepancy
  linarith only [h]

theorem gramDiscrepancy_symmetric (M N : ℕ) :
    gramDiscrepancy M N = gramDiscrepancy N M := by
  rw [gramDiscrepancy_eq, gramDiscrepancy_eq, metricPairing_symmetric]

/-- The diagonal is the complete positive correction, not a covariance estimate. -/
theorem gramDiscrepancy_self (N : ℕ) :
    gramDiscrepancy N N = metricCorrection (residual N) := by
  rw [gramDiscrepancy_eq]
  rfl

theorem gramDiscrepancy_sq_le (M N : ℕ) :
    (gramDiscrepancy M N) ^ 2 ≤
      metricCorrection (residual M) * metricCorrection (residual N) := by
  rw [gramDiscrepancy_eq]
  exact metricPairing_sq_le _ _

theorem gramDiscrepancy_sq_le_energyRates (M N : ℕ) :
    (gramDiscrepancy M N) ^ 2 ≤
      Pareto.MovingCovariance.energyRate M * Pareto.MovingCovariance.energyRate N :=
  (gramDiscrepancy_sq_le M N).trans
    (mul_le_mul (correction_le_energyRate M) (correction_le_energyRate N)
      (metricCorrection_nonneg _) (Pareto.MovingCovariance.energyRate_nonneg _))

/-- Strong convergence in the square-root reciprocal energy realization. -/
theorem correctionVector_residual_tendsto_zero :
    Tendsto (fun N => correctionVector (residual N)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp correction_tendsto_zero
  simpa only [Function.comp_def, ← correctionVector_norm_sq, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using h

/-- Both indices may move independently at arbitrary cofinal speeds. -/
theorem cofinal_gramDiscrepancy_tendsto_zero (M N : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => gramDiscrepancy (M j) (N j)) atTop (𝓝 0) := by
  have hp : Tendsto (fun j => metricCorrection (residual (M j)) *
      metricCorrection (residual (N j))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (correction_tendsto_zero.comp hM).mul (correction_tendsto_zero.comp hN)
  have hs : Tendsto (fun j => (gramDiscrepancy (M j) (N j)) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun j => gramDiscrepancy_sq_le _ _) hp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using h

/-- Uniform control of the entire infinite cofinal Gram correction block. -/
theorem uniform_tail_gramDiscrepancy (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ M, H ≤ M → ∀ N, H ≤ N → |gramDiscrepancy M N| ≤ ε := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp
    (correction_tendsto_zero.eventually (gt_mem_nhds hε))
  refine ⟨H, fun M hM N hN => ?_⟩
  rw [gramDiscrepancy_eq]
  exact metricPairing_abs_le_of_budget _ _ hε.le (hH M hM).le (hH N hN).le

def signedBlock (n : ℕ) (κ : Fin n → ℕ) (a : Fin n → ℝ) : QHilbert :=
  ∑ i, a i • residual (κ i)

theorem toPareto_signedBlock (n : ℕ) (κ : Fin n → ℕ) (a : Fin n → ℝ) :
    toPareto (signedBlock n κ a) =
      ∑ i, a i • Pareto.MovingCovariance.residual (κ i) := by
  change toParetoLinear (∑ i, a i • residual (κ i)) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ i, a i • toPareto (residual (κ i))) = _
  simp only [toPareto_residual]

theorem signedBlock_energy_identity (n : ℕ) (κ : Fin n → ℕ) (a : Fin n → ℝ) :
    zetaTwo * ‖signedBlock n κ a‖ ^ 2 =
      ‖∑ i, a i • Pareto.MovingCovariance.residual (κ i)‖ ^ 2 +
        metricCorrection (signedBlock n κ a) := by
  simpa only [toPareto_signedBlock] using norm_identity (signedBlock n κ a)

/-- H is independent of block dimension, indices, and signs of coefficients. -/
theorem uniform_signed_tail_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ n : ℕ, ∀ κ : Fin n → ℕ, ∀ a : Fin n → ℝ,
      (∀ i, H ≤ κ i) →
        metricCorrection (signedBlock n κ a) ≤ (∑ i, |a i|) ^ 2 * ε := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp
    (correction_tendsto_zero.eventually (gt_mem_nhds hε))
  refine ⟨H, fun n κ a hκ => ?_⟩
  exact metricCorrection_sum_le (fun i => residual (κ i)) a hε.le
    (fun i => (hH (κ i) (hκ i)).le)

/-- Growing dimension and signed coefficients are permitted. Every selected
index escapes to infinity through one common lower schedule. -/
theorem cofinal_signed_correction_tendsto_zero
    (n H : ℕ → ℕ) (κ : (j : ℕ) → Fin (n j) → ℕ)
    (a : (j : ℕ) → Fin (n j) → ℝ) (hH : Tendsto H atTop atTop)
    (hκ : ∀ j i, H j ≤ κ j i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ∑ i, |a j i| ≤ C) :
    Tendsto (fun j => metricCorrection (signedBlock (n j) (κ j) (a j))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun j => hb.trans_le (metricCorrection_nonneg _))
  · intro b hb
    let ε := b / (C ^ 2 + 1)
    have hε : 0 < ε := div_pos hb (by positivity)
    have hid : ε * (C ^ 2 + 1) = b := by
      dsimp [ε]
      field_simp
    have hstrict : C ^ 2 * ε < b := by nlinarith only [hid, hε]
    obtain ⟨K, hK⟩ := uniform_signed_tail_budget ε hε
    filter_upwards [hH.eventually (eventually_ge_atTop K)] with j hj
    have ht := hK (n j) (κ j) (a j) (fun i => hj.trans (hκ j i))
    have hs : (∑ i, |a j i|) ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hC).mpr (ha j)
    exact (ht.trans (mul_le_mul_of_nonneg_right hs hε.le)).trans_lt hstrict

/-- Absolute energy transfer for every bounded-l1 cofinal signed average.
The original full energies need not be bounded for this conclusion. -/
theorem cofinal_signed_energy_discrepancy_tendsto_zero
    (n H : ℕ → ℕ) (κ : (j : ℕ) → Fin (n j) → ℕ)
    (a : (j : ℕ) → Fin (n j) → ℝ) (hH : Tendsto H atTop atTop)
    (hκ : ∀ j i, H j ≤ κ j i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ∑ i, |a j i| ≤ C) :
    Tendsto (fun j => zetaTwo * ‖signedBlock (n j) (κ j) (a j)‖ ^ 2 -
      ‖∑ i, a j i • Pareto.MovingCovariance.residual (κ j i)‖ ^ 2) atTop (𝓝 0) := by
  have ht := cofinal_signed_correction_tendsto_zero n H κ a hH hκ C hC ha
  simpa only [signedBlock_energy_identity, add_sub_cancel_left] using ht

/-- The full checked stretched Mertens profile improves the log-square example,
including the finite boundary term and the exact factor N/(N+1). -/
theorem correction_eventual_stretched_bound :
    ∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      metricCorrection (residual N) ≤ 8 / ((N : ℝ) + 1) +
        C * (N : ℝ) / ((N : ℝ) + 1) *
          Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
  obtain ⟨b, hb, C, hC, hbound⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨b, hb, C, hC, ?_⟩
  filter_upwards [hbound] with N hN
  have hp : ‖Pareto.MovingCovariance.residual N‖ ^ 2 ≤
      8 + C * (N : ℝ) *
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := hN
  calc
    _ ≤ ‖Pareto.MovingCovariance.residual N‖ ^ 2 / ((N : ℝ) + 1) :=
      correction_le_energyRate N
    _ ≤ (8 + C * (N : ℝ) *
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) /
        ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := by ring


/-- The exact finite signed Gram quadratic form is the correction energy. -/
theorem signedBlock_correction_eq_gram (n : ℕ) (κ : Fin n → ℕ) (a : Fin n → ℝ) :
    metricCorrection (signedBlock n κ a) =
      ∑ i, ∑ j, a i * a j * gramDiscrepancy (κ i) (κ j) := by
  rw [← correctionVector_norm_sq, ← real_inner_self_eq_norm_sq]
  unfold signedBlock
  rw [map_sum]
  simp only [map_smul, sum_inner, real_inner_smul_left, inner_sum, real_inner_smul_right,
    correctionVector_inner, ← gramDiscrepancy_eq, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gramDiscrepancy_symmetric (κ j) (κ i)]

theorem gramDiscrepancy_quadratic_nonneg (n : ℕ) (κ : Fin n → ℕ) (a : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * gramDiscrepancy (κ i) (κ j) := by
  rw [← signedBlock_correction_eq_gram]
  exact metricCorrection_nonneg _

/-- A trace bound controls every l2-normalized signed source simultaneously. -/
theorem signedBlock_correction_le_trace (n : ℕ) (κ : Fin n → ℕ) (a : Fin n → ℝ) :
    metricCorrection (signedBlock n κ a) ≤
      (∑ i, (a i) ^ 2) * (∑ i, Pareto.MovingCovariance.energyRate (κ i)) := by
  exact (metricCorrection_sum_le_l2 (fun i => residual (κ i)) a).trans
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => correction_le_energyRate (κ i)))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))


/-- Signed change of measure for a completely arbitrary Hilbert test. -/
def testDiscrepancy (f : QHilbert) (N : ℕ) : ℝ :=
  zetaTwo * inner ℝ f (residual N) -
    inner ℝ (toPareto f) (Pareto.MovingCovariance.residual N)

theorem testDiscrepancy_eq (f : QHilbert) (N : ℕ) :
    testDiscrepancy f N = metricPairing f (residual N) := by
  have h := inner_identity f (residual N)
  simp only [toPareto_residual] at h
  unfold testDiscrepancy
  linarith only [h]

/-- An extra factor 1/(N+1) controls the norm of the covariance-change functional. -/
theorem testDiscrepancy_sq_le (f : QHilbert) (N : ℕ) :
    (testDiscrepancy f N) ^ 2 ≤
      ‖toPareto f‖ ^ 2 * metricCorrection (residual N) / ((N : ℝ) + 1) := by
  rw [testDiscrepancy_eq]
  exact metricPairing_sq_le_test_norm f (residual N) N (residual_head_zero N)

theorem testDiscrepancy_sq_le_energyRate (f : QHilbert) (N : ℕ) :
    (testDiscrepancy f N) ^ 2 ≤
      ‖toPareto f‖ ^ 2 * Pareto.MovingCovariance.energyRate N / ((N : ℝ) + 1) :=
  (testDiscrepancy_sq_le f N).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (correction_le_energyRate N) (sq_nonneg _))
      (by positivity))

/-- Uniform covariance transfer even for moving tests with squared Hilbert
norm bounded by C*(N+1). Neither test needs a pointwise uniform bound. -/
theorem growing_testDiscrepancy_tendsto_zero (f : ℕ → QHilbert)
    (C : ℝ)
    (hf : ∀ N, ‖toPareto (f N)‖ ^ 2 ≤ C * ((N : ℝ) + 1)) :
    Tendsto (fun N => testDiscrepancy (f N) N) atTop (𝓝 0) := by
  have hb (N : ℕ) : (testDiscrepancy (f N) N) ^ 2 ≤ C * metricCorrection (residual N) := by
    calc
      _ ≤ ‖toPareto (f N)‖ ^ 2 * metricCorrection (residual N) / ((N : ℝ) + 1) :=
        testDiscrepancy_sq_le _ N
      _ ≤ (C * ((N : ℝ) + 1)) * metricCorrection (residual N) / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hf N) (metricCorrection_nonneg _)) (by positivity)
      _ = _ := by field_simp
  have hs : Tendsto (fun N => (testDiscrepancy (f N) N) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hb
      (by simpa only [mul_zero] using correction_tendsto_zero.const_mul C)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht


/-- A cofinal affine block of the full Möbius candidates has the constant
metric charge of its coefficient mass. The residual block loses its charge
by the bounded-l1 comparison. -/
theorem cofinal_uncentered_discrepancy
    (n H : ℕ → ℕ) (κ : (j : ℕ) → Fin (n j) → ℕ)
    (a : (j : ℕ) → Fin (n j) → ℝ) (hH : Tendsto H atTop atTop)
    (hκ : ∀ j i, H j ≤ κ j i) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ∑ i, |a j i| ≤ C) (c : ℝ)
    (hc : Tendsto (fun j => ∑ i, a j i) atTop (𝓝 c)) :
    Tendsto (fun j =>
      let f := ∑ i, a j i • QCanonicalMovingCovariance.canonical (κ j i)
      zetaTwo * ‖f‖ ^ 2 - ‖toPareto f‖ ^ 2) atTop (𝓝 ((zetaTwo - 1) * c ^ 2)) := by
  let r (j : ℕ) := signedBlock (n j) (κ j) (a j)
  have hr2 : Tendsto (fun j => metricCorrection (r j)) atTop (𝓝 0) :=
    cofinal_signed_correction_tendsto_zero n H κ a hH hκ C hC ha
  have hr : Tendsto (fun j => correctionVector (r j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hr2
    simpa only [Function.comp_def, ← correctionVector_norm_sq, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hs
  have hconst : Tendsto (fun _ : ℕ => correctionVector qOne) atTop
      (𝓝 (correctionVector qOne)) := tendsto_const_nhds
  have hvec : Tendsto (fun j => (∑ i, a j i) • correctionVector qOne -
      correctionVector (r j)) atTop (𝓝 (c • correctionVector qOne)) := by
    simpa only [sub_zero] using (hc.smul hconst).sub hr
  have hone := norm_identity qOne
  rw [qOne_norm_sq, toPareto_qOne, hilbertOne_norm_sq, mul_one] at hone
  have hsynth (j : ℕ) :
      ∑ i, a j i • QCanonicalMovingCovariance.canonical (κ j i) =
        (∑ i, a j i) • qOne - r j := by
    simp only [r, signedBlock, QCanonicalMovingCovariance.residual, smul_sub,
      Finset.sum_sub_distrib, Finset.sum_smul, sub_sub_cancel]
  have hcq : metricCorrection qOne = zetaTwo - 1 := by linarith only [hone]
  have hlim : ‖c • correctionVector qOne‖ ^ 2 = (zetaTwo - 1) * c ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, correctionVector_norm_sq, hcq]
    ring
  have h := hvec.norm.pow 2
  rw [hlim] at h
  convert h using 1
  funext j
  dsimp only
  rw [norm_identity, add_sub_cancel_left, ← correctionVector_norm_sq,
    hsynth, map_sub, map_smul]

end RiemannResearch.RH.QCanonicalCofinalGram
