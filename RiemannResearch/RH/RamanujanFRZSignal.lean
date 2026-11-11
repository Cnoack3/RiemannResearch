/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.RamanujanZeroSignal
import RiemannResearch.Analysis.ActualRationalThirdCoefficient

/-!
# Horizontal correction in the actual Pareto inverse Gram metric

Source: FRZ_Strengthening_2026-11-10, Sections 6 and 8 (First).
The sampled zero Gram and the Pareto Gram are distinct. This module transports
the corrected *source vector* through the actual Pareto inverse, preserving
the signed cross term and the exact screened target error. At every Taylor
order the source is a finite sum over actual zeros and multiplicities.

The quartic estimate uses the explicit, intentionally deferred classical
Selberg density input. The rational Landau provider is already proved. Thus
the new inverse-cubic-log source estimate and inverse-sixth-log metric-square
budget are conditional on precisely that density input, not on RH. The
arithmetic capacity deficit remains in the final approximation bound.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.RamanujanFRZSignal
open RiemannResearch.Analysis
open FiniteHilbertGram FiniteGramCapacity FiniteGramSignalStability
open ActualZeroOrdinate RamanujanZeroSignal Pareto

/-- Actual-zero signal with every even horizontal moment through order `2 * J`. -/
def correctedSignal (J q : ℕ) (T : ℝ) : ℝ :=
  -(2 * Real.pi * Real.sqrt (q : ℝ)) *
    (horizontalTaylorPolynomial T (Real.log (q : ℝ)) J / (T : ℂ)).re

def correctedVector (J : ℕ) (s : Finset ℕ) (T : ℝ) (i : s) : ℝ :=
  correctedSignal J i.val T

def correctedCoefficients (J : ℕ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (T : ℝ) : s → ℝ :=
  normalizedCoefficients (family_independent s hs) (signal s) (correctedVector J s T)

def taylorDefect (J : ℕ) (s : Finset ℕ) (T : ℝ) : s → ℝ :=
  correctedVector J s T - landauVector s T

/-- Exact signed error at every order, before any absolute majorant. -/
theorem correctedSignal_sub_landauSignal (J q : ℕ) (T : ℝ) :
    correctedSignal J q T - landauSignal q T =
      -(2 * Real.pi * Real.sqrt (q : ℝ)) *
        (horizontalTaylorError T (Real.log (q : ℝ)) J / (T : ℂ)).re := by
  simp only [correctedSignal, landauSignal, horizontalTaylorError,
    sub_div, Complex.sub_re]
  ring

/-- The first correction is literally the observed second horizontal moment. -/
theorem correctedSignal_one (q : ℕ) (T : ℝ) :
    correctedSignal 1 q T = sampledSignal q T -
      (2 * Real.pi * Real.sqrt (q : ℝ)) *
        ((((Real.log (q : ℝ) : ℂ) ^ 2 / 2) *
          evenHorizontalMoment T (Real.log (q : ℝ)) 1) / (T : ℂ)).re := by
  have h := horizontalTaylorError_one T (Real.log (q : ℝ))
  unfold horizontalTaylorError at h
  have hp : horizontalTaylorPolynomial T (Real.log (q : ℝ)) 1 =
      ordinateSum T (Real.log (q : ℝ)) +
        ((Real.log (q : ℝ) : ℂ) ^ 2 / 2) *
          evenHorizontalMoment T (Real.log (q : ℝ)) 1 := by
    linear_combination h
  simp only [correctedSignal, sampledSignal, hp, add_div, Complex.add_re]
  ring

theorem corrected_error_decomposition (J : ℕ) (s : Finset ℕ) (T : ℝ) :
    correctedVector J s T - signal s =
      (landauVector s T - signal s) + taylorDefect J s T := by
  unfold taylorDefect
  abel

/-- The actual inverse Gram retains the signed interaction between the
Landau remainder and the retained-moment remainder. -/
theorem corrected_error_energy_exact (J : ℕ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (T : ℝ) :
    inverseNorm (family_independent s hs) (correctedVector J s T - signal s) ^ 2 =
      inverseNorm (family_independent s hs) (landauVector s T - signal s) ^ 2 +
      2 * inversePair (family_independent s hs)
        (landauVector s T - signal s) (taylorDefect J s T) +
      inverseNorm (family_independent s hs) (taylorDefect J s T) ^ 2 := by
  rw [corrected_error_decomposition, inverseNorm_sq_add]

theorem correctedSignal_sub_landau_abs_le (J q : ℕ) (T B : ℝ)
    (hB : ‖horizontalTaylorError T (Real.log (q : ℝ)) J / (T : ℂ)‖ ≤ B) :
    |correctedSignal J q T - landauSignal q T| ≤
      (2 * Real.pi * Real.sqrt (q : ℝ)) * B := by
  rw [correctedSignal_sub_landauSignal, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * Real.sqrt (q : ℝ))]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hB) (by positivity)

/-- The Landau contribution uses the actual arithmetic signal, including
composites and prime powers, rather than a prime-only substitution. -/
theorem landauSignal_error_exact (q : ℕ) (hq : 1 < q) (T : ℝ) (hT : T ≠ 0) :
    landauSignal q T - ArithmeticFunction.vonMangoldt q =
      -(2 * Real.pi * Real.sqrt (q : ℝ)) *
        ((landauSum T (Real.log (q : ℝ)) +
          ((T * rationalLandauMain q 1 : ℝ) : ℂ)) / (T : ℂ)).re := by
  have hs : Real.sqrt (q : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < q)))
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hr : (2 * Real.pi * Real.sqrt (q : ℝ)) * rationalLandauMain q 1 =
      ArithmeticFunction.vonMangoldt q := by
    rw [rationalLandauMain_eq_vonMangoldt_div_sqrt (by norm_num : 1 ≤ 1) hq]
    simp only [Nat.one_dvd, if_true, Nat.div_one, Nat.cast_one, div_one]
    field_simp [hs, hp]
  have he : ((landauSum T (Real.log (q : ℝ)) +
      ((T * rationalLandauMain q 1 : ℝ) : ℂ)) / (T : ℂ)) =
      landauSum T (Real.log (q : ℝ)) / (T : ℂ) + (rationalLandauMain q 1 : ℂ) := by
    push_cast
    field_simp [hT]
  rw [he, Complex.add_re, Complex.ofReal_re, landauSignal]
  nlinarith [hr]

/-- All-orders transfer of the two analytic remainder bounds. -/
theorem correctedSignal_error_abs_le (J q : ℕ) (hq : 1 < q)
    (T B H : ℝ) (hT : T ≠ 0)
    (hL : ‖(landauSum T (Real.log (q : ℝ)) +
      ((T * rationalLandauMain q 1 : ℝ) : ℂ)) / (T : ℂ)‖ ≤ B)
    (hH : ‖horizontalTaylorError T (Real.log (q : ℝ)) J / (T : ℂ)‖ ≤ H) :
    |correctedSignal J q T - ArithmeticFunction.vonMangoldt q| ≤
      (2 * Real.pi * Real.sqrt (q : ℝ)) * (B + H) := by
  have hlandau : |landauSignal q T - ArithmeticFunction.vonMangoldt q| ≤
      (2 * Real.pi * Real.sqrt (q : ℝ)) * B := by
    rw [landauSignal_error_exact q hq T hT, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * Real.sqrt (q : ℝ))]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hL) (by positivity)
  calc
    _ = |(correctedSignal J q T - landauSignal q T) +
        (landauSignal q T - ArithmeticFunction.vonMangoldt q)| := by congr 1; ring
    _ ≤ |correctedSignal J q T - landauSignal q T| +
        |landauSignal q T - ArithmeticFunction.vonMangoldt q| := abs_add_le _ _
    _ ≤ _ := by
      have h := correctedSignal_sub_landau_abs_le J q T H hH
      nlinarith

/-- The coordinate weight includes the actual arithmetic prefactor. -/
def quarticSignalWeight (B C a : ℝ) (q : ℕ) : ℝ :=
  (2 * Real.pi * Real.sqrt (q : ℝ)) *
    (B + (32 * C / (3 * a ^ 4)) * (Real.log (q : ℝ)) ^ 4)

theorem quarticSignalWeight_nonneg (B C a : ℝ) (q : ℕ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) : 0 ≤ quarticSignalWeight B C a q := by
  unfold quarticSignalWeight
  positivity

/-- Uniform growing-band inverse-cubic-log source error. The Landau estimate
is discharged by the existing unconditional rational provider. -/
theorem eventually_correctedSignal_error (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ q : ℕ,
      1 < q → Real.log (q : ℝ) ≤ Real.log T / 8 →
      Real.log (q : ℝ) ≤ a * Real.log T / 2 →
      |correctedSignal 1 q T - ArithmeticFunction.vonMangoldt q| ≤
        quarticSignalWeight B C a q / (Real.log T) ^ 3 := by
  obtain ⟨B, hB, hL⟩ := eventually_rational_landau_error_le_inv_log_cube
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [hL, eventually_ge_atTop T₀] with T hL hT
  intro q hq hqL hqa
  have hT1 : 1 < T := hT₀.trans_le hT
  have hu : |Real.log (q : ℝ)| ≤ a * Real.log T / 2 := by
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q)))]
    exact hqa
  have hl := hL q 1 (by norm_num) hq hqL
  simp only [Nat.cast_one, div_one] at hl
  have hh := normalized_horizontalTaylorError_one_of_selberg T (Real.log (q : ℝ))
    C a hT1 hC ha hu (hD T hT)
  rw [← horizontalTaylorError_one] at hh
  have h := correctedSignal_error_abs_le 1 q hq T _ _
    (ne_of_gt (by linarith : 0 < T)) hl hh
  apply h.trans_eq
  unfold quarticSignalWeight
  ring

/-- Transfer coordinate bounds through the complete actual Pareto inverse.
The family may grow; no hidden dimension-independent conditioning is assumed. -/
theorem corrected_metric_sq_le (J : ℕ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (T E : ℝ) (weight : ℕ → ℝ)
    (hE : 0 ≤ E) (hw : ∀ q ∈ s, 0 ≤ weight q)
    (he : ∀ q ∈ s, |correctedSignal J q T - ArithmeticFunction.vonMangoldt q| ≤
      weight q * E) :
    inverseNorm (family_independent s hs) (correctedVector J s T - signal s) ^ 2 ≤
      E ^ 2 * inverseGramWeightBudget s weight := by
  classical
  have h := inverseNorm_sq_le_entrywise (family_independent s hs)
    (correctedVector J s T - signal s) (fun i => weight i.val * E)
    (fun i => mul_nonneg (hw i.val i.property) hE)
    (fun i => he i.val i.property)
  apply h.trans_eq
  simp only [inverseGramWeightBudget, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact complete target error still contains the arithmetic capacity
deficit; accurate zero sampling alone does not establish RH. -/
theorem corrected_target_error_exact (J : ℕ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (h2 : 2 ∈ s) (T : ℝ)
    (hd : inversePair (family_independent s hs) (signal s) (correctedVector J s T) ≠ 0) :
    ‖hilbertOne - Fintype.linearCombination ℝ (family s) (correctedCoefficients J s hs T)‖ ^ 2 =
      1 / packetCapacity s hs - 1 +
        inverseNorm (family_independent s hs)
          (screenedSource (family_independent s hs) (signal s) (correctedVector J s T)) ^ 2 /
        inversePair (family_independent s hs) (signal s) (correctedVector J s T) ^ 2 :=
  normalized_target_error_screenedSource (family_independent s hs) (signal s)
    (correctedVector J s T) (signal_nonzero_of_two_mem s h2) hd
    hilbertOne hilbertOne_norm_sq (signal_observation s)

/-- One eventual threshold works for every finite support in the two stated
bands. The inverse metric is allowed to vary arbitrarily with the support. -/
theorem eventually_corrected_metric (a : ℝ) (ha : 0 < a)
    (hD : UniformSelbergDensity a) :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q),
      (∀ q ∈ s, Real.log (q : ℝ) ≤ Real.log T / 8) →
      (∀ q ∈ s, Real.log (q : ℝ) ≤ a * Real.log T / 2) →
      inverseNorm (family_independent s hs) (correctedVector 1 s T - signal s) ^ 2 ≤
        inverseGramWeightBudget s (quarticSignalWeight B C a) / (Real.log T) ^ 6 := by
  obtain ⟨B, C, hB, hC, he⟩ := eventually_correctedSignal_error a ha hD
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with T he hT
  intro s hs hband hbandA
  have hL : 0 < Real.log T := Real.log_pos hT
  have h := corrected_metric_sq_le 1 s hs T (1 / (Real.log T) ^ 3)
    (quarticSignalWeight B C a) (by positivity)
    (fun q _ => quarticSignalWeight_nonneg B C a q hB.le hC)
    (fun q hq => by
      simpa only [mul_one_div] using he q (hs q hq) (hband q hq) (hbandA q hq))
  apply h.trans_eq
  ring

/-- A fully explicit inverse-matrix budget gives complete approximation
error, not merely convergence of a replacement Gram matrix. -/
theorem corrected_target_error_le_of_budget (J : ℕ) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (h2 : 2 ∈ s) (T E ε : ℝ)
    (weight : ℕ → ℝ) (hE : 0 ≤ E) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hw : ∀ q ∈ s, 0 ≤ weight q)
    (he : ∀ q ∈ s, |correctedSignal J q T - ArithmeticFunction.vonMangoldt q| ≤
      weight q * E)
    (hbudget : E ^ 2 * inverseGramWeightBudget s weight ≤
      ε ^ 2 * packetCapacity s hs) :
    ‖hilbertOne - Fintype.linearCombination ℝ (family s) (correctedCoefficients J s hs T)‖ ^ 2 ≤
      1 / packetCapacity s hs - 1 +
        ε ^ 2 / (packetCapacity s hs * (1 - ε) ^ 2) := by
  have hh := (corrected_metric_sq_le J s hs T E weight hE hw he).trans hbudget
  have hnorm : inverseNorm (family_independent s hs) (correctedVector J s T - signal s) ≤
      ε * inverseNorm (family_independent s hs) (signal s) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hε0 (norm_nonneg _))).mp
    simpa only [mul_pow, inverseNorm, packetCapacity, capacity_eq_norm_sq] using hh
  exact normalized_target_error_le (family_independent s hs) (signal s)
    (correctedVector J s T) (signal_nonzero_of_two_mem s h2) hilbertOne
    hilbertOne_norm_sq (signal_observation s) hε0 hε hnorm

end RiemannResearch.RH.RamanujanFRZSignal
