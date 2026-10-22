/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramSignalStability
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import RiemannResearch.Analysis.ActualZeroCoshMass
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Data.Nat.Squarefree

/-!
# Actual Ramanujan signals sampled from zeta-zero ordinates

Source for the ordinate bias: Ford--Zaharescu, "On the distribution of
imaginary parts of zeros of the Riemann zeta function", Theorem 1 and
(3.8), https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
The source supports the fixed-conductor analytic limit.
The inverse-metric normalization and diagonal selection follow the
user-directed research calculation of 21 October 2026.

Formalization boundary: the zero-limit results use SublinearHorizontalEnergy.
ActualZeroSublinearEnergy derives this from a single shrinking-strip condition,
or from every fixed logarithmic loss and every positive exponential rate in
UniformLogLossDensity. The analytic count provider itself is not supplied.
The packet means, actual Gram identification, exact normalization and
inverse-metric stability need no density or RH hypothesis.
No growing-capacity saturation is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.RamanujanZeroSignal
open Pareto ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis
open FiniteHilbertGram FiniteGramCapacity FiniteGramSignalStability
open ActualZeroOrdinate ActualZeroCoshMass

/-- The exact Radon--Nikodym weighted Q mean, on physical positive integers. -/
def weightedQMean (f : ℕ → ℝ) : ℝ :=
  ∑' n, positiveQWeight n * ((n : ℝ) / (n + 1 : ℝ)) * f n

theorem weightedQMean_eq_paretoMean (f : ℕ → ℝ) :
    zetaTwo * weightedQMean f = paretoMean f := by
  unfold weightedQMean paretoMean
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [positiveQWeight, positiveWeight]
  · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hZ : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
    unfold positiveQWeight positiveWeight
    field_simp [hn0, hn1, hZ]

theorem weightedQMean_packet (q : ℕ) :
    zetaTwo * weightedQMean (ramanujanPacket q) =
      ArithmeticFunction.vonMangoldt q := by
  rw [weightedQMean_eq_paretoMean, paretoMean_ramanujanPacket]

def family (s : Finset ℕ) (i : s) : ThresholdHilbert :=
  ramanujanPacketHilbert i.val

/-- Every finite conductor family inherits genuine packet independence. -/
theorem family_independent (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    LinearIndependent ℝ (family s) := by
  classical
  let f : s → Fin (s.sup id + 1) := fun i =>
    ⟨i.val - 2, by
      have hi : i.val ≤ s.sup id := Finset.le_sup (f := id) i.property
      exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le hi)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg Fin.val hij
    have hi := hs i.val i.property
    have hj := hs j.val j.property
    apply Subtype.ext
    dsimp [f] at h
    omega
  have h := (finitePacket_independent (s.sup id + 1)).comp f hf
  convert h using 1
  funext i
  change ramanujanPacketHilbert i.val =
    ramanujanPacketHilbert (i.val - 2 + 2)
  congr 1
  have hi := hs i.val i.property
  omega

def signal (s : Finset ℕ) (i : s) : ℝ := ArithmeticFunction.vonMangoldt i.val

theorem signal_observation (s : Finset ℕ) (i : s) :
    inner ℝ (family s i) hilbertOne = signal s i := by
  rw [family, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
    paretoMean_ramanujanPacket]
  rfl

theorem signal_nonzero_of_two_mem (s : Finset ℕ) (h2 : 2 ∈ s) :
    signal s ≠ 0 := by
  intro hz
  have h := congrFun hz ⟨2, h2⟩
  have hp : ArithmeticFunction.vonMangoldt 2 = Real.log (2 : ℝ) :=
    ArithmeticFunction.vonMangoldt_apply_prime (by decide)
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  simp only [signal, hp, Pi.zero_apply] at h
  linarith

theorem signal_eq_prime_of_squarefree (s : Finset ℕ) (i : s)
    (hi : Squarefree i.val) :
    signal s i = if i.val.Prime then Real.log (i.val : ℝ) else 0 := by
  by_cases hp : i.val.Prime
  · simp only [signal, if_pos hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · have hn : ¬ IsPrimePow i.val := fun h =>
      hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hi, h⟩)
    simp only [signal, ArithmeticFunction.vonMangoldt_apply, if_neg hn, if_neg hp]

/-- The complete weighted Q Gram entry, with all cross terms retained. -/
theorem gram_entry_eq_weightedQ (s : Finset ℕ) (i j : s) :
    gramMatrix (family s) i j =
      zetaTwo * weightedQMean
        (fun n => ramanujanPacket i.val n * ramanujanPacket j.val n) := by
  rw [gramMatrix, family, family, hilbert_inner_weighted,
    hilbertSequence_ramanujanPacketHilbert, hilbertSequence_ramanujanPacketHilbert]
  exact (weightedQMean_eq_paretoMean _).symm

/-- A real, multiplicity-preserving fixed-conductor zero estimate. -/
def sampledSignal (q : ℕ) (T : ℝ) : ℝ :=
  -(2 * Real.pi * Real.sqrt (q : ℝ)) *
    (ordinateSum T (Real.log (q : ℝ)) / (T : ℂ)).re

/-- The estimator is literally the multiplicity-weighted cosine sum. -/
theorem sampledSignal_eq_cos_sum (q : ℕ) (T : ℝ) :
    sampledSignal q T =
      -(2 * Real.pi * Real.sqrt (q : ℝ)) *
        (realSum T (fun ρ => Real.cos (Real.log (q : ℝ) * ρ.im)) / T) := by
  have hphase (u t : ℝ) : (ZeroOrdinate.phase u t).re = Real.cos (u * t) := by
    simp only [ZeroOrdinate.phase, Complex.exp_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, mul_one, Real.exp_zero, one_mul]
  have hr : (ordinateSum T (Real.log (q : ℝ))).re =
      realSum T (fun ρ => Real.cos (Real.log (q : ℝ) * ρ.im)) := by
    simp [ordinateSum, ActualZeroOrdinate.sum, realSum, Complex.mul_re, hphase]
  unfold sampledSignal
  congr 1
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply,
    mul_zero, add_zero, hr]
  by_cases hT : T = 0
  · simp [hT]
  · field_simp [hT]
    <;> ring

theorem sampledSignal_tendsto (q : ℕ) (hq : 1 < q)
    (hE : SublinearHorizontalEnergy) :
    Tendsto (sampledSignal q) atTop (𝓝 (ArithmeticFunction.vonMangoldt q)) := by
  change Tendsto (fun T : ℝ => -(2 * Real.pi * Real.sqrt (q : ℝ)) *
    (ordinateSum T (Real.log (q : ℝ)) / (T : ℂ)).re) atTop
    (𝓝 (ArithmeticFunction.vonMangoldt q))
  have h : Tendsto
      (fun T : ℝ => ordinateSum T (Real.log (q : ℝ)) / (T : ℂ)) atTop
      (𝓝 (-((ArithmeticFunction.vonMangoldt q /
        ((2 * Real.pi) * Real.sqrt (q : ℝ)) : ℝ) : ℂ))) := by
    have hL : Tendsto
        (fun T : ℝ => landauSum T (Real.log (q : ℝ)) / (T : ℂ)) atTop
        (𝓝 (-(rationalLandauMain q 1 : ℂ))) := by
      simpa using tendsto_rational_landau_div (n := q) (m := 1) (by norm_num) hq
    have hsum := (tendsto_ordinate_landau_error_of_sublinear_horizontal
      (Real.log (q : ℝ)) hE).add hL
    simp only [zero_add] at hsum
    have h' : Tendsto
        (fun T : ℝ => ordinateSum T (Real.log (q : ℝ)) / (T : ℂ)) atTop
        (𝓝 (-(rationalLandauMain q 1 : ℂ))) := by
      convert hsum using 1
      funext T
      ring
    simpa only [rationalLandauMain_eq_vonMangoldt_div_sqrt
      (n := q) (m := 1) (by norm_num) hq, Nat.one_dvd, if_true,
      Nat.div_one, Nat.cast_one, div_one] using h'
  have hr := (Complex.continuous_re.tendsto _).comp h
  simp only [Complex.neg_re, Complex.ofReal_re] at hr
  have hs : Real.sqrt (q : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < q)))
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hv : -(2 * Real.pi * Real.sqrt (q : ℝ)) *
      -(ArithmeticFunction.vonMangoldt q /
        ((2 * Real.pi) * Real.sqrt (q : ℝ))) =
      ArithmeticFunction.vonMangoldt q := by
    field_simp [hs, hp]
  simpa only [sampledSignal, Function.comp_def, hv] using
    hr.const_mul (-(2 * Real.pi * Real.sqrt (q : ℝ)))

def sampledVector (s : Finset ℕ) (T : ℝ) (i : s) : ℝ :=
  sampledSignal i.val T

def coefficients (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (T : ℝ) : s → ℝ :=
  normalizedCoefficients (family_independent s hs) (signal s) (sampledVector s T)

def packetCapacity (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) : ℝ :=
  capacity (family_independent s hs) (signal s)

theorem packetCapacity_le_one (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    packetCapacity s hs ≤ 1 :=
  capacity_le_one (family_independent s hs) (signal s) hilbertOne
    hilbertOne_norm_sq (signal_observation s)

theorem sampled_inverseNorm_error_tendsto (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hE : SublinearHorizontalEnergy) :
    Tendsto (fun T => inverseNorm (family_independent s hs)
      (sampledVector s T - signal s)) atTop (𝓝 0) :=
  inverseNorm_error_tendsto (family_independent s hs) (signal s) (sampledVector s)
    (fun i => sampledSignal_tendsto i.val (hs i.val i.property) hE)

theorem coefficients_tendsto (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (h2 : 2 ∈ s) (hE : SublinearHorizontalEnergy) :
    Tendsto (coefficients s hs) atTop
      (𝓝 (normalizedCoefficients (family_independent s hs) (signal s) (signal s))) :=
  normalizedCoefficients_tendsto (family_independent s hs) (signal s)
    (signal_nonzero_of_two_mem s h2) (sampledVector s)
    (fun i => sampledSignal_tendsto i.val (hs i.val i.property) hE)

/-- Exact prime-only normalization from a certified inverse-metric error. -/
theorem coefficients_prime_signal (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (hsf : ∀ q ∈ s, Squarefree q) (h2 : 2 ∈ s) (T : ℝ)
    {ε : ℝ} (hε : ε < 1)
    (he : inverseNorm (family_independent s hs) (sampledVector s T - signal s) ≤
      ε * inverseNorm (family_independent s hs) (signal s)) :
    (∑ i : s, if i.val.Prime then
      coefficients s hs T i * Real.log (i.val : ℝ) else 0) = 1 := by
  have hd := normalized_pairing_pos (family_independent s hs)
    (signal s) (sampledVector s T) (signal_nonzero_of_two_mem s h2) hε he
  have hn := normalizedCoefficients_signal (family_independent s hs)
    (signal s) (sampledVector s T) (ne_of_gt hd)
  calc
    _ = ∑ i : s, coefficients s hs T i * signal s i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [signal_eq_prime_of_squarefree s i (hsf i.val i.property)]
      split_ifs <;> simp
    _ = 1 := hn

/-- Complete true error bound, including the arithmetic capacity deficit. -/
theorem sampled_target_error_le (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (h2 : 2 ∈ s) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (he : inverseNorm (family_independent s hs) (sampledVector s T - signal s) ≤
      ε * inverseNorm (family_independent s hs) (signal s)) :
    ‖hilbertOne - Fintype.linearCombination ℝ (family s) (coefficients s hs T)‖ ^ 2 ≤
      1 / packetCapacity s hs - 1 +
        ε ^ 2 / (packetCapacity s hs * (1 - ε) ^ 2) :=
  normalized_target_error_le (family_independent s hs) (signal s) (sampledVector s T)
    (signal_nonzero_of_two_mem s h2) hilbertOne hilbertOne_norm_sq
    (signal_observation s) hε0 hε he

/-- The zero cutoffs may grow as rapidly as the actual inverse metrics require.
No uniform condition-number or fixed-stage convergence rate is needed. -/
theorem exists_strictMono_zero_cutoffs
    (s : ℕ → Finset ℕ) (hs : ∀ j q, q ∈ s j → 1 < q)
    (h2 : ∀ j, 2 ∈ s j) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hE : SublinearHorizontalEnergy) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ (∀ j, j ≤ τ j) ∧
      ∀ j, inverseNorm (family_independent (s j) (hs j))
        (sampledVector (s j) (τ j : ℝ) - signal (s j)) ≤
          ε j * inverseNorm (family_independent (s j) (hs j)) (signal (s j)) := by
  apply exists_strictMono_diagonal_relative_error
    (fun j => family (s j)) (fun j => family_independent (s j) (hs j))
    (fun j => signal (s j)) (fun j => signal_nonzero_of_two_mem (s j) (h2 j))
    (fun j n => sampledVector (s j) (n : ℝ)) ε hε
  intro j i
  exact (sampledSignal_tendsto i.val (hs j i.val i.property) hE).comp
    tendsto_natCast_atTop_atTop

/-- The centered Landau signal, including every actual zero and its multiplicity. -/
def landauSignal (q : ℕ) (T : ℝ) : ℝ :=
  -(2 * Real.pi * Real.sqrt (q : ℝ)) *
    (landauSum T (Real.log (q : ℝ)) / (T : ℂ)).re

def landauVector (s : Finset ℕ) (T : ℝ) (i : s) : ℝ := landauSignal i.val T

def densityDefect (s : Finset ℕ) (T : ℝ) : s → ℝ :=
  sampledVector s T - landauVector s T

/-- Exact signed horizontal correction, before a norm majorant is used. -/
theorem sampledSignal_sub_landauSignal (q : ℕ) (T : ℝ) :
    sampledSignal q T - landauSignal q T =
      (2 * Real.pi * Real.sqrt (q : ℝ)) *
        (coshCorrection T (Real.log (q : ℝ)) / (T : ℂ)).re := by
  rw [sampledSignal, landauSignal, exact_signed_correction, sub_div, Complex.sub_re]
  ring

/-- The total signal error retains the signed interaction of its two sources. -/
theorem signal_error_decomposition (s : Finset ℕ) (T : ℝ) :
    sampledVector s T - signal s =
      (landauVector s T - signal s) + densityDefect s T := by
  unfold densityDefect
  abel

theorem signal_error_energy_exact (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (T : ℝ) :
    inverseNorm (family_independent s hs) (sampledVector s T - signal s) ^ 2 =
      inverseNorm (family_independent s hs) (landauVector s T - signal s) ^ 2 +
      2 * inversePair (family_independent s hs)
        (landauVector s T - signal s) (densityDefect s T) +
      inverseNorm (family_independent s hs) (densityDefect s T) ^ 2 := by
  rw [signal_error_decomposition, inverseNorm_sq_add]

/-- A coordinate weight for the moment-only density certificate. -/
def horizontalSignalWeight (q : ℕ) : ℝ :=
  (2 * Real.pi * Real.sqrt (q : ℝ)) *
    (4 * (Real.cosh (|Real.log (q : ℝ)| / 2) - 1))

theorem horizontalSignalWeight_nonneg (q : ℕ) : 0 ≤ horizontalSignalWeight q := by
  unfold horizontalSignalWeight
  have h := Real.one_le_cosh (|Real.log (q : ℝ)| / 2)
  positivity

theorem horizontalSignalWeight_eq (q : ℕ) (hq : 1 ≤ q) :
    horizontalSignalWeight q = 4 * Real.pi * (Real.sqrt (q : ℝ) - 1) ^ 2 := by
  have hx1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hx : (0 : ℝ) < (q : ℝ) := by linarith
  have hs : Real.sqrt (q : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have he_sq : Real.exp (Real.log (q : ℝ) / 2) ^ 2 = (q : ℝ) := by
    calc
      _ = Real.exp (Real.log (q : ℝ) / 2 + Real.log (q : ℝ) / 2) := by
        rw [Real.exp_add]; ring
      _ = (q : ℝ) := by
        rw [show Real.log (q : ℝ) / 2 + Real.log (q : ℝ) / 2 = Real.log (q : ℝ) by ring]
        exact Real.exp_log hx
  have he : Real.exp (Real.log (q : ℝ) / 2) = Real.sqrt (q : ℝ) := by
    nlinarith [Real.sq_sqrt hx.le, Real.exp_pos (Real.log (q : ℝ) / 2),
      Real.sqrt_nonneg (q : ℝ)]
  unfold horizontalSignalWeight
  rw [abs_of_nonneg (Real.log_nonneg hx1), Real.cosh_eq, Real.exp_neg, he]
  field_simp [hs]
  ring

theorem horizontalSignalWeight_le_exponential (q : ℕ) :
    horizontalSignalWeight q ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
      ((Real.log (q : ℝ)) ^ 2 * Real.exp (|Real.log (q : ℝ)| / 2)) := by
  exact mul_le_mul_of_nonneg_left
    (sharp_coefficient_le_exponential (Real.log (q : ℝ))) (by positivity)

theorem sampledSignal_sub_landauSignal_abs_le (q : ℕ) (T : ℝ) (hT : 0 < T) :
    |sampledSignal q T - landauSignal q T| ≤
      horizontalSignalWeight q * (horizontalEnergy T / T) := by
  have hc : 0 ≤ 2 * Real.pi * Real.sqrt (q : ℝ) := by positivity
  have he : sampledSignal q T - landauSignal q T =
      -(2 * Real.pi * Real.sqrt (q : ℝ)) *
        ((ordinateSum T (Real.log (q : ℝ)) -
          landauSum T (Real.log (q : ℝ))) / (T : ℂ)).re := by
    rw [sampledSignal, landauSignal, sub_div, Complex.sub_re]
    ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg hc]
  calc
    _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
        ‖(ordinateSum T (Real.log (q : ℝ)) -
          landauSum T (Real.log (q : ℝ))) / (T : ℂ)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc
    _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
        ((4 * (Real.cosh (|Real.log (q : ℝ)| / 2) - 1)) *
          horizontalEnergy T / T) := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
      exact div_le_div_of_nonneg_right (ordinate_landau_error_sharp T _) hT.le
    _ = _ := by unfold horizontalSignalWeight; ring

/-- An explicit cost computed from the actual full inverse Gram matrix. -/
def inverseGramWeightBudget (s : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ i : s, ∑ j : s, |(gramMatrix (family s))⁻¹ i j| * weight i.val * weight j.val

/-- Scaled anisotropic errors preserve the actual inverse matrix in their certificate. -/
theorem densityDefect_metric_sq_le (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (T E : ℝ) (weight : ℕ → ℝ) (hE : 0 ≤ E)
    (hw : ∀ q ∈ s, 0 ≤ weight q)
    (he : ∀ q ∈ s, |sampledSignal q T - landauSignal q T| ≤ weight q * E) :
    inverseNorm (family_independent s hs) (densityDefect s T) ^ 2 ≤
      E ^ 2 * inverseGramWeightBudget s weight := by
  classical
  have h := inverseNorm_sq_le_entrywise (family_independent s hs) (densityDefect s T)
    (fun i => weight i.val * E)
    (fun i => mul_nonneg (hw i.val i.property) hE)
    (fun i => he i.val i.property)
  apply h.trans_eq
  simp only [inverseGramWeightBudget, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem densityDefect_metric_sq_le_horizontalEnergy
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (T : ℝ) (hT : 0 < T) :
    inverseNorm (family_independent s hs) (densityDefect s T) ^ 2 ≤
      (horizontalEnergy T / T) ^ 2 * inverseGramWeightBudget s horizontalSignalWeight := by
  exact densityDefect_metric_sq_le s hs T (horizontalEnergy T / T) horizontalSignalWeight
    (div_nonneg (horizontalEnergy_nonneg T) hT.le)
    (fun q _ => horizontalSignalWeight_nonneg q)
    (fun q _ => sampledSignal_sub_landauSignal_abs_le q T hT)

def bandSignalWeight (q : ℕ) : ℝ :=
  (2 * Real.pi * Real.sqrt (q : ℝ)) * (Real.log (q : ℝ)) ^ 2

/-- The finite frequency band supplies a Gram-aware quantitative density budget. -/
theorem densityDefect_metric_sq_le_tailProfile
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (T M decay θ : ℝ) (hT : 0 < T) (hM : 0 ≤ M) (hdecay : 0 < decay)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hband : ∀ q ∈ s, |Real.log (q : ℝ)| ≤ θ * decay)
    (htail : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ M * Real.exp (-decay * t)) :
    inverseNorm (family_independent s hs) (densityDefect s T) ^ 2 ≤
      ((2 / (1 - θ ^ 2)) * (M / (T * decay ^ 2))) ^ 2 *
        inverseGramWeightBudget s bandSignalWeight := by
  have hθsq : 0 < 1 - θ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hθ1) (by linarith : 0 < 1 + θ)]
  apply densityDefect_metric_sq_le s hs T _ bandSignalWeight
  · positivity
  · intro q hq
    unfold bandSignalWeight
    positivity
  · intro q hq
    have hc : 0 ≤ 2 * Real.pi * Real.sqrt (q : ℝ) := by positivity
    have he : sampledSignal q T - landauSignal q T =
        -(2 * Real.pi * Real.sqrt (q : ℝ)) *
          ((ordinateSum T (Real.log (q : ℝ)) -
            landauSum T (Real.log (q : ℝ))) / (T : ℂ)).re := by
      rw [sampledSignal, landauSignal, sub_div, Complex.sub_re]
      ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg hc]
    calc
      _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
          ‖(ordinateSum T (Real.log (q : ℝ)) -
            landauSum T (Real.log (q : ℝ))) / (T : ℂ)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc
      _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
          ((2 * (Real.log (q : ℝ)) ^ 2 / (1 - θ ^ 2)) *
            (M / (T * decay ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (normalized_ordinate_landau_error_of_right_expTail_band T _ M decay θ
            hT hM hdecay hθ0 hθ1 (hband q hq) htail) hc
      _ = _ := by unfold bandSignalWeight; ring

/-- The exact target formula uses only the screened actual sampled signal. -/
theorem sampled_target_error_screened (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (h2 : 2 ∈ s) (T : ℝ)
    (hd : inversePair (family_independent s hs) (signal s) (sampledVector s T) ≠ 0) :
    ‖hilbertOne - Fintype.linearCombination ℝ (family s) (coefficients s hs T)‖ ^ 2 =
      1 / packetCapacity s hs - 1 +
        inverseNorm (family_independent s hs)
          (screenedSource (family_independent s hs) (signal s) (sampledVector s T)) ^ 2 /
        inversePair (family_independent s hs) (signal s) (sampledVector s T) ^ 2 :=
  normalized_target_error_screenedSource (family_independent s hs) (signal s)
    (sampledVector s T) (signal_nonzero_of_two_mem s h2) hd
    hilbertOne hilbertOne_norm_sq (signal_observation s)

theorem sampled_target_error_le_of_screened (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (h2 : 2 ∈ s) (T η : ℝ) (hη : 0 ≤ η)
    (hd : inversePair (family_independent s hs) (signal s) (sampledVector s T) ≠ 0)
    (he : inverseNorm (family_independent s hs)
      (screenedSource (family_independent s hs) (signal s) (sampledVector s T)) ≤
      η * |inversePair (family_independent s hs) (signal s) (sampledVector s T)|) :
    ‖hilbertOne - Fintype.linearCombination ℝ (family s) (coefficients s hs T)‖ ^ 2 ≤
      1 / packetCapacity s hs - 1 + η ^ 2 :=
  normalized_target_error_le_of_screenedSource (family_independent s hs) (signal s)
    (sampledVector s T) (signal_nonzero_of_two_mem s h2) hd
    hilbertOne hilbertOne_norm_sq (signal_observation s) η hη he


/-- Exact prime normalization needs only a nonzero actual pairing. -/
theorem coefficients_prime_signal_of_pairing (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hsf : ∀ q ∈ s, Squarefree q) (T : ℝ)
    (hd : inversePair (family_independent s hs) (signal s) (sampledVector s T) ≠ 0) :
    (∑ i : s, if i.val.Prime then
      coefficients s hs T i * Real.log (i.val : ℝ) else 0) = 1 := by
  have hn := normalizedCoefficients_signal (family_independent s hs)
    (signal s) (sampledVector s T) hd
  calc
    _ = ∑ i : s, coefficients s hs T i * signal s i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [signal_eq_prime_of_squarefree s i (hsf i.val i.property)]
      split_ifs <;> simp
    _ = 1 := hn

/-- The two signed errors are screened in the same actual inverse metric. -/
theorem screened_signal_error_decomposition (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (h2 : 2 ∈ s) (T : ℝ) :
    screenedSource (family_independent s hs) (signal s) (sampledVector s T) =
      screenedSource (family_independent s hs) (signal s) (landauVector s T - signal s) +
      screenedSource (family_independent s hs) (signal s) (densityDefect s T) := by
  have h := congrArg (screenedSource (family_independent s hs) (signal s))
    (signal_error_decomposition s T)
  rw [screenedSource_sub,
    screenedSource_self _ _ (signal_nonzero_of_two_mem s h2), sub_zero,
    screenedSource_add] at h
  exact h

theorem screened_signal_error_energy_exact (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (h2 : 2 ∈ s) (T : ℝ) :
    inverseNorm (family_independent s hs)
        (screenedSource (family_independent s hs) (signal s) (sampledVector s T)) ^ 2 =
      inverseNorm (family_independent s hs)
        (screenedSource (family_independent s hs) (signal s) (landauVector s T - signal s)) ^ 2 +
      2 * inversePair (family_independent s hs)
        (screenedSource (family_independent s hs) (signal s) (landauVector s T - signal s))
        (screenedSource (family_independent s hs) (signal s) (densityDefect s T)) +
      inverseNorm (family_independent s hs)
        (screenedSource (family_independent s hs) (signal s) (densityDefect s T)) ^ 2 := by
  rw [screened_signal_error_decomposition s hs h2 T, inverseNorm_sq_add]

/-- The density budget may first discard any coherent radial bias c times Lambda. -/
theorem sampled_target_error_le_of_split_screened (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (h2 : 2 ∈ s) (T η c : ℝ) (hη : 0 ≤ η)
    (hd : inversePair (family_independent s hs) (signal s) (sampledVector s T) ≠ 0)
    (he : inverseNorm (family_independent s hs)
        (screenedSource (family_independent s hs) (signal s) (landauVector s T - signal s)) +
      inverseNorm (family_independent s hs) (densityDefect s T - c • signal s) ≤
        η * |inversePair (family_independent s hs) (signal s) (sampledVector s T)|) :
    ‖hilbertOne - Fintype.linearCombination ℝ (family s) (coefficients s hs T)‖ ^ 2 ≤
      1 / packetCapacity s hs - 1 + η ^ 2 := by
  apply sampled_target_error_le_of_screened s hs h2 T η hη hd
  rw [screened_signal_error_decomposition s hs h2 T]
  exact (inverseNorm_add_le _ _ _).trans
    ((add_le_add le_rfl
      (inverseNorm_screenedSource_le_sub_smul (family_independent s hs) (signal s)
        (densityDefect s T) (signal_nonzero_of_two_mem s h2) c)).trans he)

/-- The exact screened inverse matrix determines this coordinate budget. -/
def screenedGramWeightBudget (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (weight : ℕ → ℝ) : ℝ :=
  ∑ i : s, ∑ j : s,
    |screenedInverseMatrix (family_independent s hs) (signal s) i j| *
      weight i.val * weight j.val

theorem densityDefect_screened_metric_sq_le (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (h2 : 2 ∈ s) (T E c : ℝ)
    (weight : ℕ → ℝ) (hE : 0 ≤ E) (hw : ∀ q ∈ s, 0 ≤ weight q)
    (he : ∀ q ∈ s,
      |sampledSignal q T - landauSignal q T - c * ArithmeticFunction.vonMangoldt q| ≤
        weight q * E) :
    inverseNorm (family_independent s hs)
      (screenedSource (family_independent s hs) (signal s) (densityDefect s T)) ^ 2 ≤
        E ^ 2 * screenedGramWeightBudget s hs weight := by
  classical
  have h := inverseNorm_screenedSource_sq_le_entrywise (family_independent s hs)
    (signal s) (densityDefect s T - c • signal s) (fun i => weight i.val * E)
    (signal_nonzero_of_two_mem s h2)
    (fun i => mul_nonneg (hw i.val i.property) hE)
    (fun i => he i.val i.property)
  rw [screenedSource_sub_smul_self] at h
  · apply h.trans_eq
    simp only [screenedGramWeightBudget, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · exact signal_nonzero_of_two_mem s h2

/-- Coordinate weight monotonicity certifies an improvement of the full budget. -/
theorem inverseGramWeightBudget_mono (s : Finset ℕ) (v w : ℕ → ℝ)
    (hv : ∀ q ∈ s, 0 ≤ v q) (hle : ∀ q ∈ s, v q ≤ w q) :
    inverseGramWeightBudget s v ≤ inverseGramWeightBudget s w := by
  classical
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul (hle i.val i.property) (hle j.val j.property)
    (hv j.val j.property) ((hv i.val i.property).trans (hle i.val i.property))
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left h (abs_nonneg ((gramMatrix (family s))⁻¹ i j))

theorem inverseGramWeightBudget_horizontal_le_exponential (s : Finset ℕ) :
    inverseGramWeightBudget s horizontalSignalWeight ≤
      inverseGramWeightBudget s (fun q => (2 * Real.pi * Real.sqrt (q : ℝ)) *
        ((Real.log (q : ℝ)) ^ 2 * Real.exp (|Real.log (q : ℝ)| / 2))) :=
  inverseGramWeightBudget_mono s _ _
    (fun q _ => horizontalSignalWeight_nonneg q)
    (fun q _ => horizontalSignalWeight_le_exponential q)

/-- Keep each frequency's exact exponential-tail denominator. -/
def tailSignalWeight (decay : ℝ) (q : ℕ) : ℝ :=
  (4 * Real.pi * Real.sqrt (q : ℝ)) * (Real.log (q : ℝ)) ^ 2 /
    (decay ^ 2 - (Real.log (q : ℝ)) ^ 2)

theorem densityDefect_metric_sq_le_tailProfile_anisotropic
    (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (T M decay : ℝ) (hT : 0 < T) (hM : 0 ≤ M)
    (hband : ∀ q ∈ s, |Real.log (q : ℝ)| < decay)
    (htail : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      rightStrictTail T t ≤ M * Real.exp (-decay * t)) :
    inverseNorm (family_independent s hs) (densityDefect s T) ^ 2 ≤
      (M / T) ^ 2 * inverseGramWeightBudget s (tailSignalWeight decay) := by
  apply densityDefect_metric_sq_le s hs T (M / T) (tailSignalWeight decay)
    (div_nonneg hM hT.le)
  · intro q hq
    have hdec : 0 < decay := lt_of_le_of_lt (abs_nonneg _) (hband q hq)
    have hden : 0 < decay ^ 2 - (Real.log (q : ℝ)) ^ 2 := by
      nlinarith [sq_abs (Real.log (q : ℝ)),
        mul_pos (sub_pos.mpr (hband q hq)) (by positivity :
          0 < decay + |Real.log (q : ℝ)|)]
    unfold tailSignalWeight
    positivity
  · intro q hq
    have hc : 0 ≤ 2 * Real.pi * Real.sqrt (q : ℝ) := by positivity
    have he : sampledSignal q T - landauSignal q T =
        -(2 * Real.pi * Real.sqrt (q : ℝ)) *
          ((ordinateSum T (Real.log (q : ℝ)) -
            landauSum T (Real.log (q : ℝ))) / (T : ℂ)).re := by
      rw [sampledSignal, landauSignal, sub_div, Complex.sub_re]
      ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg hc]
    calc
      _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
          ‖(ordinateSum T (Real.log (q : ℝ)) -
            landauSum T (Real.log (q : ℝ))) / (T : ℂ)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc
      _ ≤ (2 * Real.pi * Real.sqrt (q : ℝ)) *
          ((2 * M * (Real.log (q : ℝ)) ^ 2 /
            (decay ^ 2 - (Real.log (q : ℝ)) ^ 2)) / T) := by
        apply mul_le_mul_of_nonneg_left _ hc
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
        exact div_le_div_of_nonneg_right
          (ordinate_landau_error_of_right_expTail T _ M decay hM (hband q hq) htail) hT.le
      _ = _ := by unfold tailSignalWeight; ring

end RiemannResearch.RH.RamanujanZeroSignal
