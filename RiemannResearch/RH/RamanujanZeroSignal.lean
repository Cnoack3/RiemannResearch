/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramSignalStability
import RiemannResearch.Analysis.ActualRationalFMZLimits
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

Formalization boundary: the zero-limit results explicitly take the
repository's UniformSelbergDensity (1/4) proposition. Its classical
analytic proof is not supplied here. The packet means, actual Gram
identification, exact normalization and inverse-metric stability need
no density or RH hypothesis. No growing-capacity saturation is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.RamanujanZeroSignal
open Pareto ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis
open FiniteHilbertGram FiniteGramCapacity FiniteGramSignalStability
open ActualZeroOrdinate

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
      mul_zero, zero_mul, sub_zero, add_zero, mul_one, Real.exp_zero, one_mul]
  have hr : (ordinateSum T (Real.log (q : ℝ))).re =
      realSum T (fun ρ => Real.cos (Real.log (q : ℝ) * ρ.im)) := by
    simp [ordinateSum, ActualZeroOrdinate.sum, realSum, Complex.mul_re, hphase]
  unfold sampledSignal
  congr 1
  rw [Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply,
    mul_zero, zero_mul, add_zero, hr]
  by_cases hT : T = 0
  · simp [hT]
  · field_simp [hT]
    <;> ring

theorem sampledSignal_tendsto (q : ℕ) (hq : 1 < q)
    (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (sampledSignal q) atTop (𝓝 (ArithmeticFunction.vonMangoldt q)) := by
  change Tendsto (fun T : ℝ => -(2 * Real.pi * Real.sqrt (q : ℝ)) *
    (ordinateSum T (Real.log (q : ℝ)) / (T : ℂ)).re) atTop
    (𝓝 (ArithmeticFunction.vonMangoldt q))
  have h : Tendsto
      (fun T : ℝ => ordinateSum T (Real.log (q : ℝ)) / (T : ℂ)) atTop
      (𝓝 (-((ArithmeticFunction.vonMangoldt q /
        ((2 * Real.pi) * Real.sqrt (q : ℝ)) : ℝ) : ℂ))) := by
    simpa using
      tendsto_rational_ordinate_div_vonMangoldt_of_uniformSelberg
        (n := q) (m := 1) (by norm_num) hq hD
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
    (hs : ∀ q ∈ s, 1 < q) (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (fun T => inverseNorm (family_independent s hs)
      (sampledVector s T - signal s)) atTop (𝓝 0) :=
  inverseNorm_error_tendsto (family_independent s hs) (signal s) (sampledVector s)
    (fun i => sampledSignal_tendsto i.val (hs i.val i.property) hD)

theorem coefficients_tendsto (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q)
    (h2 : 2 ∈ s) (hD : UniformSelbergDensity (1 / 4)) :
    Tendsto (coefficients s hs) atTop
      (𝓝 (normalizedCoefficients (family_independent s hs) (signal s) (signal s))) :=
  normalizedCoefficients_tendsto (family_independent s hs) (signal s)
    (signal_nonzero_of_two_mem s h2) (sampledVector s)
    (fun i => sampledSignal_tendsto i.val (hs i.val i.property) hD)

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
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ (∀ j, j ≤ τ j) ∧
      ∀ j, inverseNorm (family_independent (s j) (hs j))
        (sampledVector (s j) (τ j : ℝ) - signal (s j)) ≤
          ε j * inverseNorm (family_independent (s j) (hs j)) (signal (s j)) := by
  apply exists_strictMono_diagonal_relative_error
    (fun j => family (s j)) (fun j => family_independent (s j) (hs j))
    (fun j => signal (s j)) (fun j => signal_nonzero_of_two_mem (s j) (h2 j))
    (fun j n => sampledVector (s j) (n : ℝ)) ε hε
  intro j i
  exact (sampledSignal_tendsto i.val (hs j i.val i.property) hD).comp
    tendsto_natCast_atTop_atTop

end RiemannResearch.RH.RamanujanZeroSignal
