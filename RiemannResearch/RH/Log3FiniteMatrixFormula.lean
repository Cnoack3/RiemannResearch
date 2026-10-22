/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.Log3Parameters
import Mathlib.Analysis.PSeries
import Mathlib.Data.Matrix.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Exact-real candidate formula scaffold at `L = log 3`

Source: the user-provided recovered `rh_log3_second_interval_verifier.py`.
The source supports transcription of the displayed formulas only.

This module does not formalize interval enclosures, operator provenance,
Hermitianity, high-mode positivity, Schur-complement validity, or positive
definiteness. In particular, definitions named `candidateHighFloor`,
`schurFormula`, and `finiteLowerFormula` are formula candidates, not
theorems identifying an operator or proving a valid order bound.
-/

open scoped BigOperators

noncomputable section

namespace RiemannResearch.RH.Log3FiniteMatrixFormula

/-- The low-mode index is definitionally the same index used by the exact
rational interval certificate. -/
abbrev LowIndex :=
  RiemannResearch.RH.Log3Parameters.LowIndex
abbrev ChannelIndex := RiemannResearch.RH.Log3Parameters.ChannelIndex

inductive Parity
  | even
  | odd
deriving DecidableEq, Repr

namespace Parity

def sign : Parity → ℝ
  | even => 1
  | odd => -1

def poleCoefficient : Parity → ℝ
  | even => 2
  | odd => -2

def mode : Parity → LowIndex → ℕ
  | even, i => 2 * i.1
  | odd, i => 2 * i.1 + 1

def nextMode : Parity → ℕ
  | even => 40
  | odd => 41

@[simp] theorem sign_even : sign even = 1 := rfl
@[simp] theorem sign_odd : sign odd = -1 := rfl
@[simp] theorem poleCoefficient_even : poleCoefficient even = 2 := rfl
@[simp] theorem poleCoefficient_odd : poleCoefficient odd = -2 := rfl
@[simp] theorem mode_even (i : LowIndex) : mode even i = 2 * i.1 := rfl
@[simp] theorem mode_odd (i : LowIndex) : mode odd i = 2 * i.1 + 1 := rfl

end Parity

def R : ℝ := Real.log 3
def H : ℝ := Real.log 2
def wPrime : ℝ := H / Real.sqrt 2
def kappa : ℝ :=
  Real.eulerMascheroniConstant + Real.log (8 * Real.pi) + Real.pi / 2

def alpha (j : ℕ) : ℝ := 2 * (j : ℝ) + (1 : ℝ) / 2

def basisNorm (n : ℕ) : ℝ :=
  if n = 0 then 1 / Real.sqrt R else Real.sqrt (2 / R)

def frequency (n : ℕ) : ℝ := (n : ℝ) * Real.pi / R

def integralCosFormula
    (omega phase left right : ℝ) (zeroFrequency : Bool) : ℝ :=
  if zeroFrequency then
    (right - left) * Real.cos phase
  else
    (Real.sin (omega * right + phase) -
      Real.sin (omega * left + phase)) / omega

def aInfinityMode (n : ℕ) : ℝ :=
  let t := frequency n
  ∑' j : ℕ,
    2 * t ^ 2 /
      (alpha j * (alpha j ^ 2 + t ^ 2))

def primeShiftEntry (m n : ℕ) : ℝ :=
  let km := frequency m
  let kn := frequency n
  basisNorm m * basisNorm n *
    (integralCosFormula (km - kn) (kn * H) H R (decide (m = n)) +
      integralCosFormula (km + kn) (-kn * H) H R (decide (m + n = 0)))

def edgeProjectionEntry (m n : ℕ) : ℝ :=
  let km := frequency m
  let kn := frequency n
  basisNorm m * basisNorm n *
    (integralCosFormula (km - kn) 0 H R (decide (m = n)) +
      integralCosFormula (km + kn) 0 H R (decide (m + n = 0)))

def channelLowCoefficient (p : Parity) (n j : ℕ) : ℝ :=
  let a := alpha j
  let q := Real.exp (-a * R)
  let k := frequency n
  p.sign * basisNorm n * Real.sqrt 2 * a *
      Real.sqrt (1 - p.sign * q) /
    (a ^ 2 + k ^ 2)

def channelFullGram (p : Parity) (j k : ℕ) : ℝ :=
  let a := alpha j
  let b := alpha k
  let qa := Real.exp (-a * R)
  let qb := Real.exp (-b * R)
  let da := 1 - p.sign * qa
  let db := 1 - p.sign * qb
  let first := (1 - qa * qb) / (a + b)
  let second := if j = k then R * qa else (qb - qa) / (a - b)
  (first + p.sign * second) / Real.sqrt (da * db)

def channelShiftPairing (p : Parity) (j n : ℕ) : ℝ :=
  let a := alpha j
  let q := Real.exp (-a * R)
  let normalization := 1 / Real.sqrt 2 / Real.sqrt (1 - p.sign * q)
  let k := frequency n
  let d := R - H
  let cosine := Real.cos (k * d)
  let sine := Real.sin (k * d)
  let bracket :=
    a * cosine + k * sine - a * Real.exp (-a * d) +
      p.sign *
        (a * Real.exp (-a * H) + q * (-a * cosine + k * sine))
  2 * basisNorm n * normalization * bracket / (a ^ 2 + k ^ 2)

def diagonalLow (p : Parity) (i : LowIndex) : ℝ :=
  aInfinityMode (p.mode i) - kappa

/-- Candidate comparison value at the first discarded mode. No theorem here
asserts that it is positive or is a uniform lower bound for the high block. -/
def candidateHighFloor (p : Parity) : ℝ :=
  aInfinityMode p.nextMode - kappa - wPrime

def primeShiftMatrix (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  fun i j => primeShiftEntry (p.mode i) (p.mode j)

def edgeProjectionMatrix (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  fun i j => edgeProjectionEntry (p.mode i) (p.mode j)

def channelLowMatrix (p : Parity) : Matrix LowIndex ChannelIndex ℝ :=
  fun i j => channelLowCoefficient p (p.mode i) j.1

def channelGramMatrix (p : Parity) : Matrix ChannelIndex ChannelIndex ℝ :=
  fun j k => channelFullGram p j.1 k.1

def channelShiftMatrix (p : Parity) : Matrix ChannelIndex LowIndex ℝ :=
  fun j i => channelShiftPairing p j.1 (p.mode i)

def bSquaredLow (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  primeShiftMatrix p * primeShiftMatrix p

def qbpGram (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  edgeProjectionMatrix p - bSquaredLow p

def qChannelGram (p : Parity) : Matrix ChannelIndex ChannelIndex ℝ :=
  channelGramMatrix p -
    (channelLowMatrix p).transpose * channelLowMatrix p

def qChannelQbp (p : Parity) : Matrix ChannelIndex LowIndex ℝ :=
  channelShiftMatrix p -
    (channelLowMatrix p).transpose * primeShiftMatrix p

def crossMatrix (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  (qChannelQbp p).transpose * (channelLowMatrix p).transpose +
    channelLowMatrix p * qChannelQbp p

def xStarX (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  fun i j =>
    wPrime ^ 2 * qbpGram p i j -
      wPrime * crossMatrix p i j +
      (channelLowMatrix p * qChannelGram p *
        (channelLowMatrix p).transpose) i j

def lowChannelOuterProduct (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  channelLowMatrix p * (channelLowMatrix p).transpose

def lowBlock (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  fun i j =>
    (if i = j then diagonalLow p i else 0) -
      wPrime * primeShiftMatrix p i j +
      lowChannelOuterProduct p i j

/-- Candidate scalar-denominator Schur formula transcribed from the verifier.
Lean's division is total; an operator interpretation requires a separate proof
that `candidateHighFloor p` is a valid nonzero high-block lower bound. -/
def schurFormula (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  fun i j => lowBlock p i j - xStarX p i j / candidateHighFloor p

def alpha0 : ℝ := 1 / 2

def channelWeight (p : Parity) : ℝ :=
  2 / (Real.exp (alpha0 * R) - p.sign)

def scale0 (p : Parity) : ℝ := Real.sqrt (channelWeight p)

def bLow (p : Parity) (i : LowIndex) : ℝ :=
  channelLowMatrix p i 0 / scale0 p

def bNormSquared : Parity → ℝ
  | .even => R / 2 + Real.sinh (R / 2)
  | .odd => Real.sinh (R / 2) - R / 2

def bLowSquared (p : Parity) : ℝ :=
  ∑ i : LowIndex, bLow p i * bLow p i

/-- Candidate squared norm of the discarded channel component. Its positivity
is an explicit future analytic obligation. -/
def candidateBHighSquared (p : Parity) : ℝ :=
  bNormSquared p - bLowSquared p

def fullChannelB (p : Parity) (j : ChannelIndex) : ℝ :=
  channelGramMatrix p j 0 / scale0 p

def fullShiftB (p : Parity) (i : LowIndex) : ℝ :=
  channelShiftMatrix p 0 i / scale0 p

def lowChannelB (p : Parity) (j : ChannelIndex) : ℝ :=
  ∑ i : LowIndex, channelLowMatrix p i j * bLow p i

def lowShiftB (p : Parity) (i : LowIndex) : ℝ :=
  ∑ k : LowIndex, primeShiftMatrix p i k * bLow p k

def xStarBHigh (p : Parity) (i : LowIndex) : ℝ :=
  (∑ j : ChannelIndex,
      channelLowMatrix p i j *
        (fullChannelB p j - lowChannelB p j)) -
    wPrime * (fullShiftB p i - lowShiftB p i)

def candidateRankOneVector (p : Parity) (i : LowIndex) : ℝ :=
  bLow p i - xStarBHigh p i / candidateHighFloor p

/-- Candidate pole denominator. No nonzeroness theorem is asserted here. -/
def candidateHighPoleDenominator (p : Parity) : ℝ :=
  candidateHighFloor p + p.poleCoefficient * candidateBHighSquared p

/-- Candidate effective rank-one coefficient; its intended reduction requires
a separate nonzero-denominator and operator-order argument. -/
def candidateEffectiveRankOne (p : Parity) : ℝ :=
  p.poleCoefficient * candidateHighFloor p / candidateHighPoleDenominator p

/-- Candidate finite lower-matrix formula. This definition does not identify
the formula with the localized Weil operator or prove any enclosure. -/
def finiteLowerFormula (p : Parity) : Matrix LowIndex LowIndex ℝ :=
  fun i j =>
    schurFormula p i j +
      candidateEffectiveRankOne p * candidateRankOneVector p i * candidateRankOneVector p j

/-- Even candidate finite formula on the certificate's 20-element index. -/
def evenFiniteLowerFormula : Matrix LowIndex LowIndex ℝ :=
  finiteLowerFormula .even

/-- Odd candidate finite formula on the certificate's 20-element index. -/
def oddFiniteLowerFormula : Matrix LowIndex LowIndex ℝ :=
  finiteLowerFormula .odd

theorem R_pos : 0 < R := Real.log_pos (by norm_num)

theorem H_pos : 0 < H := Real.log_pos (by norm_num)

theorem R_ne_zero : R ≠ 0 := ne_of_gt R_pos

theorem wPrime_pos : 0 < wPrime := by
  exact div_pos H_pos (Real.sqrt_pos.2 (by norm_num))

theorem alpha_pos (j : ℕ) : 0 < alpha j := by
  unfold alpha
  positivity

theorem alpha_injective : Function.Injective alpha := by
  intro j k h
  have hc : (j : ℝ) = (k : ℝ) := by
    unfold alpha at h
    linarith
  exact_mod_cast hc

theorem alpha_sub_ne_zero {j k : ℕ} (hjk : j ≠ k) :
    alpha j - alpha k ≠ 0 := by
  intro h
  apply hjk
  apply alpha_injective
  linarith

theorem channel_denominator_pos (n j : ℕ) :
    0 < alpha j ^ 2 + frequency n ^ 2 := by
  have ha2 : 0 < alpha j ^ 2 := sq_pos_of_pos (alpha_pos j)
  have hk2 : 0 ≤ frequency n ^ 2 := sq_nonneg (frequency n)
  linarith

theorem channel_denominator_ne_zero (n j : ℕ) :
    alpha j ^ 2 + frequency n ^ 2 ≠ 0 :=
  ne_of_gt (channel_denominator_pos n j)

theorem summable_aInfinitySummand (t : ℝ) :
    Summable (fun j : ℕ =>
      2 * t ^ 2 / (alpha j * (alpha j ^ 2 + t ^ 2))) := by
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift :
      Summable (fun j : ℕ => (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 3)) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      hp.comp_injective Nat.succ_injective
  have hbound :
      Summable (fun j : ℕ => 16 * t ^ 2 / (((j + 1 : ℕ) : ℝ) ^ 3)) := by
    have hm := hshift.mul_left (16 * t ^ 2)
    simpa only [div_eq_mul_inv, mul_assoc, one_mul] using hm
  apply Summable.of_nonneg_of_le (f := fun j : ℕ =>
      16 * t ^ 2 / (((j + 1 : ℕ) : ℝ) ^ 3))
  · intro j
    unfold alpha
    positivity
  · intro j
    unfold alpha
    rw [Nat.cast_add, Nat.cast_one]
    let x : ℝ := (j : ℝ)
    let a : ℝ := 2 * x + 1 / 2
    let b : ℝ := x + 1
    let d : ℝ := a * (a ^ 2 + t ^ 2)
    change 2 * t ^ 2 / d ≤ 16 * t ^ 2 / b ^ 3
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have ha : 0 < a := by dsimp [a]; positivity
    have hd : 0 < d := by dsimp [d]; positivity
    have hba : b ≤ 2 * a := by
      dsimp [a, b]
      nlinarith
    have hcube : b ^ 3 ≤ (2 * a) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hb) hba 3
    have had : a ^ 3 ≤ d := by
      dsimp [d]
      calc
        a ^ 3 = a * a ^ 2 := by ring
        _ ≤ a * (a ^ 2 + t ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith [sq_nonneg t]
          · exact le_of_lt ha
    have hbd : b ^ 3 ≤ 8 * d := by
      calc
        b ^ 3 ≤ (2 * a) ^ 3 := hcube
        _ = 8 * a ^ 3 := by ring
        _ ≤ 8 * d := mul_le_mul_of_nonneg_left had (by norm_num)
    rw [div_le_div_iff₀ hd (pow_pos hb 3)]
    have ht : (0 : ℝ) ≤ 2 * t ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg t)
    have hs := mul_le_mul_of_nonneg_left hbd ht
    calc
      2 * t ^ 2 * b ^ 3 ≤ 2 * t ^ 2 * (8 * d) := hs
      _ = 16 * t ^ 2 * d := by ring
  · exact hbound

theorem channel_radicand_pos (p : Parity) (j : ℕ) :
    0 < 1 - p.sign * Real.exp (-alpha j * R) := by
  cases p with
  | even =>
      simp only [Parity.sign_even, one_mul]
      rw [sub_pos, ← Real.exp_zero]
      apply Real.exp_lt_exp.mpr
      nlinarith [alpha_pos j, R_pos]
  | odd =>
      simp only [Parity.sign_odd, neg_mul, sub_neg_eq_add]
      positivity

theorem alpha0_pos : 0 < alpha0 := by norm_num [alpha0]

theorem exp_alpha0R_gt_one : 1 < Real.exp (alpha0 * R) := by
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  exact mul_pos alpha0_pos R_pos

theorem channelWeight_pos (p : Parity) : 0 < channelWeight p := by
  cases p with
  | even =>
      simp only [channelWeight, Parity.sign_even]
      exact div_pos (by norm_num) (sub_pos.mpr exp_alpha0R_gt_one)
  | odd =>
      simp only [channelWeight, Parity.sign_odd, sub_neg_eq_add]
      positivity

theorem scale0_pos (p : Parity) : 0 < scale0 p :=
  Real.sqrt_pos.2 (channelWeight_pos p)

theorem scale0_ne_zero (p : Parity) : scale0 p ≠ 0 :=
  ne_of_gt (scale0_pos p)

theorem aInfinityMode_zero : aInfinityMode 0 = 0 := by
  simp [aInfinityMode, frequency]

theorem odd_channel_sign (n j : ℕ) :
    channelLowCoefficient .odd n j =
      let a := alpha j
      let q := Real.exp (-a * R)
      let k := frequency n
      (-basisNorm n) * Real.sqrt 2 * a * Real.sqrt (1 + q) /
        (a ^ 2 + k ^ 2) := by
  simp [channelLowCoefficient, Parity.sign]

theorem lowBlock_entry (p : Parity) (i j : LowIndex) :
    lowBlock p i j =
      (if i = j then diagonalLow p i else 0) -
        wPrime * primeShiftMatrix p i j +
        lowChannelOuterProduct p i j := rfl

/-- The signed prime term remains explicit in the common low-block formula. -/
theorem schurFormula_entry (p : Parity) (i j : LowIndex) :
    schurFormula p i j =
      lowBlock p i j - xStarX p i j / candidateHighFloor p := rfl

theorem finiteLowerFormula_entry (p : Parity) (i j : LowIndex) :
    finiteLowerFormula p i j =
      schurFormula p i j +
        candidateEffectiveRankOne p * candidateRankOneVector p i * candidateRankOneVector p j := rfl

end RiemannResearch.RH.Log3FiniteMatrixFormula
