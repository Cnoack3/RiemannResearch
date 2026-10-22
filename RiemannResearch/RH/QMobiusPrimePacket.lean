/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreePrimePacket
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.QMobiusPrimePacketArithmetic
import RiemannResearch.RH.QCovarianceTrial
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Fintype.BigOperators

/-!
# Actual Möbius-weighted primorial packets

Source: user-provided QSquarefreePrimePacketResearch20261016 agenda,
16 October 2026. The arithmetic formula and signed screened trial are assembled
for the actual existing primorial stages. No divergence provider is assumed
or asserted; all quantitative conclusions are finite-stage statements.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QMobiusPrimePacket

open Pareto.SquarefreeStageExhaustion
open ZetaTwoHilbert ZetaTwoProbability QCovarianceInverse QCovarianceInvertibility
open QCovarianceScreening QCovarianceTrial
open QSquarefreePrimePacket QSquarefreePrimorialCofinality

def moebiusWeight (n : ℕ) (j : PacketIndex n) : ℝ :=
  ArithmeticFunction.moebius j.val

def moebiusPacket (n p : ℕ) : QHilbert :=
  qSynthesis (packetConductor n p) (moebiusWeight n)

def moebiusSource (n p : ℕ) : ℝ :=
  trialSource (divisorConductor n) (packetConductor n p)
    (divisorConductor_gt_one n) (divisorConductor_injective n) (moebiusWeight n)

def moebiusEnergy (n p : ℕ) : ℝ :=
  trialEnergy (divisorConductor n) (packetConductor n p)
    (divisorConductor_gt_one n) (divisorConductor_injective n) (moebiusWeight n)

theorem moebiusWeight_ne_zero (n : ℕ) : moebiusWeight n ≠ 0 := by
  intro h
  let j : PacketIndex n :=
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt (primorialPeriod_pos n)⟩⟩
  have hj := congrFun h j
  simp [moebiusWeight, j] at hj

theorem moebiusPacket_physical (n p k : ℕ) :
    qSequence (moebiusPacket n p) k =
      arithmeticPacket (primorialPeriod n) p k := by
  change (qSequenceLinear (qSynthesis (packetConductor n p) (moebiusWeight n))) k = _
  rw [qSynthesis, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ j : PacketIndex n, moebiusWeight n j *
    qSequence (qResidue (packetConductor n p j)) k) = _
  simp only [qSequence_qResidue]
  simpa only [moebiusWeight, packetConductor, arithmeticPacket, PacketIndex] using
    (Finset.sum_coe_sort (primorialPeriod n).divisors
      (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) *
        ArithmeticCumulative.residueFraction (p * d) k))

theorem moebiusPacket_physical_eq_count (n p k : ℕ) (hp : 0 < p) :
    qSequence (moebiusPacket n p) k =
      (k:ℝ)*(Nat.totient (primorialPeriod n):ℝ)/
        ((p:ℝ)*(primorialPeriod n:ℝ)) -
          QPrimeSieve.coprimeCount (primorialPeriod n) (k/p) := by
  rw [moebiusPacket_physical]
  exact arithmeticPacket_eq_totient_count _ _ _ (ne_of_gt (primorialPeriod_pos n)) hp

theorem moebiusPacket_mem_squarefreeSpan (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) :
    moebiusPacket n p ∈ qSquarefreeCRTSpan := by
  apply adjoinedStage_le_squarefreeSpan n p hp hfresh
  unfold moebiusPacket qSynthesis
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨Sum.inr j, rfl⟩

theorem moebiusSource_eq_residual_pairing (n p : ℕ) :
    moebiusSource n p =
      (1 + primorialCapacity n) *
        inner ℝ (qOne - primorialOptimizer n) (moebiusPacket n p) := by
  have h := trialSource_eq_residual_pairing (divisorConductor n)
    (packetConductor n p) (divisorConductor_gt_one n)
    (divisorConductor_injective n) (moebiusWeight n)
  change moebiusSource n p =
    (1 + covarianceInformation (divisorConductor n)) *
      inner ℝ (qOne - divisorCandidate n) (moebiusPacket n p) at h
  rwa [divisorCandidate_eq_primorialOptimizer,
    ← primorialCapacity_eq_covarianceInformation] at h

theorem moebiusEnergy_pos (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) :
    0 < moebiusEnergy n p :=
  trialEnergy_pos (divisorConductor n) (packetConductor n p)
    (divisorConductor_gt_one n) (divisorConductor_injective n)
    (packetConductor_gt_one n p hp) (adjoinedConductor_injective n p hp hfresh)
    (moebiusWeight n) (moebiusWeight_ne_zero n)

theorem moebius_trial_lower_bound (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) :
    moebiusSource n p ^ 2 / moebiusEnergy n p ≤ packetGain n p := by
  have h := trial_lower_bound (divisorConductor n) (packetConductor n p)
    (divisorConductor_gt_one n) (divisorConductor_injective n)
    (packetConductor_gt_one n p hp) (adjoinedConductor_injective n p hp hfresh)
    (moebiusWeight n) (moebiusWeight_ne_zero n)
  change moebiusSource n p ^ 2 / moebiusEnergy n p ≤
    adjoinedCapacity n p - covarianceInformation (divisorConductor n) at h
  rwa [← primorialCapacity_eq_covarianceInformation,
    adjoinedCapacity_sub_primorialCapacity n p hp hfresh] at h

/-- Finite quantitative consumer; the arithmetic estimates remain explicit. -/
theorem moebius_gain_lower_of_bounds (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) (a e : ℝ) (he : 0 < e)
    (hsource : a ^ 2 ≤ moebiusSource n p ^ 2)
    (henergy : moebiusEnergy n p ≤ e) :
    a ^ 2 / e ≤ packetGain n p := by
  have hE := moebiusEnergy_pos n p hp hfresh
  have htrial := moebius_trial_lower_bound n p hp hfresh
  have hgain : 0 ≤ packetGain n p :=
    (div_nonneg (sq_nonneg _) hE.le).trans htrial
  have hprod := (div_le_iff₀ hE).mp htrial
  apply (div_le_iff₀ he).mpr
  exact hsource.trans
    (hprod.trans (mul_le_mul_of_nonneg_left henergy hgain))

end RiemannResearch.RH.QMobiusPrimePacket
