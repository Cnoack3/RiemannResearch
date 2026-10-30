/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTTrialCertificate
import RiemannResearch.RH.QCRTDensePrimeSupport
import Mathlib.NumberTheory.Primorial
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QCRTPrimeInnovation
import RiemannResearch.RH.QCRTInnovationBlock
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QCRTMovingPredictionGain
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.OrthogonalObservationInnovation

/-!
# Full arithmetic coordinates for a new prime conductor block

Source: the user-provided full-squarefree research handoff of 30 October 2026,
priority 1. Every old divisor, including 1, is retained. Exact source and Gram
transport preserves all floor/prime cross terms and the head correction.
These finite identities do not assert a favorable inverse-Gram spectrum or
a cumulative arithmetic budget.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTDivisorBlock
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTInnovationGain QSquarefreeEnergyTransitions QCRTPrimeInnovation
open QCRTInnovationBlock QCRTTrialCertificate QCRTMovingPredictionGain
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.OrthogonalObservationInnovation

/-- All newly admitted conductors are multiplied by the single new prime. -/
theorem dense_primorial_eq_of_prime (i : ℕ) (hp : Nat.Prime (2 * i + 3)) :
    primorial (denseSchedule (i + 1) + 2) = (2 * i + 3) * oldPeriod i := by
  have he : ¬ Nat.Prime (2 * i + 4) := by
    intro hh
    rcases hh.eq_two_or_odd with hh | hh <;> omega
  have hn : 2 * i + 3 ∉ (2 * i + 2).primesLE := by
    intro h
    have := (Nat.mem_primesLE.mp h).1
    omega
  have hset : (denseSchedule (i + 1) + 2).primesLE =
      insert (2 * i + 3) (2 * i + 2).primesLE := by
    rw [show denseSchedule (i + 1) + 2 = (2 * i + 3) + 1 by
      dsimp [denseSchedule]; omega]
    rw [Nat.primesLE_succ, if_neg (by convert he using 1)]
    conv_lhs => rw [show 2 * i + 3 = (2 * i + 2) + 1 by omega]
    rw [Nat.primesLE_succ, if_pos (by convert hp using 1)]
  change primorial (denseSchedule (i + 1) + 2) =
    (2 * i + 3) * primorial (2 * i + 2)
  rw [primorial_eq_prod_primesLE, hset, Finset.prod_insert hn]
  rw [primorial_eq_prod_primesLE]

theorem new_prime_not_dvd_old (i : ℕ) (hp : Nat.Prime (2 * i + 3)) :
    ¬ (2 * i + 3) ∣ oldPeriod i := by
  intro h
  have := hp.dvd_primorial_iff.mp h
  dsimp [denseSchedule] at this
  omega

theorem prime_mul_mem_added (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (d : ℕ) (hd : d ∈ (oldPeriod i).divisors) :
    (2 * i + 3) * d ∈ addedConductors i := by
  have hdL := (Nat.mem_divisors.mp hd).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdL (primorial_pos _)
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, primorial_ne_zero _⟩, ?_⟩
    · rw [dense_primorial_eq_of_prime i hp]
      exact Nat.mul_dvd_mul_left _ hdL
    · have := hp.two_le
      nlinarith
  · intro hm
    have hmL := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm).1).1
    exact new_prime_not_dvd_old i hp ((dvd_mul_right _ _).trans hmL)

theorem added_eq_prime_mul (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (e : ℕ) (he : e ∈ addedConductors i) :
    ∃ d ∈ (oldPeriod i).divisors, e = (2 * i + 3) * d := by
  have hn := Finset.mem_sdiff.mp he
  have hnew := Finset.mem_filter.mp hn.1
  have hdiv := (Nat.mem_divisors.mp hnew.1).1
  rw [dense_primorial_eq_of_prime i hp] at hdiv
  have hold : ¬ e ∣ oldPeriod i := by
    intro hd
    exact hn.2 (Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hd, primorial_ne_zero _⟩, hnew.2⟩)
  have hpe : (2 * i + 3) ∣ e := by
    by_contra h
    have hc := (hp.coprime_iff_not_dvd.mpr h).symm
    exact hold (hc.dvd_of_dvd_mul_left hdiv)
  obtain ⟨d, rfl⟩ := hpe
  exact ⟨d, Nat.mem_divisors.mpr
    ⟨(Nat.mul_dvd_mul_iff_left hp.pos).mp hdiv, primorial_ne_zero _⟩, rfl⟩

/-- Includes d=1, which represents the compensated-prime direction. -/
def primeDivisorEquiv (i : ℕ) (hp : Nat.Prime (2 * i + 3)) :
    ↥((oldPeriod i).divisors) ≃ ↥(addedConductors i) :=
  Equiv.ofBijective
    (fun d => ⟨(2 * i + 3) * d.1, prime_mul_mem_added i hp d.1 d.2⟩)
    (by
      constructor
      · intro d e h
        apply Subtype.ext
        exact mul_left_cancel₀ hp.ne_zero (congrArg Subtype.val h)
      · intro e
        obtain ⟨d, hd, hde⟩ := added_eq_prime_mul i hp e.1 e.2
        exact ⟨⟨d, hd⟩, Subtype.ext hde.symm⟩)

@[simp] theorem primeDivisorEquiv_val (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (d : ↥((oldPeriod i).divisors)) :
    (primeDivisorEquiv i hp d).val = (2 * i + 3) * d.val := rfl

@[simp] theorem blockFamily_primeDivisorEquiv (i : ℕ)
    (hp : Nat.Prime (2 * i + 3)) (d : ↥((oldPeriod i).divisors)) :
    blockFamily i (primeDivisorEquiv i hp d) = screenedDirection i d := rfl

/-- Literal full-source transport; no off-diagonal matrix terms are discarded. -/
theorem trialCertificate_divisor_coordinates (i : ℕ)
    (hp : Nat.Prime (2 * i + 3)) (t : addedConductors i → ℝ) :
    trialCertificate i t = oldMismatch i ^ 2 / oldCapacity i -
      2 * (∑ d : ↥((oldPeriod i).divisors),
        t (primeDivisorEquiv i hp d) * jointSource i (primeDivisorEquiv i hp d)) +
      ∑ d : ↥((oldPeriod i).divisors),
        ∑ e : ↥((oldPeriod i).divisors),
          t (primeDivisorEquiv i hp d) *
            jointGram i (primeDivisorEquiv i hp d) (primeDivisorEquiv i hp e) *
            t (primeDivisorEquiv i hp e) := by
  classical
  have hs : dotProduct t (jointSource i) =
      ∑ d : ↥((oldPeriod i).divisors),
        t (primeDivisorEquiv i hp d) * jointSource i (primeDivisorEquiv i hp d) := by
    exact ((primeDivisorEquiv i hp).sum_comp (fun d => t d * jointSource i d)).symm
  have hq : dotProduct t ((jointGram i).mulVec t) =
      ∑ d : ↥((oldPeriod i).divisors),
        ∑ e : ↥((oldPeriod i).divisors),
          t (primeDivisorEquiv i hp d) *
            jointGram i (primeDivisorEquiv i hp d) (primeDivisorEquiv i hp e) *
            t (primeDivisorEquiv i hp e) := by
    simp only [dotProduct, Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    rw [← (primeDivisorEquiv i hp).sum_comp
      (fun d => ∑ e, t d * (jointGram i d e * t e))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← (primeDivisorEquiv i hp).sum_comp
      (fun e => t (primeDivisorEquiv i hp d) *
        (jointGram i (primeDivisorEquiv i hp d) e * t e))]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [trialCertificate, hs, hq]

end RiemannResearch.RH.QCRTDivisorBlock

namespace RiemannResearch.RH.QCRTDivisorBlock
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTInnovationGain QSquarefreeEnergyTransitions QCRTPrimeInnovation QCRTPeriodHeadBalance
open QCRTInnovationBlock QCRTTrialCertificate QCRTMovingPredictionGain QFloorDilation
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open scoped BigOperators

/-- The floor-dilated old residue after old-tangent screening. -/
def floorColumn (i d : ℕ) : QHilbert :=
  innovation (oldTangent i)
    (floorDilation (2 * i + 3) (by omega) (qResidue d))

/-- Physical observation retaining the compensated prime direction. -/
def divisorObservation (i d : ℕ) : ℝ :=
  qSequence (floorColumn i d) (i + 2) +
    (1 / (d : ℝ)) * qSequence (screenedDirection i 1) (i + 2)

/-- Actual optimizer source, including its signed observation correction. -/
def divisorSource (i d : ℕ) : ℝ :=
  inner ℝ (floorColumn i d) (minimumAt (denseSchedule i) (i + 1)) +
    (1 / (d : ℝ)) * inner ℝ (screenedDirection i 1)
      (minimumAt (denseSchedule i) (i + 1)) -
    oldMismatch i * divisorObservation i d / oldCapacity i

/-- All four floor/prime mixed terms and the rank-one head correction. -/
def divisorGram (i d e : ℕ) : ℝ :=
  inner ℝ (floorColumn i d) (floorColumn i e) +
    (1 / (e : ℝ)) * inner ℝ (floorColumn i d) (screenedDirection i 1) +
    (1 / (d : ℝ)) * inner ℝ (screenedDirection i 1) (floorColumn i e) +
    (1 / (d : ℝ)) * (1 / (e : ℝ)) * ‖screenedDirection i 1‖ ^ 2 +
    divisorObservation i d * divisorObservation i e / oldCapacity i

theorem observation_primeDivisorEquiv (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (d : ↥((oldPeriod i).divisors)) :
    observation i (primeDivisorEquiv i hp d) = divisorObservation i d := by
  have hd := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 (primorial_pos _)
  rw [observation, blockFamily_primeDivisorEquiv, screenedDirection_floor_block i d hd]
  change qSequenceLinear (floorColumn i d +
    (1 / (d.val : ℝ)) • screenedDirection i 1) (i + 2) = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem source_primeDivisorEquiv (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (d : ↥((oldPeriod i).divisors)) :
    jointSource i (primeDivisorEquiv i hp d) = divisorSource i d := by
  have hd := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 (primorial_pos _)
  rw [jointSource, cross, blockFamily_primeDivisorEquiv,
    screenedDirection_floor_block i d hd, observation_primeDivisorEquiv]
  simp only [inner_add_left, real_inner_smul_left]
  rfl

theorem gram_primeDivisorEquiv (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (d e : ↥((oldPeriod i).divisors)) :
    jointGram i (primeDivisorEquiv i hp d) (primeDivisorEquiv i hp e) =
      divisorGram i d e := by
  have hd := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 (primorial_pos _)
  have he := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp e.property).1 (primorial_pos _)
  simp only [jointGram, gramMatrix, blockFamily_primeDivisorEquiv,
    observation_primeDivisorEquiv, screenedDirection_floor_block i d hd,
    screenedDirection_floor_block i e he,
    inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq]
  change _ = divisorGram i d e
  unfold divisorGram floorColumn
  ring

/-- The complete adjusted trial expressed in the entire old divisor block.
This includes d=1 and all d,e cross terms. -/
theorem trialCertificate_arithmetic (i : ℕ)
    (hp : Nat.Prime (2 * i + 3)) (t : addedConductors i → ℝ) :
    trialCertificate i t = oldMismatch i ^ 2 / oldCapacity i -
      2 * (∑ d : ↥((oldPeriod i).divisors),
        t (primeDivisorEquiv i hp d) * divisorSource i d) +
      ∑ d : ↥((oldPeriod i).divisors),
        ∑ e : ↥((oldPeriod i).divisors),
          t (primeDivisorEquiv i hp d) * divisorGram i d e *
            t (primeDivisorEquiv i hp e) := by
  rw [trialCertificate_divisor_coordinates i hp t]
  simp only [source_primeDivisorEquiv, gram_primeDivisorEquiv]

end RiemannResearch.RH.QCRTDivisorBlock

namespace RiemannResearch.RH.QCRTDivisorBlock
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTInnovationGain QSquarefreeEnergyTransitions QCRTPrimeInnovation
open QCRTInnovationBlock QCRTTrialCertificate QCRTMovingPredictionGain QFloorDilation
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open scoped BigOperators

theorem addedConductors_empty_of_nonprime (i : ℕ)
    (hp : ¬ Nat.Prime (2 * i + 3)) : addedConductors i = ∅ := by
  simp [addedConductors, QCRTDensePrimeSupport.dense_primorial_eq_of_nonprime i hp,
    oldPeriod]

@[simp] theorem floorColumn_one (i : ℕ) : floorColumn i 1 = 0 := by
  simp [floorColumn, qResidue_one, innovation]

/-- Any divisor coefficient array becomes a trial on the complete added family. -/
def divisorTrial (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (u : ↥((oldPeriod i).divisors) → ℝ) : addedConductors i → ℝ :=
  fun e => u ((primeDivisorEquiv i hp).symm e)

@[simp] theorem divisorTrial_apply (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (u : ↥((oldPeriod i).divisors) → ℝ) (d : ↥((oldPeriod i).divisors)) :
    divisorTrial i hp u (primeDivisorEquiv i hp d) = u d := by
  simp [divisorTrial]

theorem divisorTrial_certificate (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (u : ↥((oldPeriod i).divisors) → ℝ) :
    trialCertificate i (divisorTrial i hp u) =
      oldMismatch i ^ 2 / oldCapacity i -
        2 * (∑ d : ↥((oldPeriod i).divisors), u d * divisorSource i d) +
        ∑ d : ↥((oldPeriod i).divisors), ∑ e : ↥((oldPeriod i).divisors),
          u d * divisorGram i d e * u e := by
  rw [trialCertificate_arithmetic i hp]
  simp only [divisorTrial_apply]

end RiemannResearch.RH.QCRTDivisorBlock
