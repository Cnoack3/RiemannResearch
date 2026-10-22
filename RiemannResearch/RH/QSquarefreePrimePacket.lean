/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.QCovarianceScreening
import RiemannResearch.RH.QSquarefreeInverseCapacity
import RiemannResearch.Analysis.FiniteGramScreenedCapacity
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-!
# Prime-adjunction packets for actual squarefree Q approximants

Source: user-provided primorial cofinality research agenda, 16 October 2026,
Sections 7--8. For an actual primorial L and a prime p not dividing L, the
new conductors are exactly the disjoint old divisors and the packet p*d
for every d dividing L, including d=1. The signed Q source and covariance
are screened against the complete old centered family. These finite
identities do not provide an accumulated-gain lower bound.
-/

namespace Nat

/-- Exact arithmetic divisor partition; primality alone gives the union,
while freshness is used separately for its disjointness. -/
theorem divisor_prime_mul_partition (L p d : ℕ) (hL : 0 < L) (hp : p.Prime) :
    (1 < d ∧ d ∣ p * L) ↔
      (1 < d ∧ d ∣ L) ∨ ∃ a, a ∣ L ∧ d = p * a := by
  constructor
  · rintro ⟨hd, hdiv⟩
    by_cases hpd : p ∣ d
    · obtain ⟨a, rfl⟩ := hpd
      exact Or.inr ⟨a, (Nat.mul_dvd_mul_iff_left hp.pos).mp hdiv, rfl⟩
    · left
      refine ⟨hd, ?_⟩
      have hcop : p.Coprime d := hp.coprime_iff_not_dvd.mpr hpd
      exact hcop.symm.dvd_mul_left.mp hdiv
  · rintro (⟨hd, hdiv⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨hd, dvd_mul_of_dvd_right hdiv p⟩
    · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hL
      exact ⟨lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p ha0),
        Nat.mul_dvd_mul_left p ha⟩

end Nat

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreePrimePacket

open ZetaTwoHilbert ZetaTwoProbability QCovarianceInverse QCovarianceInvertibility
open QSquarefreePrimorialCofinality QCovarianceScreening
open Pareto.SquarefreeStageExhaustion

/-- The packet includes the divisor one, which supplies the newly adjoined prime. -/
def PacketIndex (n : ℕ) := ↥((primorialPeriod n).divisors)

instance (n : ℕ) : Fintype (PacketIndex n) := by
  unfold PacketIndex
  infer_instance

instance (n : ℕ) : DecidableEq (PacketIndex n) := by
  unfold PacketIndex
  infer_instance

def packetConductor (n p : ℕ) (j : PacketIndex n) : ℕ := p * j.val

def adjoinedConductor (n p : ℕ) : DivisorIndex n ⊕ PacketIndex n → ℕ :=
  Sum.elim (divisorConductor n) (packetConductor n p)

theorem packetConductor_gt_one (n p : ℕ) (hp : p.Prime) (j : PacketIndex n) :
    1 < packetConductor n p j := by
  have hd : j.val ∣ primorialPeriod n := (Nat.mem_divisors.mp j.property).1
  have hj : 0 < j.val := Nat.pos_of_dvd_of_pos hd (primorialPeriod_pos n)
  exact lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p hj)

theorem packetConductor_injective (n p : ℕ) (hp : p.Prime) :
    Function.Injective (packetConductor n p) := by
  intro i j h
  apply Subtype.ext
  exact Nat.eq_of_mul_eq_mul_left hp.pos h

/-- Freshness makes the arithmetic old/new divisor partition disjoint. -/
theorem adjoinedConductor_injective (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) : Function.Injective (adjoinedConductor n p) := by
  apply Sum.elim_injective.mpr
  refine ⟨divisorConductor_injective n, packetConductor_injective n p hp, ?_⟩
  intro i j he
  apply hfresh
  have hpi : p ∣ divisorConductor n i := by
    rw [he]
    exact dvd_mul_right p j.val
  exact dvd_trans hpi (Nat.mem_divisors.mp i.property.1).1

theorem adjoinedConductor_gt_one (n p : ℕ) (hp : p.Prime)
    (k : DivisorIndex n ⊕ PacketIndex n) : 1 < adjoinedConductor n p k := by
  cases k with
  | inl i => exact divisorConductor_gt_one n i
  | inr j => exact packetConductor_gt_one n p hp j

theorem mem_range_adjoinedConductor (n p d : ℕ) (hp : p.Prime) :
    d ∈ Set.range (adjoinedConductor n p) ↔
      1 < d ∧ d ∣ p * primorialPeriod n := by
  rw [Nat.divisor_prime_mul_partition _ _ _ (primorialPeriod_pos n) hp]
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | inl i => exact Or.inl ⟨i.property.2, (Nat.mem_divisors.mp i.property.1).1⟩
    | inr j =>
      exact Or.inr ⟨j.val, (Nat.mem_divisors.mp j.property).1, rfl⟩
  · rintro (hi | ⟨a, ha, rfl⟩)
    · exact ⟨Sum.inl ⟨d, Nat.mem_divisors.mpr
        ⟨hi.2, Nat.ne_of_gt (primorialPeriod_pos n)⟩, hi.1⟩, rfl⟩
    · exact ⟨Sum.inr ⟨a, Nat.mem_divisors.mpr
        ⟨ha, Nat.ne_of_gt (primorialPeriod_pos n)⟩⟩, rfl⟩

def adjoinedStage (n p : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range fun k => qResidue (adjoinedConductor n p k))

/-- This is the entire divisor span of p*L, not a smaller prime-only span. -/
theorem adjoinedStage_eq_divisorSpan (n p : ℕ) (hp : p.Prime) :
    adjoinedStage n p =
      Submodule.span ℝ {f | ∃ d : ℕ,
        1 < d ∧ d ∣ p * primorialPeriod n ∧ f = qResidue d} := by
  apply congrArg (Submodule.span ℝ)
  ext f
  constructor
  · rintro ⟨k, rfl⟩
    have hk := (mem_range_adjoinedConductor n p _ hp).mp ⟨k, rfl⟩
    exact ⟨adjoinedConductor n p k, hk.1, hk.2, rfl⟩
  · rintro ⟨d, hd, hdiv, rfl⟩
    obtain ⟨k, hk⟩ := (mem_range_adjoinedConductor n p d hp).mpr ⟨hd, hdiv⟩
    exact ⟨k, congrArg qResidue hk⟩

def packetMean (n p : ℕ) : PacketIndex n → ℝ :=
  screenedMean (divisorConductor n) (packetConductor n p)
    (divisorConductor_gt_one n) (divisorConductor_injective n)

def packetCovariance (n p : ℕ) : Matrix (PacketIndex n) (PacketIndex n) ℝ :=
  screenedCovariance (divisorConductor n) (packetConductor n p)
    (divisorConductor_gt_one n) (divisorConductor_injective n)

def packetInverseSource (n p : ℕ) : PacketIndex n → ℝ :=
  (packetCovariance n p)⁻¹.mulVec (packetMean n p)

def packetGain (n p : ℕ) : ℝ :=
  dotProduct (packetMean n p) (packetInverseSource n p)

def adjoinedCapacity (n p : ℕ) : ℝ :=
  covarianceInformation (adjoinedConductor n p)

theorem packetMean_eq_screened_source (n p : ℕ) :
    packetMean n p = qMean (packetConductor n p) -
      (crossCovariance (divisorConductor n) (packetConductor n p)).transpose.mulVec
        (covarianceInverseSource (divisorConductor n)) :=
  screenedMean_eq_sub _ _ _ _

theorem packetCovariance_eq_schur (n p : ℕ) :
    packetCovariance n p = residueCovarianceMatrix (packetConductor n p) -
      (crossCovariance (divisorConductor n) (packetConductor n p)).transpose *
        (residueCovarianceMatrix (divisorConductor n))⁻¹ *
          crossCovariance (divisorConductor n) (packetConductor n p) :=
  screenedCovariance_eq_schur _ _ _ _

theorem packetCovariance_posDef (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) : (packetCovariance n p).PosDef :=
  screenedCovariance_posDef _ _ (divisorConductor_gt_one n)
    (divisorConductor_injective n) (packetConductor_gt_one n p hp)
    (adjoinedConductor_injective n p hp hfresh)

/-- The agenda's exact prime-packet gain for the actual primorial old stage. -/
theorem adjoinedCapacity_sub_primorialCapacity (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) :
    adjoinedCapacity n p - primorialCapacity n = packetGain n p := by
  rw [primorialCapacity_eq_covarianceInformation]
  exact covarianceInformation_gain _ _ (divisorConductor_gt_one n)
    (divisorConductor_injective n) (packetConductor_gt_one n p hp)
    (adjoinedConductor_injective n p hp hfresh)

/-- Exact old/new inverse-covariance coefficients, before normalization. -/
theorem adjoinedInverseSource_blocks (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) :
    covarianceInverseSource (adjoinedConductor n p) =
      Sum.elim
        (fun i => covarianceInverseSource (divisorConductor n) i -
          ∑ j, packetInverseSource n p j *
            projectionCoefficients (divisorConductor n) (packetConductor n p) j i)
        (packetInverseSource n p) :=
  covarianceInverseSource_blocks _ _ (divisorConductor_gt_one n)
    (divisorConductor_injective n) (packetConductor_gt_one n p hp)
    (adjoinedConductor_injective n p hp hfresh)

/-- The actual legal least-squares error after adjoining the prime packet. -/
theorem adjoined_error_eq_reciprocal (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) :
    ‖qOne - qSynthesis (adjoinedConductor n p)
      (fun k => covarianceInverseSource (adjoinedConductor n p) k /
        (1 + adjoinedCapacity n p))‖ ^ 2 = 1 / (1 + adjoinedCapacity n p) :=
  qError_genuine_inverse _ (adjoinedConductor_gt_one n p hp)
    (adjoinedConductor_injective n p hp hfresh)

theorem adjoinedPeriod_squarefree (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) : Squarefree (p * primorialPeriod n) :=
  Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hfresh, hp.squarefree, primorialPeriod_squarefree n⟩

theorem adjoinedStage_le_squarefreeSpan (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) :
    adjoinedStage n p ≤ qSquarefreeCRTSpan := by
  rw [adjoinedStage_eq_divisorSpan n p hp]
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, hdvd, rfl⟩
  have hsf := (adjoinedPeriod_squarefree n p hp hfresh).squarefree_of_dvd hdvd
  exact Submodule.subset_span ⟨⟨d, by omega, hsf⟩, rfl⟩

/-- Exact residual correlation; the screened source is not replaced by an unsigned mean. -/
theorem packetMean_eq_residual_correlation (n p : ℕ) (j : PacketIndex n) :
    packetMean n p j =
      (1 + primorialCapacity n) *
        inner ℝ (qOne - primorialOptimizer n) (qResidue (packetConductor n p j)) := by
  have h := screenedMean_eq_residual_correlation (divisorConductor n)
    (packetConductor n p) (divisorConductor_gt_one n) (divisorConductor_injective n) j
  change packetMean n p j = (1 + covarianceInformation (divisorConductor n)) *
    inner ℝ (qOne - divisorCandidate n) (qResidue (packetConductor n p j)) at h
  rwa [divisorCandidate_eq_primorialOptimizer,
    ← primorialCapacity_eq_covarianceInformation] at h

theorem packetMean_sq_le_gain_mul_diagonal (n p : ℕ) (hp : p.Prime)
    (hfresh : ¬p ∣ primorialPeriod n) (j : PacketIndex n) :
    packetMean n p j ^ 2 ≤ packetGain n p * packetCovariance n p j j := by
  have h := screenedMean_sq_le_gain_mul_diagonal
    (divisorConductor n) (packetConductor n p)
    (divisorConductor_gt_one n) (divisorConductor_injective n)
    (packetConductor_gt_one n p hp) (adjoinedConductor_injective n p hp hfresh) j
  change packetMean n p j ^ 2 ≤
    (adjoinedCapacity n p - covarianceInformation (divisorConductor n)) *
      packetCovariance n p j j at h
  rwa [← primorialCapacity_eq_covarianceInformation,
    adjoinedCapacity_sub_primorialCapacity n p hp hfresh] at h

theorem fresh_iff_cutoff_lt (n p : ℕ) (hp : p.Prime) :
    ¬p ∣ primorialPeriod n ↔ n + 3 < p := by
  rw [primorialPeriod, hp.dvd_primorial_iff, not_le]

theorem primorialPeriod_prime_step (n : ℕ) (hp : (n + 4).Prime) :
    primorialPeriod (n + 1) = (n + 4) * primorialPeriod n := by
  simpa [primorialPeriod, Nat.add_assoc, Finset.filter_singleton, hp, mul_comm] using
    (primorial_add (n + 3) 1)

theorem primorialPeriod_composite_step (n : ℕ) (hp : ¬(n + 4).Prime) :
    primorialPeriod (n + 1) = primorialPeriod n := by
  simpa [primorialPeriod, Nat.add_assoc, Finset.filter_singleton, hp] using
    (primorial_add (n + 3) 1)

theorem cutoff_prime_fresh (n : ℕ) (hp : (n + 4).Prime) :
    ¬(n + 4) ∣ primorialPeriod n :=
  (fresh_iff_cutoff_lt n (n + 4) hp).mpr (by omega)

theorem adjoinedStage_eq_next (n : ℕ) (hp : (n + 4).Prime) :
    adjoinedStage n (n + 4) = primorialStage (n + 1) := by
  rw [adjoinedStage_eq_divisorSpan n (n + 4) hp, primorialStage,
    primorialPeriod_prime_step n hp]

def toNextIndex (n : ℕ) (hp : (n + 4).Prime)
    (k : DivisorIndex n ⊕ PacketIndex n) : DivisorIndex (n + 1) :=
  ⟨adjoinedConductor n (n + 4) k,
    Nat.mem_divisors.mpr ⟨by
      rw [primorialPeriod_prime_step n hp]
      exact ((mem_range_adjoinedConductor n (n + 4) _ hp).mp ⟨k, rfl⟩).2,
      Nat.ne_of_gt (primorialPeriod_pos (n + 1))⟩,
    adjoinedConductor_gt_one n (n + 4) hp k⟩

theorem toNextIndex_bijective (n : ℕ) (hp : (n + 4).Prime) :
    Function.Bijective (toNextIndex n hp) := by
  constructor
  · intro i j h
    apply adjoinedConductor_injective n (n + 4) hp (cutoff_prime_fresh n hp)
    exact congrArg Subtype.val h
  · intro i
    have hdvd : i.val ∣ (n + 4) * primorialPeriod n := by
      rw [← primorialPeriod_prime_step n hp]
      exact (Nat.mem_divisors.mp i.property.1).1
    obtain ⟨k, hk⟩ :=
      (mem_range_adjoinedConductor n (n + 4) i.val hp).mpr ⟨i.property.2, hdvd⟩
    exact ⟨k, Subtype.ext hk⟩

def equivToNext (n : ℕ) (hp : (n + 4).Prime) :
    DivisorIndex n ⊕ PacketIndex n ≃ DivisorIndex (n + 1) :=
  Equiv.ofBijective (toNextIndex n hp) (toNextIndex_bijective n hp)

theorem adjoinedCapacity_eq_next (n : ℕ) (hp : (n + 4).Prime) :
    adjoinedCapacity n (n + 4) = primorialCapacity (n + 1) := by
  rw [primorialCapacity_eq_covarianceInformation]
  exact covarianceInformation_comp_equiv (equivToNext n hp) (divisorConductor (n + 1))
    (divisorConductor_gt_one (n + 1)) (divisorConductor_injective (n + 1))

theorem primorialCapacity_prime_step (n : ℕ) (hp : (n + 4).Prime) :
    primorialCapacity (n + 1) - primorialCapacity n = packetGain n (n + 4) := by
  rw [← adjoinedCapacity_eq_next n hp]
  exact adjoinedCapacity_sub_primorialCapacity n (n + 4) hp (cutoff_prime_fresh n hp)

theorem primorialCapacity_composite_step (n : ℕ) (hp : ¬(n + 4).Prime) :
    primorialCapacity (n + 1) = primorialCapacity n := by
  have hstage : primorialStage (n + 1) = primorialStage n := by
    simp only [primorialStage, primorialPeriod_composite_step n hp]
  simp only [primorialCapacity, primorialError, primorialOptimizer, hstage]

/-- The genuine cutoff increment: a full prime packet, or zero at a composite cutoff. -/
def cutoffGain (n : ℕ) : ℝ :=
  if (n + 4).Prime then packetGain n (n + 4) else 0

theorem primorialCapacity_step (n : ℕ) :
    primorialCapacity (n + 1) = primorialCapacity n + cutoffGain n := by
  by_cases hp : (n + 4).Prime
  · have h := primorialCapacity_prime_step n hp
    simp only [cutoffGain, if_pos hp]
    linarith
  · simp only [cutoffGain, if_neg hp, add_zero]
    exact primorialCapacity_composite_step n hp

/-- The complete accumulated signed-source quadratic gains, with the initial capacity retained. -/
theorem primorialCapacity_eq_initial_add_sum (N : ℕ) :
    primorialCapacity N = primorialCapacity 0 + ∑ n ∈ Finset.range N, cutoffGain n :=
  RiemannResearch.Analysis.FiniteGramCapacity.capacity_telescope
    primorialCapacity cutoffGain primorialCapacity_step N

/-- Conditional consumer only: divergence of the actual gains remains an open arithmetic premise. -/
theorem riemannHypothesis_of_packetGain_sum_tendsto
    (h : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, cutoffGain n)
      Filter.atTop Filter.atTop) : RiemannHypothesis := by
  apply QSquarefreeInverseCapacity.riemannHypothesis_of_inverseCapacity_tendsto
  apply primorialCapacity_tendsto_iff_exhaustive.mp
  have hzero : 0 ≤ primorialCapacity 0 := by
    rw [primorialCapacity_eq_covarianceInformation]
    exact qInformation_nonneg _ _ (covarianceInverseSource_normal _
      (divisorConductor_gt_one 0) (divisorConductor_injective 0))
  apply Filter.tendsto_atTop_mono (fun N => ?_) h
  rw [primorialCapacity_eq_initial_add_sum]
  linarith

end RiemannResearch.RH.QSquarefreePrimePacket
