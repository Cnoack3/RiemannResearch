/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.TwoDirectionTrial
import RiemannResearch.RH.QCRTScreenedFloorTrial
import RiemannResearch.RH.QCRTFullFloorTrial
import RiemannResearch.RH.QCRTDivisorBlock
import RiemannResearch.RH.QFloorDilationHeadEnergy
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QCRTTrialCertificate
import RiemannResearch.RH.QCRTPrimeInnovation
import RiemannResearch.RH.QCRTInnovationGain
import RiemannResearch.RH.QCRTInnovationBlock
import RiemannResearch.RH.QCRTPrimePairCertificate
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeEnergyTransitions
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.OrthogonalObservationInnovation
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertConstraints
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit mixed trials from the actual full-squarefree optimizer

Source: the user-provided full-squarefree dyadic agenda, priorities 1 and 2,
30 October 2026, together with the checked next-head screening transport.
Every divisor is retained; d=1 carries the compensated-prime correction.
The actual optimizer supplies the other direction.

Linear independence proves strict positivity of the exact two-dimensional
determinant, without a regularizer or an extra spectral hypothesis. The exact
mixed gain dominates the earlier head-refined raw gain. All unused full-family
loss squares and all intervening stages remain in the global certificate.
The arithmetic dyadic budget is still open.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTMixedFloorTrial
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace QSquarefreeAffineHead
open QCRTPeriodHeadBalance QSquarefreeEnergyTransitions QCRTPrimePairCertificate
open QCRTPrimeInnovation QCRTInnovationGain QCRTFullFloorTrial QFloorDilation
open QCRTTrialCertificate QCRTInnovationBlock QCRTDivisorBlock QCRTScreenedFloorTrial
open RiemannResearch.Analysis.OrthogonalObservationInnovation
open RiemannResearch.Analysis.FiniteHilbertGram

def divisorOne (i : ℕ) : ↥((oldPeriod i).divisors) :=
  ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, primorial_ne_zero _⟩⟩

def oldVector (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ) : QHilbert :=
  ∑ d, b d • qResidue d

def reciprocalSlope (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ) : ℝ :=
  ∑ d, b d / (d : ℕ)

def floorCoefficients (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ)
    (d : ↥((oldPeriod i).divisors)) : ℝ :=
  b d - if d = divisorOne i then reciprocalSlope i b else 0

def mixedCoefficients (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ) (α β : ℝ)
    (d : ↥((oldPeriod i).divisors)) : ℝ :=
  α * floorCoefficients i b d + if d = divisorOne i then β else 0

theorem oldVector_mem (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ) :
    oldVector i b ∈ divisorStage (oldPeriod i) := by
  exact (divisorStage _).sum_mem fun d _ =>
    (divisorStage _).smul_mem _ (Submodule.subset_span
      ⟨d, (Nat.mem_divisors.mp d.property).1, rfl⟩)

theorem exists_oldVector (i : ℕ) (f : QHilbert) (hf : f ∈ divisorStage (oldPeriod i)) :
    ∃ b : ↥((oldPeriod i).divisors) → ℝ, oldVector i b = f := by
  have hs : divisorStage (oldPeriod i) ≤
      Submodule.span ℝ (Set.range fun d : ↥((oldPeriod i).divisors) => qResidue d) := by
    apply Submodule.span_le.mpr
    rintro v ⟨d, hd, rfl⟩
    exact Submodule.subset_span
      ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, primorial_ne_zero _⟩⟩, rfl⟩
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hs hf)

theorem raw_sum (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ) :
    (∑ d : ↥((oldPeriod i).divisors), b d • rawDirection i d) =
      floorDilation (2 * i + 3) (by omega) (oldVector i b) +
        reciprocalSlope i b • rawDirection i 1 := by
  have hd (d : ↥((oldPeriod i).divisors)) : 0 < (d : ℕ) :=
    Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 (primorial_pos _)
  simp only [rawDirection_floor_block i _ (hd _), smul_add, smul_smul,
    Finset.sum_add_distrib, oldVector, map_sum, map_smul, reciprocalSlope, Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  ring


theorem prime_synthesis (i : ℕ) (a : ℝ) :
    (∑ d : ↥((oldPeriod i).divisors),
      (if d = divisorOne i then a else 0) • rawDirection i d) =
      a • rawDirection i 1 := by
  classical
  rw [Finset.sum_eq_single (divisorOne i)]
  · rfl
  · intro d hd hne
    simp only [if_neg hne, zero_smul]
  · simp

theorem floorCoefficients_raw (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ) :
    (∑ d : ↥((oldPeriod i).divisors), floorCoefficients i b d • rawDirection i d) =
      floorDilation (2 * i + 3) (by omega) (oldVector i b) := by
  classical
  simp only [floorCoefficients, sub_smul, Finset.sum_sub_distrib]
  rw [raw_sum, prime_synthesis, add_sub_cancel_right]

theorem mixedCoefficients_raw (i : ℕ) (b : ↥((oldPeriod i).divisors) → ℝ) (α β : ℝ) :
    (∑ d : ↥((oldPeriod i).divisors), mixedCoefficients i b α β d • rawDirection i d) =
      α • floorDilation (2 * i + 3) (by omega) (oldVector i b) +
        β • rawDirection i 1 := by
  classical
  simp only [mixedCoefficients, add_smul, Finset.sum_add_distrib, mul_smul,
    ← Finset.smul_sum, floorCoefficients_raw]
  congr 1
  exact prime_synthesis i β

theorem divisorTrial_raw (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (u : ↥((oldPeriod i).divisors) → ℝ) :
    (∑ e : addedConductors i, divisorTrial i hp u e • compensatedResidue e (oldPeriod i)) =
      ∑ d : ↥((oldPeriod i).divisors), u d • rawDirection i d := by
  rw [← (primeDivisorEquiv i hp).sum_comp]
  simp only [divisorTrial_apply]
  rfl

/-- The explicit full coefficient rule transports to screened floor plus prime. -/
theorem mixedSynthesis (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (b : ↥((oldPeriod i).divisors) → ℝ) (α β : ℝ) :
    Fintype.linearCombination ℝ (jointFamily i)
      (divisorTrial i hp (mixedCoefficients i b α β)) =
      α • screen i (floorDilation (2 * i + 3) (by omega) (oldVector i b)) +
        β • screen i (rawDirection i 1) := by
  rw [jointSynthesis_eq_screen i hi hsf, divisorTrial_raw, mixedCoefficients_raw]
  change innovationMap (nextTangent i) (_ + _) = _
  rw [map_add, map_smul, map_smul]
  rfl

theorem screenedPrime_ne_zero (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) : screen i (rawDirection i 1) ≠ 0 := by
  have h := (jointFamily_independent i).ne_zero (primeDivisorEquiv i hp (divisorOne i))
  rw [jointFamily_eq_screen i hi hsf] at h
  simpa only [primeDivisorEquiv_val, divisorOne, rawDirection, Nat.mul_one] using h


open RiemannResearch.Analysis.TwoDirectionTrial
open RiemannResearch.Analysis.FiniteHilbertConstraints

def selfFloor (i : ℕ) : QHilbert :=
  screen i (floorDilation (2 * i + 3) (by omega)
    (minimumAt (denseSchedule i) (i + 1)))

def primeColumn (i : ℕ) : QHilbert := screen i (rawDirection i 1)

def selfUpper (i : ℕ) : ℝ :=
  stageEnergy denseSchedule i / (2 * i + 3 : ℕ) - headBlockDefect (2 * i + 3) (i + 1)

theorem selfFloor_energy (i : ℕ) :
    ‖selfFloor i‖ ^ 2 = selfUpper i -
      tailBlockDefect (2 * i + 3) (i + 1) (minimumAt (denseSchedule i) (i + 1)) -
      ‖(nextTangent i).starProjection
        (floorDilation (2 * i + 3) (by omega)
          (minimumAt (denseSchedule i) (i + 1)))‖ ^ 2 := by
  rw [selfFloor, screen_energy, floorDilation_norm_sq_head_defect _ (i + 1) _ _
    (minimumAt_head _ _ (by dsimp [denseSchedule]; omega))]
  rfl

theorem selfFloor_energy_le (i : ℕ) : ‖selfFloor i‖ ^ 2 ≤ selfUpper i := by
  rw [selfFloor_energy]
  have ht := tailBlockDefect_nonneg (2 * i + 3) (i + 1) (by omega)
    (minimumAt (denseSchedule i) (i + 1))
  nlinarith [sq_nonneg ‖(nextTangent i).starProjection
    (floorDilation (2 * i + 3) (by omega) (minimumAt (denseSchedule i) (i + 1)))‖]

theorem selfUpper_pos (i : ℕ) : 0 < selfUpper i :=
  headAdjustedEnergy_pos (2 * i + 3) (i + 1) (by omega) (by omega)
    (minimumAt (denseSchedule i) (i + 1))
    (minimumAt_head _ _ (by dsimp [denseSchedule]; omega))

def mixedTrial (i : ℕ) (hp : Nat.Prime (2 * i + 3))
    (b : ↥((oldPeriod i).divisors) → ℝ) (A : ℝ) : addedConductors i → ℝ :=
  let B := inner ℝ (selfFloor i) (primeColumn i)
  let C := ‖primeColumn i‖ ^ 2
  let u := inner ℝ (headFirstMinimum i) (selfFloor i)
  let v := inner ℝ (headFirstMinimum i) (primeColumn i)
  divisorTrial i hp (mixedCoefficients i b (first A B C u v) (second A B C u v))

def mixedGain (i : ℕ) (A : ℝ) : ℝ :=
  gain A (inner ℝ (selfFloor i) (primeColumn i)) (‖primeColumn i‖ ^ 2)
    (inner ℝ (headFirstMinimum i) (selfFloor i))
    (inner ℝ (headFirstMinimum i) (primeColumn i))

def mixedFirst (i : ℕ) (A : ℝ) : ℝ :=
  first A (inner ℝ (selfFloor i) (primeColumn i)) (‖primeColumn i‖ ^ 2)
    (inner ℝ (headFirstMinimum i) (selfFloor i))
    (inner ℝ (headFirstMinimum i) (primeColumn i))

/-- Exact full-family certificate for an explicit two-direction rule.
The coefficient representation is provided for every old vector by exists_oldVector. -/
theorem mixed_certificate (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (b : ↥((oldPeriod i).divisors) → ℝ)
    (hb : oldVector i b = minimumAt (denseSchedule i) (i + 1)) (A : ℝ) :
    trialCertificate i (mixedTrial i hp b A) =
      headFirstCost i - mixedGain i A - (A - ‖selfFloor i‖ ^ 2) * mixedFirst i A ^ 2 := by
  have he := norm_completion (headFirstMinimum i) (selfFloor i) (primeColumn i) A
  dsimp only at he
  rw [trialCertificate_physical i hi hsf]
  dsimp only [mixedTrial]
  rw [mixedSynthesis i hi hsf hp, hb]
  change headFirstCost i - 2 * inner ℝ (headFirstMinimum i)
    (first A _ _ _ _ • selfFloor i + second A _ _ _ _ • primeColumn i) +
    ‖first A _ _ _ _ • selfFloor i + second A _ _ _ _ • primeColumn i‖ ^ 2 = _
  rw [norm_sub_sq_real] at he
  dsimp [mixedGain, mixedFirst, headFirstCost]
  linarith

/-- Signed increment with both the denominator defect and the exact
full-family approximation loss retained. -/
theorem mixed_step_completion (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (b : ↥((oldPeriod i).divisors) → ℝ)
    (hb : oldVector i b = minimumAt (denseSchedule i) (i + 1)) (A : ℝ) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      headFirstCost i - mixedGain i A - (A - ‖selfFloor i‖ ^ 2) * mixedFirst i A ^ 2 -
        ‖minimumVector (jointFamily_independent i) (jointSource i) -
          Fintype.linearCombination ℝ (jointFamily i) (mixedTrial i hp b A)‖ ^ 2 := by
  have h := dense_trial_completion i hi hsf (mixedTrial i hp b A)
  rw [mixed_certificate i hi hsf hp b hb A] at h
  linarith

theorem mixed_certificate_le (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (b : ↥((oldPeriod i).divisors) → ℝ)
    (hb : oldVector i b = minimumAt (denseSchedule i) (i + 1))
    (A : ℝ) (hA : ‖selfFloor i‖ ^ 2 ≤ A) :
    trialCertificate i (mixedTrial i hp b A) ≤ headFirstCost i - mixedGain i A := by
  rw [mixed_certificate i hi hsf hp b hb A]
  exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg _))

/-- Positivity is automatic after any positive regularization, without
a uniform spectral or inverse-Gram hypothesis. -/
theorem mixed_determinant_pos (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (τ : ℝ) (hτ : 0 < τ) :
    0 < (selfUpper i + τ) * ‖primeColumn i‖ ^ 2 -
      (inner ℝ (selfFloor i) (primeColumn i)) ^ 2 :=
  regularized_determinant_pos _ _ _ τ (selfFloor_energy_le i)
    (screenedPrime_ne_zero i hi hsf hp) hτ

/-- The exact screened denominator is also available. -/
theorem screened_determinant_pos (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (τ : ℝ) (hτ : 0 < τ) :
    0 < (‖selfFloor i‖ ^ 2 + τ) * ‖primeColumn i‖ ^ 2 -
      (inner ℝ (selfFloor i) (primeColumn i)) ^ 2 :=
  regularized_determinant_pos _ _ _ τ le_rfl
    (screenedPrime_ne_zero i hi hsf hp) hτ

theorem mixedGain_ge_self (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (τ : ℝ) (hτ : 0 < τ) :
    (inner ℝ (headFirstMinimum i) (selfFloor i)) ^ 2 / (selfUpper i + τ) ≤
      mixedGain i (selfUpper i + τ) :=
  gain_ge_first _ _ _ _ _ (add_pos (selfUpper_pos i) hτ)
    (mixed_determinant_pos i hi hsf hp τ hτ)

theorem mixedGain_ge_prime (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (τ : ℝ) (hτ : 0 < τ) :
    (inner ℝ (headFirstMinimum i) (primeColumn i)) ^ 2 / ‖primeColumn i‖ ^ 2 ≤
      mixedGain i (selfUpper i + τ) :=
  gain_ge_second _ _ _ _ _
    (sq_pos_of_pos (norm_pos_iff.mpr (screenedPrime_ne_zero i hi hsf hp)))
    (mixed_determinant_pos i hi hsf hp τ hτ)


/-- The screened self-dilation cannot collapse into the prime direction:
that would force the entire actual old optimizer to be zero. -/
theorem selfFloor_not_prime_multiple (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (hp : Nat.Prime (2 * i + 3)) (a : ℝ) :
    selfFloor i ≠ a • primeColumn i := by
  classical
  obtain ⟨b, hb⟩ := exists_oldVector i
    (minimumAt (denseSchedule i) (i + 1)) (minimumAt_mem _ _)
  intro hdep
  have hlin : Fintype.linearCombination ℝ (jointFamily i)
      (divisorTrial i hp (mixedCoefficients i b 1 (-a))) = 0 := by
    rw [mixedSynthesis i hi hsf hp, hb]
    change (1 : ℝ) • selfFloor i + (-a) • primeColumn i = 0
    rw [one_smul, hdep, neg_smul, add_neg_cancel]
  have hz : divisorTrial i hp (mixedCoefficients i b 1 (-a)) = 0 :=
    (jointFamily_independent i).fintypeLinearCombination_injective (by
      simpa only [map_zero] using hlin)
  have hbd (d : ↥((oldPeriod i).divisors)) (hd : d ≠ divisorOne i) : b d = 0 := by
    have h := congrFun hz (primeDivisorEquiv i hp d)
    simpa only [divisorTrial_apply, mixedCoefficients, floorCoefficients,
      if_neg hd, sub_zero, one_mul, add_zero, Pi.zero_apply] using h
  have hfzero : oldVector i b = 0 := by
    unfold oldVector
    rw [Finset.sum_eq_single (divisorOne i)]
    · simp [divisorOne, qResidue_one]
    · intro d hd hne
      rw [hbd d hne, zero_smul]
    · simp
  have hpos := stageEnergy_pos i
  change 0 < ‖minimumAt (denseSchedule i) (i + 1)‖ ^ 2 at hpos
  rw [← hb, hfzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hpos
  exact lt_irrefl 0 hpos

/-- The exact two-dimensional determinant is positive for the actual optimizer.
No regularizer, inverse-Gram bound, or extra independence hypothesis is needed. -/
theorem exact_determinant_pos (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (hp : Nat.Prime (2 * i + 3)) :
    0 < ‖selfFloor i‖ ^ 2 * ‖primeColumn i‖ ^ 2 -
      (inner ℝ (selfFloor i) (primeColumn i)) ^ 2 := by
  have hq := screenedPrime_ne_zero i hi hsf hp
  have hq2 : 0 < ‖primeColumn i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  have hres : selfFloor i -
      (inner ℝ (selfFloor i) (primeColumn i) / ‖primeColumn i‖ ^ 2) • primeColumn i ≠ 0 :=
    sub_ne_zero.mpr (selfFloor_not_prime_multiple i hi hsf hp _)
  have hr := sq_pos_of_pos (norm_pos_iff.mpr hres)
  have hc := observation_completion (selfFloor i) (primeColumn i)
  have he := congrArg (fun x : ℝ => x * ‖primeColumn i‖ ^ 2) hc
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hq2)] at he
  nlinarith [mul_pos hr hq2]

theorem selfFloor_ne_zero (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (hp : Nat.Prime (2 * i + 3)) : selfFloor i ≠ 0 := by
  simpa only [zero_smul] using selfFloor_not_prime_multiple i hi hsf hp 0

/-- The exact two-direction gain dominates the previous head-refined raw trial. -/
theorem exact_mixedGain_ge_raw (i : ℕ) (hi : 0 < i)
    (hsf : Squarefree (i + 2)) (hp : Nat.Prime (2 * i + 3)) :
    (inner ℝ (headFirstMinimum i)
      (floorDilation (2 * i + 3) (by omega)
        (minimumAt (denseSchedule i) (i + 1)))) ^ 2 / selfUpper i ≤
      mixedGain i (‖selfFloor i‖ ^ 2) := by
  have hA := sq_pos_of_pos (norm_pos_iff.mpr (selfFloor_ne_zero i hi hsf hp))
  have hg := gain_ge_first (‖selfFloor i‖ ^ 2)
    (inner ℝ (selfFloor i) (primeColumn i)) (‖primeColumn i‖ ^ 2)
    (inner ℝ (headFirstMinimum i) (selfFloor i))
    (inner ℝ (headFirstMinimum i) (primeColumn i))
    hA (exact_determinant_pos i hi hsf hp)
  apply le_trans _ hg
  change _ ≤ (inner ℝ (headFirstMinimum i) (screen i _)) ^ 2 / ‖selfFloor i‖ ^ 2
  rw [screen_source]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hA (selfFloor_energy_le i)

/-- Exact optimal gain inside the explicit two-dimensional trial subspace.
The only loss is the still-unused part of the full innovation block. -/
theorem exact_mixed_step (i : ℕ) (hi : 0 < i) (hsf : Squarefree (i + 2))
    (hp : Nat.Prime (2 * i + 3)) (b : ↥((oldPeriod i).divisors) → ℝ)
    (hb : oldVector i b = minimumAt (denseSchedule i) (i + 1)) :
    stageEnergy denseSchedule (i + 1) - stageEnergy denseSchedule i =
      headFirstCost i - mixedGain i (‖selfFloor i‖ ^ 2) -
        ‖minimumVector (jointFamily_independent i) (jointSource i) -
          Fintype.linearCombination ℝ (jointFamily i)
            (mixedTrial i hp b (‖selfFloor i‖ ^ 2))‖ ^ 2 := by
  have hc := mixed_step_completion i hi hsf hp b hb (‖selfFloor i‖ ^ 2)
  nlinarith only [hc]


/-- A full divisor representation of the actual old optimizer, whose existence
is proved. Its harmless d=1 ambiguity cancels in floorCoefficients. -/
def actualCoefficients (i : ℕ) : ↥((oldPeriod i).divisors) → ℝ :=
  Classical.choose (exists_oldVector i
    (minimumAt (denseSchedule i) (i + 1)) (minimumAt_mem _ _))

theorem actualCoefficients_spec (i : ℕ) :
    oldVector i (actualCoefficients i) = minimumAt (denseSchedule i) (i + 1) :=
  Classical.choose_spec (exists_oldVector i
    (minimumAt (denseSchedule i) (i + 1)) (minimumAt_mem _ _))

/-- An explicit global coefficient rule; dependent observation sites retain
the exact negative period gain through fullCertificate. -/
def actualTrials (i : ℕ) : addedConductors i → ℝ :=
  if hp : Nat.Prime (2 * i + 3) then
    mixedTrial i hp (actualCoefficients i) (‖selfFloor i‖ ^ 2)
  else 0

/-- Every stage is accounted for, including positive head costs without a
prime enlargement and the initial finite boundary. -/
theorem actualCertificate_formula (i : ℕ) :
    fullCertificate actualTrials i =
      if i = 0 then stageEnergy denseSchedule 1 - stageEnergy denseSchedule 0
      else if Squarefree (i + 2) then
        if Nat.Prime (2 * i + 3) then headFirstCost i - mixedGain i (‖selfFloor i‖ ^ 2)
        else headFirstCost i
      else -periodGain denseSchedule i := by
  by_cases hi : i = 0
  · simp only [fullCertificate, if_pos hi]
  · by_cases hsf : Squarefree (i + 2)
    · by_cases hp : Nat.Prime (2 * i + 3)
      · simp only [fullCertificate, if_neg hi, if_pos hsf, if_pos hp,
          actualTrials, dif_pos hp]
        have hc := mixed_certificate i (Nat.pos_of_ne_zero hi) hsf hp
          (actualCoefficients i) (actualCoefficients_spec i) (‖selfFloor i‖ ^ 2)
        nlinarith only [hc]
      · rw [headFirstCost_eq i (Nat.pos_of_ne_zero hi) hsf]
        simp [fullCertificate, hi, hsf, hp, actualTrials, trialCertificate, dotProduct]
    · simp only [fullCertificate, if_neg hi, if_neg hsf]

end RiemannResearch.RH.QCRTMixedFloorTrial
