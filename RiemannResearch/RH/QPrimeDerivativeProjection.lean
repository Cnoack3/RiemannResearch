/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FinitePrimeDerivativeProjection
import RiemannResearch.RH.QFinitePrimeBasis
import RiemannResearch.RH.QDifferenceGram
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact finite prime-product derivative projection

Source: elementary finite-product Hilbert projection specialization of the
prime-block agenda (4 November 2026), using the existing finite likelihood
and Boolean-lift modules. Euler-product background: NIST DLMF 25.2.11.
The target is derivative least squares; no bounded primitive energy or RH
provider is asserted. Exact norm-square remainders are retained.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace RiemannResearch.RH.QPrimeDerivativeProjection
open ZetaTwoProbability ZetaTwoHilbert QPhysicalDifference QDifferenceGram
open QFinitePrimeBasis FinitePrimeLikelihood FinitePrimeDerivativeProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem booleanLift_at_one (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (f : (ι → Bool) → ℝ) :
    qSequence (booleanLift p f) 1 = f zeroConfiguration := by
  rw [booleanLift_sequence]
  unfold booleanSequence
  simp only [Nat.one_ne_zero, if_false]
  congr 1
  funext i
  have hnot : ¬p i ∣ 1 := fun h => (hp i).ne_one (Nat.dvd_one.mp h)
  simp [hnot, zeroConfiguration]

theorem booleanLift_norm_sq (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (f : (ι → Bool) → ℝ) :
    ‖booleanLift p f‖^2 =
      tensorExpectation (fun i => primeParameter (p i : ℝ)) (fun x => f x ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, booleanLift_inner p hp hinj]
  congr 1
  funext x
  ring

theorem booleanLift_sub (p : ι → ℕ) (f g : (ι → Bool) → ℝ) :
    booleanLift p (fun x => f x - g x) = booleanLift p f-booleanLift p g := by
  apply qSequence_injective
  funext n
  have hsub := congrFun (qSequenceLinear.map_sub (booleanLift p f) (booleanLift p g)) n
  change qSequence (booleanLift p (fun x => f x - g x)) n =
    qSequence (booleanLift p f-booleanLift p g) n
  change qSequence (booleanLift p f - booleanLift p g) n =
    qSequence (booleanLift p f) n - qSequence (booleanLift p g) n at hsub
  rw [hsub]
  simp only [booleanLift_sequence]
  unfold booleanSequence
  split_ifs <;> simp

theorem physical_error_eq_targetError (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (f : (ι → Bool) → ℝ) :
    ‖differenceCLM qOne-booleanLift p f‖^2 =
      targetError (fun i => (p i : ℝ)) (1/zetaTwo) f := by
  rw [norm_sub_sq_real, norm_difference_qOne_sq,
    booleanLift_norm_sq p hp hinj, inner_difference_qOne,
    booleanLift_at_one p hp]
  unfold targetError
  ring

theorem physical_error_complete (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p)
    (ha : zeroMass (fun i => (p i : ℝ)) ≠ 0)
    (f : (ι → Bool) → ℝ)
    (horth : tensorExpectation (fun i => primeParameter (p i : ℝ))
      (fun x => finiteLikelihood (fun i => (p i : ℝ)) x * f x) = 0) :
    ‖differenceCLM qOne-booleanLift p f‖^2 =
      (1/zetaTwo) - (1/zetaTwo)^2/zeroMass (fun i => (p i : ℝ)) +
      (1/zetaTwo)^2*baseRatio (fun i => (p i : ℝ))/(2:ℝ)^(Fintype.card ι) +
      ‖booleanLift p f - booleanLift p
        (derivativeProjection (fun i => (p i : ℝ)) (1/zetaTwo))‖^2 := by
  have hp0 (i : ι) : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  have hp1 (i : ι) : (p i : ℝ)+1 ≠ 0 := by positivity
  rw [physical_error_eq_targetError p hp hinj,
    targetError_exact (fun i => (p i : ℝ)) (1/zetaTwo) hp0 hp1 ha f horth,
    ← booleanLift_sub, booleanLift_norm_sq p hp hinj]

theorem physical_projection_error (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p)
    (ha : zeroMass (fun i => (p i : ℝ)) ≠ 0) :
    ‖differenceCLM qOne-booleanLift p
        (derivativeProjection (fun i => (p i : ℝ)) (1/zetaTwo))‖^2 =
      (1/zetaTwo) - (1/zetaTwo)^2/zeroMass (fun i => (p i : ℝ)) +
      (1/zetaTwo)^2*baseRatio (fun i => (p i : ℝ))/(2:ℝ)^(Fintype.card ι) := by
  have hp0 (i : ι) : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  have hp1 (i : ι) : (p i : ℝ)+1 ≠ 0 := by positivity
  rw [physical_error_complete p hp hinj ha _
    (projection_admissible (fun i => (p i : ℝ)) (1/zetaTwo) hp0 hp1 ha)]
  simp

end RiemannResearch.RH.QPrimeDerivativeProjection
