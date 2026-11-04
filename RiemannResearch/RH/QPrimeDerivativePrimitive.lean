/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.FinitePrimeDerivativeExpansion
import RiemannResearch.RH.QPrimeDerivativeAtoms
import RiemannResearch.RH.QSquarefreeDimension
import Mathlib.Data.Nat.Squarefree

/-!
# Explicit finite legal primitive of the tensor derivative optimizer

Exact physical remainder and minimization for distinct prime factors.
Asymptotic primitive-energy divergence is not asserted by this module.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace RiemannResearch.RH.QPrimeDerivativePrimitive
open ZetaTwoProbability ZetaTwoHilbert QPhysicalDifference QDifferenceGram
open QFinitePrimeBasis FinitePrimeLikelihood FinitePrimeDerivativeProjection
open FinitePrimeDerivativeExpansion QPrimeDerivativeProjection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conductor (p : ι → ℕ) (A : Finset ι) : ℕ := ∏ i ∈ A, p i

theorem conductor_pos (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (A : Finset ι) :
    0 < conductor p A := Finset.prod_pos (fun i _ => (hp i).pos)

theorem conductor_two_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    {A : Finset ι} (hA : A.Nonempty) : 2 ≤ conductor p A := by
  obtain ⟨i, hi⟩ := hA
  exact (hp i).two_le.trans (Nat.le_of_dvd (conductor_pos p hp A)
    (Finset.dvd_prod_of_mem p hi))

theorem conductor_squarefree (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (A : Finset ι) : Squarefree (conductor p A) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp i) (hp j)).mpr
      (fun h => hij (hinj h)))
  · intro i _
    exact (hp i).squarefree

theorem prime_zeroMass_pos (p : ι → ℕ) (hp : ∀ i, (p i).Prime) :
    0 < zeroMass (fun i => (p i : ℝ)) := by
  apply Finset.prod_pos
  intro i _
  unfold primeParameter
  have hgt : (1:ℝ) < (p i : ℝ) := by exact_mod_cast (hp i).one_lt
  have hpos : 0 < (p i : ℝ)^2 := by positivity
  rw [sub_pos, div_lt_one hpos]
  nlinarith

/-- The physical Boolean lift is linear on the whole finite observable space. -/
def booleanLiftLinear (p : ι → ℕ) : ((ι → Bool) → ℝ) →ₗ[ℝ] QHilbert where
  toFun := booleanLift p
  map_add' f g := by
    apply qSequence_injective
    funext n
    have h := congrFun (qSequenceLinear.map_add (booleanLift p f) (booleanLift p g)) n
    change qSequence (booleanLift p f+booleanLift p g) n =
      qSequence (booleanLift p f) n+qSequence (booleanLift p g) n at h
    change qSequence (booleanLift p (f+g)) n = qSequence (booleanLift p f+booleanLift p g) n
    rw [h]
    simp only [booleanLift_sequence]
    unfold booleanSequence
    split_ifs <;> simp
  map_smul' c f := by
    apply qSequence_injective
    funext n
    have h := congrFun (qSequenceLinear.map_smul c (booleanLift p f)) n
    change qSequence (c • booleanLift p f) n = c*qSequence (booleanLift p f) n at h
    change qSequence (booleanLift p (c • f)) n = qSequence (c • booleanLift p f) n
    rw [h]
    simp only [booleanLift_sequence]
    unfold booleanSequence
    split_ifs <;> simp

theorem booleanLift_zero' (p : ι → ℕ) : booleanLift p (fun _ => 0) = 0 :=
  (booleanLiftLinear p).map_zero

theorem booleanLift_derivativeAtom_all (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (A : Finset ι) :
    booleanLift p (derivativeAtom (fun i => (p i : ℝ)) A) =
      differenceCLM (qResidue (conductor p A)) := by
  by_cases hA : A = ∅
  · subst A
    have hAtom : derivativeAtom (fun i => (p i : ℝ)) (∅ : Finset ι) =
        (fun _ => 0) := by
      funext x
      simp [derivativeAtom, finiteMonomial]
    rw [hAtom, booleanLift_zero']
    simp [conductor, qResidue_one]
  · exact booleanLift_derivativeAtom p hp hinj A
      (conductor_two_le p hp (Finset.nonempty_iff_ne_empty.mpr hA))

def residueCombination (p : ι → ℕ) (c : Finset ι → ℝ) : QHilbert :=
  ∑ A : Finset ι, c A • qResidue (conductor p A)

def cubeCombination (p : ι → ℕ) (c : Finset ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ A : Finset ι, c A*derivativeAtom (fun i => (p i : ℝ)) A x

theorem derivative_residueCombination (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (c : Finset ι → ℝ) :
    differenceCLM (residueCombination p c) = booleanLift p (cubeCombination p c) := by
  unfold residueCombination
  rw [map_sum]
  simp only [map_smul]
  have heq : cubeCombination p c =
      ∑ A : Finset ι, c A • derivativeAtom (fun i => (p i : ℝ)) A := by
    funext x
    simp [cubeCombination]
  rw [heq]
  change _ = (booleanLiftLinear p) (∑ A : Finset ι,
    c A • derivativeAtom (fun i => (p i : ℝ)) A)
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  exact (booleanLift_derivativeAtom_all p hp hinj A).symm

theorem residueCombination_mem_finite_legal_span (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (c : Finset ι → ℝ) :
    residueCombination p c ∈ Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) := by
  unfold residueCombination
  apply Submodule.sum_mem
  intro A _
  apply Submodule.smul_mem
  by_cases hA : A = ∅
  · subst A
    simp [conductor, qResidue_one]
  · have hd := conductor_two_le p hp (Finset.nonempty_iff_ne_empty.mpr hA)
    have hs := conductor_squarefree p hp hinj A
    apply Submodule.subset_span
    refine ⟨conductor p A-2, ?_⟩
    simp [ZetaTwoOptimizerStage.squarefreeAtom, Nat.sub_add_cancel hd, hs]

def primitive (p : ι → ℕ) : QHilbert :=
  residueCombination p (primitiveCoefficient (fun i => (p i : ℝ)) (1/zetaTwo))

theorem primitive_mem_finite_legal_span (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    primitive p ∈ Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) :=
  residueCombination_mem_finite_legal_span p hp hinj _

theorem derivative_primitive (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    differenceCLM (primitive p) = booleanLift p
      (derivativeProjection (fun i => (p i : ℝ)) (1/zetaTwo)) := by
  have hp0 (i : ι) : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  have hp1 (i : ι) : (p i : ℝ)+1 ≠ 0 := by positivity
  rw [primitive, derivative_residueCombination p hp hinj]
  congr 1
  funext x
  exact (derivativeProjection_expansion (fun i => (p i : ℝ)) (1/zetaTwo)
    hp0 hp1 (ne_of_gt (prime_zeroMass_pos p hp)) x).symm

theorem primitive_derivative_error (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    ‖differenceCLM qOne-differenceCLM (primitive p)‖^2 =
      (1/zetaTwo) - (1/zetaTwo)^2/zeroMass (fun i => (p i : ℝ)) +
      (1/zetaTwo)^2*baseRatio (fun i => (p i : ℝ))/(2:ℝ)^(Fintype.card ι) := by
  rw [derivative_primitive p hp hinj]
  exact physical_projection_error p hp hinj (ne_of_gt (prime_zeroMass_pos p hp))

theorem cubeCombination_admissible (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (c : Finset ι → ℝ) :
    tensorExpectation (fun i => primeParameter (p i : ℝ))
      (fun x => finiteLikelihood (fun i => (p i : ℝ)) x*cubeCombination p c x) = 0 := by
  have hp0 (i : ι) : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  have hp1 (i : ι) : (p i : ℝ)+1 ≠ 0 := by positivity
  have hsplit : tensorExpectation (fun i => primeParameter (p i : ℝ))
      (fun x => finiteLikelihood (fun i => (p i : ℝ)) x*cubeCombination p c x) =
      ∑ A : Finset ι, c A *
        tensorExpectation (fun i => primeParameter (p i : ℝ))
          (fun x => finiteLikelihood (fun i => (p i : ℝ)) x*
            derivativeAtom (fun i => (p i : ℝ)) A x) := by
    unfold tensorExpectation cubeCombination
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsplit]
  simp_rw [likelihood_orthogonal_derivative (fun i => (p i : ℝ)) _ hp0 hp1]
  simp

theorem primitive_derivative_full_remainder (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (c : Finset ι → ℝ) :
    ‖differenceCLM qOne-differenceCLM (residueCombination p c)‖^2 =
      (1/zetaTwo) - (1/zetaTwo)^2/zeroMass (fun i => (p i : ℝ)) +
      (1/zetaTwo)^2*baseRatio (fun i => (p i : ℝ))/(2:ℝ)^(Fintype.card ι) +
      ‖differenceCLM (residueCombination p c)-differenceCLM (primitive p)‖^2 := by
  rw [derivative_residueCombination p hp hinj, derivative_primitive p hp hinj]
  exact physical_error_complete p hp hinj (ne_of_gt (prime_zeroMass_pos p hp))
    (cubeCombination p c) (cubeCombination_admissible p hp c)

theorem primitive_derivative_minimizes (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (c : Finset ι → ℝ) :
    ‖differenceCLM qOne-differenceCLM (primitive p)‖^2 ≤
      ‖differenceCLM qOne-differenceCLM (residueCombination p c)‖^2 := by
  rw [primitive_derivative_error p hp hinj, primitive_derivative_full_remainder p hp hinj]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.QPrimeDerivativePrimitive
