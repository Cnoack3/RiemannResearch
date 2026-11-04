/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.QPrimeDerivativeProjection
import RiemannResearch.RH.PrimeValuationIndependence
import Mathlib.Tactic.Push

/-!
# Actual divisor atoms and physical derivative normal equations.

Finite exact identities; no asymptotic arithmetic gain bound is assumed or proved.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace RiemannResearch.RH.QPrimeDerivativeProjection
open ZetaTwoProbability ZetaTwoHilbert QPhysicalDifference QDifferenceGram
open QFinitePrimeBasis FinitePrimeLikelihood FinitePrimeDerivativeProjection
open SquarefreeRadicalDifference

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteMonomial_divisibility (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (A : Finset ι) (n : ℕ) :
    finiteMonomial A (fun i => decide (p i ∣ n)) =
      if (∏ i ∈ A, p i) ∣ n then 1 else 0 := by
  have hdvd : (∏ i ∈ A, p i) ∣ n ↔ ∀ i ∈ A, p i ∣ n := by
    simpa using primePower_product_dvd_iff p hp hinj (fun _ => 1) A n
  by_cases hn : (∏ i ∈ A, p i) ∣ n
  · rw [if_pos hn]
    unfold finiteMonomial
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ A
    · simp [hi, boolIndicator, hdvd.mp hn i hi]
    · simp [hi]
  · rw [if_neg hn]
    have hnot : ¬∀ i ∈ A, p i ∣ n := fun h => hn (hdvd.mpr h)
    push Not at hnot
    obtain ⟨i, hi, hni⟩ := hnot
    unfold finiteMonomial
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, hni, boolIndicator]

theorem booleanLift_derivativeAtom (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (A : Finset ι)
    (hd : 2 ≤ ∏ i ∈ A, p i) :
    booleanLift p (derivativeAtom (fun i => (p i : ℝ)) A) =
      differenceCLM (qResidue (∏ i ∈ A, p i)) := by
  apply qSequence_injective
  funext n
  by_cases hn : n = 0
  · subst n
    simp [booleanLift_sequence, booleanSequence]
  · rw [booleanLift_sequence]
    unfold booleanSequence
    rw [if_neg hn, qSequence_differenceCLM]
    simp only [qDifference, qSequence_qResidue]
    rw [residueFraction_difference _ n hd (by omega)]
    unfold derivativeAtom
    rw [finiteMonomial_divisibility p hp hinj A n]
    simp [Nat.cast_prod]

theorem physical_projection_normal_equation (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Finset ι) (hA : A.Nonempty) (hd : 2 ≤ ∏ i ∈ A, p i)
    (ha : zeroMass (fun i => (p i : ℝ)) ≠ 0) :
    inner ℝ (differenceCLM qOne - booleanLift p
      (derivativeProjection (fun i => (p i : ℝ)) (1/zetaTwo)))
      (differenceCLM (qResidue (∏ i ∈ A, p i))) = 0 := by
  have hp0 (i : ι) : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
  have hp1 (i : ι) : (p i : ℝ)+1 ≠ 0 := by positivity
  rw [inner_sub_left, inner_difference_qOne_qResidue _ hd,
    ← booleanLift_derivativeAtom p hp hinj A hd, booleanLift_inner p hp hinj,
    projection_normal_equation (fun i => (p i : ℝ)) (1/zetaTwo) A hA hp0 hp1 ha]
  simp [Nat.cast_prod]

end RiemannResearch.RH.QPrimeDerivativeProjection
