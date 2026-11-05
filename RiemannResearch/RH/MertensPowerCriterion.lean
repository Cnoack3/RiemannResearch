/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensActualPowerPairing
import RiemannResearch.RH.MertensDefectPowerArithmetic
import RiemannResearch.RH.MertensPowerReciprocal
import Mathlib.Data.Nat.Prime.Infinite
/-!
# An RH consequence of one Mertens estimate and displacement growth

The Mertens estimate for all positive integer cutoffs is a named hypothesis.
Gerhold, Acta Arith. 142 (2010), Proposition 3, gives that hypothesis for
every exponent above any zero-free half-plane boundary.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert Pareto RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- One bound on ordinary Mertens sums supplies cofinal legal heads with a
uniform two-part defect bound. The reciprocal rate follows by Abel summation. -/
theorem exists_cofinal_power_defect_of_mertens_power
    (s C : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n → |M (n : ℝ)| ≤ C * (n : ℝ)^s) :
    ∃ (q : ℕ → ℕ) (K : ℝ), Tendsto q atTop atTop ∧ 0 ≤ K ∧
      (∀ᶠ j : ℕ in atTop, Squarefree (q j + 1)) ∧
      ∀ᶠ j : ℕ in atTop, ∀ n : ℕ, |1 - canonicalMobiusHead (q j) (n+1)| ≤
        K * min (q j : ℝ) (((n : ℝ) + 1) * (q j : ℝ) ^ (-(1-s))) := by
  classical
  choose p hpl hpp using (fun j : ℕ => Nat.exists_infinite_primes (j+2))
  let q : ℕ → ℕ := fun j => p j - 1
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with j hj
    have := hpl j
    dsimp [q]
    omega
  have hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1) := by
    apply Eventually.of_forall
    intro j
    have hp : q j + 1 = p j := by have := hpl j; dsimp [q]; omega
    rw [hp]
    exact (hpp j).squarefree
  let D := (2+1/(1-s))*C
  let E := 2*C/(1-s)+D
  have hpos : 0 < 1-s := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨q, max 3 E, hq, (by norm_num : 0 ≤ (3 : ℝ)).trans (le_max_left _ _), hlegal, ?_⟩
  filter_upwards [hq.eventually (eventually_ge_atTop 1)] with j hj n
  have hN : 0 < q j := by omega
  have hr := mobiusReciprocalSum_le_of_M_nat_power s C hs hs1 hC hM (q j) hN
  have he := canonicalMobiusHead_defect_le_min_of_M_power (q j) (n+1) hN (by omega)
    s C D hs hs1 hC hD (fun t ht => hM t (hN.trans_le ht)) hr
  let X : ℝ := ((n:ℝ)+1)*(q j :ℝ)^(s-1)
  have hx : 0 ≤ X := by dsimp [X]; positivity
  have he' : |1 - canonicalMobiusHead (q j) (n+1)| ≤ min (3*(q j :ℝ)) (E*X) := by
    simpa only [E, X, Nat.cast_add, Nat.cast_one] using he
  rw [show -(1-s) = s-1 by ring]
  change _ ≤ max 3 E * min (q j : ℝ) X
  by_cases h : (q j : ℝ) ≤ X
  · rw [min_eq_left h]
    exact he'.trans ((min_le_left _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)))
  · rw [min_eq_right (le_of_not_ge h)]
    exact he'.trans ((min_le_right _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hx))

/-- One ordinary power Mertens estimate and one absolute first moment of
physical displacement suffice. The reciprocal Mertens rate is derived. -/
theorem riemannHypothesis_of_mertens_power_and_displacement_moment
    (s C : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 0 < n → |M (n : ℝ)| ≤ C * (n : ℝ)^s)
    (hd : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 / (2-s)) *
      |qSequence displacement (n+1) / ((n : ℝ) + 1) ^ 2|)) :
    RiemannHypothesis := by
  obtain ⟨q, K, hq, hK, hlegal, hdef⟩ :=
    exists_cofinal_power_defect_of_mertens_power s C hs hs1 hC hM
  exact riemannHypothesis_of_power_defect_and_displacement_moment q hq (1-s) K
    (by linarith) hK hlegal hdef
    (by simpa only [show 1 + (1-s) = 2-s by ring] using hd)

/-- Every pointwise growth exponent strictly below `(1-s)/(2-s)` suffices. -/
theorem riemannHypothesis_of_mertens_power_and_displacement
    (s β C K : ℝ) (hs : 0 ≤ s) (hs1 : s < 1)
    (hβ : β < (1-s)/(2-s)) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hM : ∀ n : ℕ, 0 < n → |M (n : ℝ)| ≤ C * (n : ℝ)^s)
    (hd : ∀ n : ℕ, |qSequence displacement (n+1)| ≤ K * ((n : ℝ)+1)^β) :
    RiemannHypothesis := by
  have he : 1 + (1-s) = 2-s := by ring
  apply riemannHypothesis_of_mertens_power_and_displacement_moment s C hs hs1 hC hM
  simpa only [he] using RiemannResearch.Analysis.summable_power_pairing_of_growth
    _ (1-s) β K (by linarith) (by simpa only [he] using hβ) hK hd

/-- The 7/8 Mertens provider supplied on paper by a zero-free half-plane
gives every displacement exponent strictly below 1/9 by the exact-head proof. -/
theorem riemannHypothesis_of_seven_eighths_mertens_and_displacement
    (β K : ℝ) (hβ0 : 0 ≤ β) (hβ : β < 1/9) (hK : 0 ≤ K)
    (hM : ∀ s : ℝ, 7/8 < s → s < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 0 < n → |M (n : ℝ)| ≤ C * (n : ℝ)^s)
    (hd : ∀ n : ℕ, |qSequence displacement (n+1)| ≤ K * ((n : ℝ)+1)^β) :
    RiemannHypothesis := by
  let s := (15 - 9*β) / 16
  have hs : 7/8 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  obtain ⟨C, hC, hMC⟩ := hM s hs hs1
  apply riemannHypothesis_of_mertens_power_and_displacement s β C K
    (by linarith) hs1 _ hC hK hMC hd
  apply (lt_div_iff₀ (by linarith : 0 < 2-s)).2
  have hh := mul_pos (show 0 < 1+β by linarith) (show 0 < 1-9*β by linarith)
  dsimp [s]
  nlinarith only [hh]

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
