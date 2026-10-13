/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeSensorGain
import RiemannResearch.RH.PrimeSensorProjection
import RiemannResearch.RH.PrimeCoefficientStability
import RiemannResearch.RH.CoupledResidualCorrections
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# A rate obstruction for prime-only actual gain certificates

Source: user-provided consolidated Pareto/zero-ordinate handoff (2026-10-11),
Sections 5, 12 and 15, and the request to prove its remaining gap.
The finite cardinality bound and geometric summability deductions are
derived here; no mathematical novelty claim is made.

For actual new-prime blocks, a uniform coefficient bound C/q and a distance
floor L/(n+1) force the normalized prime observation energy to be summable.
Both domain-specific bounds are explicit hypotheses. The coefficient bound
is Open. The floor is a classical analytic input whose actual two-seed
specialization has not been formalized here. No RH premise is used.

Literature context, not a supplied Lean provider:
Burnol, arXiv:math/0103058, Theorem 1.3, and Bettin--Conrey--Farmer,
arXiv:1211.5191, Section 1, discuss the Nyman--Beurling lower distance floor.
The latter paper's matching upper asymptotic assumes RH and derivative
control; it is not used to infer an unconditional gain bound.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.RH.Pareto.ContrastObstruction

theorem primeCoefficientEnergy_le_inverse_scale
    (P : Finset ℕ) (c : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hcard : P.card ≤ M) (hindex : ∀ q ∈ P, M ≤ q)
    (C : ℝ) (hcoeff : ∀ q ∈ P, |c q| ≤ C / (q : ℝ)) :
    primeCoefficientEnergy P c ≤ C ^ 2 / (M : ℝ) := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hpoint : ∀ q ∈ P, (c q) ^ 2 ≤ C ^ 2 / (M : ℝ) ^ 2 := by
    intro q hqP
    have hqR : (M : ℝ) ≤ (q : ℝ) := by exact_mod_cast hindex q hqP
    have hs := mul_self_le_mul_self (abs_nonneg (c q)) (hcoeff q hqP)
    simp only [← pow_two, sq_abs, div_pow] at hs
    apply hs.trans
    exact div_le_div_of_nonneg_left (sq_nonneg C) (pow_pos hMR 2)
      (by nlinarith)
  calc
    primeCoefficientEnergy P c ≤ ∑ q ∈ P, C ^ 2 / (M : ℝ) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (P.card : ℝ) * (C ^ 2 / (M : ℝ) ^ 2) := by simp
    _ ≤ (M : ℝ) * (C ^ 2 / (M : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      positivity
    _ = C ^ 2 / (M : ℝ) := by
      field_simp [ne_of_gt hMR]

theorem primeObservedEnergy_le_inverse_scale
    (P : Finset ℕ) (c : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hcard : P.card ≤ M) (hindex : ∀ q ∈ P, M ≤ q)
    (C : ℝ) (hcoeff : ∀ q ∈ P, |c q| ≤ C / (q : ℝ)) :
    primeObservedEnergy P c ≤ C ^ 2 / (2 * (M : ℝ)) := by
  calc
    primeObservedEnergy P c ≤ primeCoefficientEnergy P c / 2 :=
      primeObservedEnergy_upper_bound P c
    _ ≤ (C ^ 2 / (M : ℝ)) / 2 :=
      div_le_div_of_nonneg_right
        (primeCoefficientEnergy_le_inverse_scale P c M hM hcard hindex C hcoeff)
        (by norm_num)
    _ = _ := by rw [div_div]; congr 1; ring

end RiemannResearch.RH.Pareto.ContrastObstruction

namespace RiemannResearch.RH.Pareto.CoupledResidual
open ContrastObstruction FiniteTwoSeedCompletion RamanujanLaguerre

def dyadicNewPrimeBlock (n : ℕ) : Finset ℕ :=
  (Finset.Icc (2 ^ n + 1) (2 ^ (n + 1))).filter (fun q => q.Prime ∧ 3 < q)

theorem dyadicNewPrimeBlock_properties (n q : ℕ) (hq : q ∈ dyadicNewPrimeBlock n) :
    q.Prime ∧ 3 < q ∧ 2 ^ n < q := by
  have h := Finset.mem_filter.mp hq
  have hi := (Finset.mem_Icc.mp h.1).1
  exact ⟨h.2.1, h.2.2, by omega⟩

theorem dyadicNewPrimeBlock_card_le (n : ℕ) : (dyadicNewPrimeBlock n).card ≤ 2 ^ n := by
  unfold dyadicNewPrimeBlock
  apply (Finset.card_filter_le _ _).trans
  rw [Nat.card_Icc, pow_succ]
  omega

theorem dyadicPrimeObservedGain_le_geometric
    (P : ℕ → Finset ℕ) (hcard : ∀ n, (P n).card ≤ 2 ^ n)
    (hindex : ∀ n, ∀ q ∈ P n, 2 ^ n ≤ q)
    (C L : ℝ) (hL : 0 < L)
    (hcoeff : ∀ n, ∀ q ∈ P n,
      |primeSensorValues (fit (2 ^ (n + 1))) q| ≤ C / (q : ℝ))
    (hfloor : ∀ n : ℕ, L / ((n : ℝ) + 1) ≤ distance (2 ^ n)) (n : ℕ) :
    dyadicPrimeObservedGain P n ≤
      (C ^ 2 / (2 * L)) * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n := by
  have hp : 0 < (2 ^ n : ℕ) := pow_pos (by norm_num) n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hf : 0 < L / ((n : ℝ) + 1) := div_pos hL hn
  have he := primeObservedEnergy_le_inverse_scale (P n)
    (primeSensorValues (fit (2 ^ (n + 1)))) (2 ^ n) hp (hcard n) (hindex n) C (hcoeff n)
  unfold dyadicPrimeObservedGain primeObservedFitEnergy
  calc
    primeObservedEnergy (P n) (primeSensorValues (fit (2 ^ (n + 1)))) / distance (2 ^ n) ≤
        (C ^ 2 / (2 * ((2 ^ n : ℕ) : ℝ))) / distance (2 ^ n) :=
      div_le_div_of_nonneg_right he (distance_pos _).le
    _ ≤ (C ^ 2 / (2 * ((2 ^ n : ℕ) : ℝ))) / (L / ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_left (by positivity) hf (hfloor n)
    _ = _ := by
      push_cast
      rw [div_pow, one_pow]
      field_simp [ne_of_gt hL]

theorem dyadicPrimeObservedGain_summable_of_mobius_scale
    (P : ℕ → Finset ℕ) (hcard : ∀ n, (P n).card ≤ 2 ^ n)
    (hindex : ∀ n, ∀ q ∈ P n, 2 ^ n ≤ q)
    (C L : ℝ) (hL : 0 < L)
    (hcoeff : ∀ n, ∀ q ∈ P n,
      |primeSensorValues (fit (2 ^ (n + 1))) q| ≤ C / (q : ℝ))
    (hfloor : ∀ n : ℕ, L / ((n : ℝ) + 1) ≤ distance (2 ^ n)) :
    Summable (dyadicPrimeObservedGain P) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hn := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hg := summable_geometric_of_norm_lt_one hr
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    simpa only [add_mul, one_mul] using hn.add hg
  have hc : Summable (fun n : ℕ =>
      (C ^ 2 / (2 * L)) * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n) := by
    simpa only [mul_assoc] using hs.mul_left (C ^ 2 / (2 * L))
  exact Summable.of_nonneg_of_le (dyadicPrimeObservedGain_nonneg P)
    (dyadicPrimeObservedGain_le_geometric P hcard hindex C L hL hcoeff hfloor) hc

theorem dyadicNewPrimeObservedGain_summable_of_mobius_scale
    (C L : ℝ) (hL : 0 < L)
    (hcoeff : ∀ n, ∀ q ∈ dyadicNewPrimeBlock n,
      |primeSensorValues (fit (2 ^ (n + 1))) q| ≤ C / (q : ℝ))
    (hfloor : ∀ n : ℕ, L / ((n : ℝ) + 1) ≤ distance (2 ^ n)) :
    Summable (dyadicPrimeObservedGain dyadicNewPrimeBlock) := by
  apply dyadicPrimeObservedGain_summable_of_mobius_scale dyadicNewPrimeBlock
    dyadicNewPrimeBlock_card_le _ C L hL hcoeff hfloor
  intro n q hq
  exact (dyadicNewPrimeBlock_properties n q hq).2.2.le

theorem dyadicNewPrime_minorant_summable_of_mobius_scale
    (C L : ℝ) (hL : 0 < L)
    (hcoeff : ∀ n, ∀ q ∈ dyadicNewPrimeBlock n,
      |primeSensorValues (fit (2 ^ (n + 1))) q| ≤ C / (q : ℝ))
    (hfloor : ∀ n : ℕ, L / ((n : ℝ) + 1) ≤ distance (2 ^ n))
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hminor : ∀ n, a n ≤ dyadicPrimeObservedGain dyadicNewPrimeBlock n) : Summable a :=
  Summable.of_nonneg_of_le ha hminor
    (dyadicNewPrimeObservedGain_summable_of_mobius_scale C L hL hcoeff hfloor)

end RiemannResearch.RH.Pareto.CoupledResidual
