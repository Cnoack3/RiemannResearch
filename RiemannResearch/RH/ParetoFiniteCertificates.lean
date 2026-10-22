/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.LinearAlgebra.FiniteWeightedEnergy
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact finite Pareto witness certificates

Source: user-provided argument RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md,
§§5,6,12,13. The integer rows are proved equal to genuine Möbius coefficients.
Their pairings are proved equal to mobiusDifference, not assumed.
The exact Gram matrix retains the negative entry -212. Finite weighted error
floors are instantiated for actual finite prime-power packet combinations.
These are lower bounds on the displayed finite coordinate energies; infinite
Hilbert-space closure and optimizer convergence are not asserted here.
-/

open scoped BigOperators
open RiemannResearch.LinearAlgebra
namespace RiemannResearch.RH.Pareto
noncomputable section

@[simp] theorem moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  rw [show 6 = 2*3 by rfl, moebius_prime_mul 2 3 (by decide)]
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)]

@[simp] theorem moebius_ten : ArithmeticFunction.moebius 10 = 1 := by
  rw [show 10 = 2*5 by rfl, moebius_prime_mul 2 5 (by decide)]
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5)]

@[simp] theorem moebius_fourteen : ArithmeticFunction.moebius 14 = 1 := by
  rw [show 14 = 2*7 by rfl, moebius_prime_mul 2 7 (by decide)]
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 7)]

@[simp] theorem moebius_fifteen : ArithmeticFunction.moebius 15 = 1 := by
  rw [show 15 = 3*5 by rfl, moebius_prime_mul 3 5 (by decide)]
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5)]


def witnessConductors (i : Fin 4) : ℕ := if i.val = 0 then 6 else if i.val = 1 then 10 else if i.val = 2 then 14 else 15
def witnessRow (i : Fin 4) (k : Fin 15) : ℤ := dualCoeff (witnessConductors i) (k+1)
def coordinateWeight (k : Fin 15) : ℤ := (k+1)*(k+2)
def witnessRowTable : Matrix (Fin 4) (Fin 15) ℤ :=
  !![2,0,-1,0,-1,1,0,0,0,0,0,0,0,0,0;
    2,-1,0,1,-1,0,0,0,-1,1,0,0,0,0,0;
    2,-1,0,0,0,1,-1,0,0,0,0,0,-1,1,0;
    1,1,-1,1,-1,0,0,0,0,0,0,0,0,-1,1]

set_option maxHeartbeats 800000 in
theorem witnessRow_eq_table : witnessRow = witnessRowTable := by
  funext i k
  fin_cases i <;> fin_cases k <;>
    norm_num [witnessRow, witnessRowTable, witnessConductors, dualCoeff,
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 7)]

def witnessGram (i j : Fin 4) : ℤ :=
  ∑ k, coordinateWeight k * witnessRow i k * witnessRow j k
def certificateNumerators : Fin 4 → ℤ := ![4130555,1131320,956664,905777]
def certificateMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![92,38,50,46; 38,264,14,48; 50,14,504,-212; 46,48,-212,520]

theorem witnessGram_eq_certificateMatrix : witnessGram = certificateMatrix := by
  unfold witnessGram
  rw [witnessRow_eq_table]
  funext i j
  fin_cases i <;> fin_cases j <;> decide

theorem dualSix_normSq : witnessGram 0 0 = 92 := by rw [witnessGram_eq_certificateMatrix]; rfl

theorem primorialDual_normSq :
    (∑ k : Fin 15, coordinateWeight k *
      (3*witnessRow 1 k - 2*witnessRow 3 k)^2) = 3880 := by
  rw [witnessRow_eq_table]
  decide

theorem certificateMatrix_mul_numerators :
    ∀ i, (∑ j, certificateMatrix i j * certificateNumerators j) = 512500162 := by decide

theorem certificateNumerators_sum : (∑ i, certificateNumerators i) = 7124316 := by decide

theorem certificate_fraction : (7124316 : ℚ)/512500162 = 3562158/256250081 := by norm_num

theorem mobiusDifference_six (f : ℕ → ℝ) (h0 : f 0 = 0) :
    mobiusDifference 6 f = 2*f 1 - f 3 - f 5 + f 6 := by
  rw [mobiusDifference, show (6:ℕ).divisors = {1,2,3,6} by decide]
  norm_num [moebius_six,
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3), h0]
  ring

theorem primePowerPacket_dualSix_zero (p a : ℕ) (hp : p.Prime) :
    mobiusDifference 6 (ramanujanPacket (p^a)) = 0 := by
  apply primePowerPacket_dual_zero 6 p a (by decide) _ hp
  rw [show 6 = 2*3 by rfl, Nat.primeFactors_mul (by decide) (by decide),
    (show Nat.Prime 2 by decide).primeFactors, (show Nat.Prime 3 by decide).primeFactors]
  decide

theorem dualSix_square_completion (a b c d : ℝ) :
    a^2/2+b^2/12+c^2/30+d^2/42 - (2*a-b-c+d)^2/92 =
    (a-4*(2*a-b-c+d)/92)^2/2 + (b+12*(2*a-b-c+d)/92)^2/12 +
    (c+30*(2*a-b-c+d)/92)^2/30 + (d-42*(2*a-b-c+d)/92)^2/42 := by ring

theorem dualSix_error_floor (f : ℕ → ℝ) (h0 : f 0 = 0)
    (hdual : mobiusDifference 6 f = 0) :
    (1:ℝ)/92 ≤ (1-f 1)^2/2+(1-f 3)^2/12+(1-f 5)^2/30+(1-f 6)^2/42 := by
  rw [mobiusDifference_six f h0] at hdual
  have h := dualSix_square_completion (1-f 1) (1-f 3) (1-f 5) (1-f 6)
  have hsignal : 2*(1-f 1)-(1-f 3)-(1-f 5)+(1-f 6) = 1 := by linarith
  rw [hsignal] at h
  have hn : 0 ≤ ((1-f 1)-4/92)^2/2 + ((1-f 3)+12/92)^2/12 +
      ((1-f 5)+30/92)^2/30 + ((1-f 6)-42/92)^2/42 := by positivity
  nlinarith

set_option maxHeartbeats 800000 in
theorem witnessRow_pairing (i : Fin 4) (f : ℕ → ℝ) (h0 : f 0 = 0) :
    (∑ k : Fin 15, (witnessRow i k : ℝ) * f (k+1)) =
      mobiusDifference (witnessConductors i) f := by
  rw [witnessRow_eq_table]
  fin_cases i <;>
    norm_num [witnessRowTable, witnessConductors, mobiusDifference, Fin.sum_univ_succ,
      show (6:ℕ).divisors = {1,2,3,6} by decide,
      show (10:ℕ).divisors = {1,2,5,10} by decide,
      show (14:ℕ).divisors = {1,2,7,14} by decide,
      show (15:ℕ).divisors = {1,3,5,15} by decide,
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 7), h0] <;> ring

def certificateRow (k : Fin 15) : ℤ := ∑ i, certificateNumerators i * witnessRow i k

theorem certificateRow_mass : (∑ k, certificateRow k) = 7124316 := by
  unfold certificateRow
  rw [witnessRow_eq_table]
  decide

theorem certificateRow_normSq :
    (∑ k, coordinateWeight k * (certificateRow k)^2) = 3651213104139192 := by
  unfold certificateRow
  rw [witnessRow_eq_table]
  decide

theorem certificateRow_pairing (f : ℕ → ℝ) (h0 : f 0 = 0) :
    (∑ k : Fin 15, (certificateRow k : ℝ) * f (k+1)) =
      ∑ i, (certificateNumerators i : ℝ) * mobiusDifference (witnessConductors i) f := by
  simp only [certificateRow, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← witnessRow_pairing i f h0, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

set_option maxHeartbeats 800000 in
theorem fourWitness_error_floor (f : ℕ → ℝ) (h0 : f 0 = 0)
    (hd : ∀ i, mobiusDifference (witnessConductors i) f = 0) :
    (3562158:ℝ)/256250081 ≤
      ∑ k : Fin 15, (1-f (k+1))^2 / (coordinateWeight k : ℝ) := by
  have hmass : (∑ k, (certificateRow k : ℝ)) = 7124316 := by
    exact_mod_cast certificateRow_mass
  have hnorm : (∑ k, (coordinateWeight k : ℝ)*(certificateRow k : ℝ)^2) =
      3651213104139192 := by exact_mod_cast certificateRow_normSq
  have hpair : (∑ k : Fin 15, (certificateRow k : ℝ)*f (k+1)) = 0 := by
    rw [certificateRow_pairing f h0]
    simp [hd]
  have hsignal : (∑ k : Fin 15, (certificateRow k : ℝ)*(1-f (k+1))) = 7124316 := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hmass, hpair, sub_zero]
  have h := finite_weighted_dual_bound Finset.univ
    (fun k : Fin 15 => (coordinateWeight k : ℝ)) (fun k => (certificateRow k : ℝ))
    (fun k => 1-f (k+1)) (by
      intro k _
      unfold coordinateWeight
      push_cast
      positivity) (by rw [hnorm]; norm_num)
  rw [hnorm, hsignal] at h
  norm_num at h ⊢
  exact h

theorem witnessConductors_primePower_zero (i : Fin 4) (p a : ℕ) (hp : p.Prime) :
    mobiusDifference (witnessConductors i) (ramanujanPacket (p^a)) = 0 := by
  apply primePowerPacket_dual_zero _ p a _ _ hp
  · fin_cases i <;> norm_num [witnessConductors]
  · fin_cases i <;> norm_num [witnessConductors]
    all_goals first
      | rw [show 6 = 2*3 by rfl]
      | rw [show 10 = 2*5 by rfl]
      | rw [show 14 = 2*7 by rfl]
      | rw [show 15 = 3*5 by rfl]
    all_goals rw [Nat.primeFactors_mul (by decide) (by decide),
      (show Nat.Prime _ by decide).primeFactors, (show Nat.Prime _ by decide).primeFactors]
    all_goals decide

set_option maxHeartbeats 800000 in
theorem primePowerCombination_error_floor (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, ∃ p a, p.Prime ∧ q = p^a) :
    (3562158:ℝ)/256250081 ≤
      ∑ k : Fin 15, (1-∑ q ∈ s, c q*ramanujanPacket q (k+1))^2 /
        (coordinateWeight k : ℝ) := by
  apply fourWitness_error_floor (fun k => ∑ q ∈ s, c q*ramanujanPacket q k)
  · simp [ramanujanPacket, residue]
  · intro i
    rw [mobiusDifference_sum]
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨p, a, hp, rfl⟩ := hs q hq
    rw [witnessConductors_primePower_zero i p a hp, mul_zero]

end
end RiemannResearch.RH.Pareto
