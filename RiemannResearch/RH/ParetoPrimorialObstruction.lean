/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoFiniteCertificates
import Mathlib.NumberTheory.Primorial

/-!
# Primepowers plus primorials remain obstructed

Source: user-provided argument RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md,
§6. The functional 3 ell_10 - 2 ell_15 annihilates actual prime-power packets
and every Mathlib primorial packet. Its signal is 1, its finite weighted
squared dual norm is 3880, and the error-floor theorem is specialized to
arbitrary finite linear combinations of the two families.
-/

open scoped BigOperators
open RiemannResearch.LinearAlgebra
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem moebius_div_of_squarefree (q d : ℕ) (hq : Squarefree q) (hd : d ∣ q) :
    ArithmeticFunction.moebius (q/d) =
      ArithmeticFunction.moebius q * ArithmeticFunction.moebius d := by
  have he : d*(q/d) = q := Nat.mul_div_cancel' hd
  have hs : Squarefree (d*(q/d)) := he.symm ▸ hq
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (Nat.coprime_of_squarefree_mul hs)
  rw [he] at hmul
  have hsq := ArithmeticFunction.moebius_sq_eq_one_of_squarefree
    (Squarefree.squarefree_of_dvd hd hq)
  rw [hmul]
  calc
    ArithmeticFunction.moebius (q/d) =
        ArithmeticFunction.moebius (q/d) * ArithmeticFunction.moebius d ^ 2 := by rw [hsq, mul_one]
    _ = _ := by ring

def primorialDual (f : ℕ → ℝ) : ℝ := 3*mobiusDifference 10 f - 2*mobiusDifference 15 f

theorem primorialDual_packet_of_squarefree (q : ℕ) (hq : 0 < q)
    (hs : Squarefree q) (hd : 10 ∣ q ↔ 15 ∣ q) :
    primorialDual (ramanujanPacket q) = 0 := by
  unfold primorialDual
  rw [mobiusDifference_packet 10 q (by decide) hq,
    mobiusDifference_packet 15 q (by decide) hq]
  by_cases h10 : 10 ∣ q
  · rw [if_pos h10, if_pos (hd.mp h10), moebius_div_of_squarefree q 10 hs h10,
      moebius_div_of_squarefree q 15 hs (hd.mp h10)]
    simp
    ring
  · simp [h10, show ¬ 15 ∣ q from fun h => h10 (hd.mpr h)]

theorem ten_dvd_primorial_iff (n : ℕ) : 10 ∣ primorial n ↔ 5 ≤ n := by
  constructor
  · intro h
    exact (show Nat.Prime 5 by decide).dvd_primorial_iff.mp (dvd_trans (by decide) h)
  · intro h
    exact (show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd
      ((show Nat.Prime 2 by decide).dvd_primorial_iff.mpr (by omega))
      ((show Nat.Prime 5 by decide).dvd_primorial_iff.mpr h)

theorem fifteen_dvd_primorial_iff (n : ℕ) : 15 ∣ primorial n ↔ 5 ≤ n := by
  constructor
  · intro h
    exact (show Nat.Prime 5 by decide).dvd_primorial_iff.mp (dvd_trans (by decide) h)
  · intro h
    exact (show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd
      ((show Nat.Prime 3 by decide).dvd_primorial_iff.mpr (by omega))
      ((show Nat.Prime 5 by decide).dvd_primorial_iff.mpr h)

theorem primorialDual_primorialPacket_zero (n : ℕ) :
    primorialDual (ramanujanPacket (primorial n)) = 0 := by
  apply primorialDual_packet_of_squarefree _ (primorial_pos n) (squarefree_primorial n)
  rw [ten_dvd_primorial_iff, fifteen_dvd_primorial_iff]

theorem primorialDual_primePowerPacket_zero (p a : ℕ) (hp : p.Prime) :
    primorialDual (ramanujanPacket (p^a)) = 0 := by
  have hc10 : 1 < (10:ℕ).primeFactors.card := by
    rw [show 10 = 2*5 by rfl, Nat.primeFactors_mul (by decide) (by decide),
      (show Nat.Prime 2 by decide).primeFactors, (show Nat.Prime 5 by decide).primeFactors]
    decide
  have hc15 : 1 < (15:ℕ).primeFactors.card := by
    rw [show 15 = 3*5 by rfl, Nat.primeFactors_mul (by decide) (by decide),
      (show Nat.Prime 3 by decide).primeFactors, (show Nat.Prime 5 by decide).primeFactors]
    decide
  simp [primorialDual, primePowerPacket_dual_zero 10 p a (by decide) hc10 hp,
    primePowerPacket_dual_zero 15 p a (by decide) hc15 hp]

theorem primorialDual_one : primorialDual (fun k => if k = 0 then 0 else 1) = 1 := by
  norm_num [primorialDual, mobiusDifference_one]

def primorialRow (k : Fin 15) : ℤ := 3*witnessRow 1 k - 2*witnessRow 3 k

theorem primorialRow_mass : (∑ k, primorialRow k) = 1 := by
  unfold primorialRow
  rw [witnessRow_eq_table]
  decide

theorem primorialRow_pairing (f : ℕ → ℝ) (h0 : f 0 = 0) :
    (∑ k : Fin 15, (primorialRow k : ℝ)*f (k+1)) = primorialDual f := by
  simp only [primorialRow, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, sub_mul,
    mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [witnessRow_pairing 1 f h0, witnessRow_pairing 3 f h0]
  rfl

theorem primorialDual_error_floor (f : ℕ → ℝ) (h0 : f 0 = 0) (hd : primorialDual f = 0) :
    (1:ℝ)/3880 ≤ ∑ k : Fin 15, (1-f (k+1))^2 / (coordinateWeight k : ℝ) := by
  have hmass : (∑ k, (primorialRow k : ℝ)) = 1 := by exact_mod_cast primorialRow_mass
  have hnorm : (∑ k, (coordinateWeight k : ℝ)*(primorialRow k : ℝ)^2) = 3880 := by
    exact_mod_cast primorialDual_normSq
  have hpair : (∑ k : Fin 15, (primorialRow k : ℝ)*f (k+1)) = 0 := by
    rw [primorialRow_pairing f h0, hd]
  have hsignal : (∑ k : Fin 15, (primorialRow k : ℝ)*(1-f (k+1))) = 1 := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [hmass, hpair, sub_zero]
  have h := finite_weighted_dual_bound Finset.univ
    (fun k : Fin 15 => (coordinateWeight k : ℝ)) (fun k => (primorialRow k : ℝ))
    (fun k => 1-f (k+1)) (by
      intro k _
      unfold coordinateWeight
      push_cast
      positivity) (by rw [hnorm]; norm_num)
  rw [hnorm, hsignal] at h
  norm_num at h ⊢
  exact h

theorem primorialDual_sum (s : Finset ℕ) (c : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    primorialDual (fun k => ∑ q ∈ s, c q*f q k) = ∑ q ∈ s, c q*primorialDual (f q) := by
  unfold primorialDual
  rw [mobiusDifference_sum, mobiusDifference_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem primePowers_primorials_error_floor (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, (∃ p a, p.Prime ∧ q = p^a) ∨ ∃ n, q = primorial n) :
    (1:ℝ)/3880 ≤
      ∑ k : Fin 15, (1-∑ q ∈ s, c q*ramanujanPacket q (k+1))^2 /
        (coordinateWeight k : ℝ) := by
  apply primorialDual_error_floor (fun k => ∑ q ∈ s, c q*ramanujanPacket q k)
  · simp [ramanujanPacket, residue]
  · rw [primorialDual_sum]
    apply Finset.sum_eq_zero
    intro q hq
    rcases hs q hq with ⟨p,a,hp,rfl⟩ | ⟨n,rfl⟩
    · rw [primorialDual_primePowerPacket_zero p a hp, mul_zero]
    · rw [primorialDual_primorialPacket_zero n, mul_zero]

end
end RiemannResearch.RH.Pareto
