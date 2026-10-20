/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerPrimorial
import RiemannResearch.RH.QPrimePowerSieveMellin
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Actual primorial sieve Euler steps

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
Exact prime updates and unchanged nonprime stages; no asymptotic hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve

theorem primeFactors_div_prime_of_squarefree (L p : ℕ) (hL : 0 < L)
    (hp : p.Prime) (hsf : Squarefree L) (hpL : p ∣ L) :
    (L / p).primeFactors = L.primeFactors.erase p := by
  have he : p * (L / p) = L := Nat.mul_div_cancel' hpL
  have hcop : Nat.Coprime p (L / p) :=
    Nat.coprime_of_squarefree_mul (he.symm ▸ hsf)
  have hpn : ¬ p ∣ L / p := hp.coprime_iff_not_dvd.mp hcop
  have hquot : L / p ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hL hpL) hp.pos)
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_erase]
  constructor
  · rintro ⟨hq, hqd, _⟩
    refine ⟨?_, hq, hqd.trans (Nat.div_dvd_of_dvd hpL), hL.ne'⟩
    intro hqp
    exact hpn (hqp ▸ hqd)
  · rintro ⟨hqp, hq, hqL, _⟩
    refine ⟨hq, ?_, hquot⟩
    rw [← he] at hqL
    rcases hq.dvd_mul.mp hqL with hqpdiv | hqdiv
    · exact (hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqpdiv)).elim
    · exact hqdiv

theorem primeFactors_primorial_div_prime (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H) :
    (primorial H / p).primeFactors = H.primesLE.erase p := by
  rw [primeFactors_div_prime_of_squarefree _ p (primorial_pos H) hp
    (squarefree_primorial H) (hp.dvd_primorial_iff.mpr hpH), primeFactors_primorial]

def primePowerEulerFactor (p H : ℕ) (σ : ℝ) : ℝ :=
  (p : ℝ) ^ (-σ) * ∏ q ∈ H.primesLE.erase p, (1 - (q : ℝ) ^ (-σ))

theorem primePowerEulerFactor_succ_prime (p H : ℕ) (hpH : p ≤ H)
    (hprime : (H + 1).Prime) (σ : ℝ) :
    primePowerEulerFactor p (H + 1) σ =
      primePowerEulerFactor p H σ * (1 - ((H + 1 : ℕ) : ℝ) ^ (-σ)) := by
  have hne : H + 1 ≠ p := by omega
  have hnot : H + 1 ∉ H.primesLE.erase p := by
    intro h
    have hH := (Nat.mem_primesLE.mp (Finset.mem_of_mem_erase h)).1
    omega
  unfold primePowerEulerFactor
  rw [Nat.primesLE_succ, if_pos hprime, Finset.erase_insert_of_ne hne,
    Finset.prod_insert hnot]
  ring

theorem primePowerEulerFactor_succ_not_prime (p H : ℕ)
    (hprime : ¬ (H + 1).Prime) (σ : ℝ) :
    primePowerEulerFactor p (H + 1) σ = primePowerEulerFactor p H σ := by
  simp only [primePowerEulerFactor, Nat.primesLE_succ, if_neg hprime]

theorem primorial_succ_not_prime (H : ℕ) (hprime : ¬ (H + 1).Prime) :
    primorial (H + 1) = primorial H := by
  simp only [primorial_eq_prod_primesLE, Nat.primesLE_succ, if_neg hprime]

theorem sieveSlope_primorial_euler (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H) :
    sieveSlope (primorial H) p = primePowerEulerFactor p H 1 := by
  have h := sieveCoefficient_rpow_sum (primorial H) p
    (Nat.mem_divisors.mpr ⟨hp.dvd_primorial_iff.mpr hpH, primorial_ne_zero H⟩)
    (squarefree_primorial H) 1 (by norm_num)
  rw [primeFactors_primorial_div_prime p H hp hpH] at h
  simpa only [sieveSlope, primePowerEulerFactor, Real.rpow_neg_one, div_eq_mul_inv] using h

theorem primePowerEulerFactor_pos (p H : ℕ) (hp : 0 < p) (σ : ℝ) (hσ : 0 < σ) :
    0 < primePowerEulerFactor p H σ := by
  apply mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hp) _)
  apply Finset.prod_pos
  intro q hq
  have hprime := Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hq)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith))

theorem sieveSlope_primorial_positive (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H) :
    0 < sieveSlope (primorial H) p := by
  rw [sieveSlope_primorial_euler p H hp hpH]
  exact primePowerEulerFactor_pos p H hp.pos 1 (by norm_num)

theorem sieveSlope_primorial_succ_prime (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H)
    (hprime : (H + 1).Prime) :
    sieveSlope (primorial (H + 1)) p =
      sieveSlope (primorial H) p * (1 - 1 / ((H + 1 : ℕ) : ℝ)) := by
  rw [sieveSlope_primorial_euler p (H + 1) hp (by omega),
    primePowerEulerFactor_succ_prime p H hpH hprime,
    ← sieveSlope_primorial_euler p H hp hpH]
  simp only [Real.rpow_neg_one, one_div]

theorem sieveSlope_primorial_succ_lt (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H)
    (hprime : (H + 1).Prime) :
    sieveSlope (primorial (H + 1)) p < sieveSlope (primorial H) p := by
  rw [sieveSlope_primorial_succ_prime p H hp hpH hprime]
  have ha := sieveSlope_primorial_positive p H hp hpH
  have hq : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
  have hi : (0 : ℝ) < 1 / ((H + 1 : ℕ) : ℝ) := by positivity
  nlinarith

theorem sieveSlope_primorial_succ_le (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H) :
    sieveSlope (primorial (H + 1)) p ≤ sieveSlope (primorial H) p := by
  by_cases hprime : (H + 1).Prime
  · exact (sieveSlope_primorial_succ_lt p H hp hpH hprime).le
  · rw [primorial_succ_not_prime H hprime]

theorem sieveSlope_primorial_plateau (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H)
    (he : sieveSlope (primorial (H + 1)) p = sieveSlope (primorial H) p) :
    sieveVector (primorial (H + 1)) p = sieveVector (primorial H) p := by
  have hn : ¬ (H + 1).Prime := by
    intro hprime
    have hlt := sieveSlope_primorial_succ_lt p H hp hpH hprime
    rw [he] at hlt
    exact (lt_irrefl _ hlt)
  rw [primorial_succ_not_prime H hn]

open QMellinTransfer in
theorem sieveVector_primorial_mellin_exact (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    (σ : ℂ) * qMellin (sieveVector (primorial H) p) σ = riemannZeta σ *
      ((primePowerEulerFactor p H σ - sieveSlope (primorial H) p : ℝ) : ℂ) := by
  rw [sieveVector_mellin_euler_exact (primorial H) p
    (Nat.mem_divisors.mpr ⟨hp.dvd_primorial_iff.mpr hpH, primorial_ne_zero H⟩)
    (squarefree_primorial H) σ hσ hσ1,
    primeFactors_primorial_div_prime p H hp hpH]
  rfl

open QMellinTransfer in
theorem sieveVector_primorial_real_mellin_exact (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    ((σ : ℂ) * qMellin (sieveVector (primorial H) p) σ).re =
      (riemannZeta σ).re * (primePowerEulerFactor p H σ - sieveSlope (primorial H) p) := by
  rw [sieveVector_primorial_mellin_exact p H hp hpH σ hσ hσ1]
  simp

end RiemannResearch.RH.QPrimePowerSieve
