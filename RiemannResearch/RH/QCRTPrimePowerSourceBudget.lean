/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTRawSourceBudget
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The actual prime-power admission rows and their complete raw-source budget

Source: CanonicalPrimePowerUpdatesResearch20261107, Section 2.
The arithmetic LCM conditions of the finite raw-source theorem are discharged
for every new conductor pa e, e|R, at L=aR -> M=paR. The application a=p^(k-1)
is explicit. No response/inverse-collocation norm bound is inferred.
-/

namespace Nat

theorem lcm_coprime_admission {p R e : ℕ} (hcop : Coprime p R) (he : e ∣ R) :
    lcm R (p * e) = p * R := by
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact ⟨p, by ring⟩
    · exact Nat.mul_dvd_mul_left p he
  · apply hcop.mul_dvd_of_dvd_of_dvd
    · exact (dvd_mul_right p e).trans (Nat.dvd_lcm_right R (p * e))
    · exact Nat.dvd_lcm_left R (p * e)

theorem lcm_scaled_coprime_admission {p a R e : ℕ}
    (hcop : Coprime p R) (he : e ∣ R) :
    lcm (a * R) ((p * a) * e) = (p * a) * R := by
  have he1 : (p * a) * e = a * (p * e) := by ring
  have he2 : (p * a) * R = a * (p * R) := by ring
  rw [he1, he2, Nat.lcm_mul_left, lcm_coprime_admission hcop he]

end Nat

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTPrimePowerSourceBudget
open ZetaTwoHilbert ZetaTwoProbability QCRTFiniteCollocation QCRTNestedCutoffs
open QPhysicalDifference QDivisibilityDensity QCRTRawSourceBudget

theorem actual_admission_rows (p a R : ℕ) (hp : p.Prime) (ha : 0 < a)
    (_hR : 0 < R) (hcop : Nat.Coprime p R) :
    ∀ e ∈ R.divisors,
      2 ≤ (p * a) * e ∧ (p * a) * e ∣ (p * a) * R ∧
        Nat.lcm (a * R) ((p * a) * e) = (p * a) * R := by
  intro e he
  have heR := Nat.dvd_of_mem_divisors he
  have hepos := Nat.pos_of_mem_divisors he
  have hpa : p ≤ p * a := by
    simpa only [mul_one] using Nat.mul_le_mul_left p (show 1 ≤ a by omega)
  have hpae : p * a ≤ (p * a) * e := by
    simpa only [mul_one] using Nat.mul_le_mul_left (p * a) (show 1 ≤ e by omega)
  exact ⟨hp.two_le.trans (hpa.trans hpae), Nat.mul_dvd_mul_left (p * a) heR,
    Nat.lcm_scaled_coprime_admission hcop heR⟩

theorem actual_admission_source_sq_le (p a R : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hR : 0 < R) (hcop : Nat.Coprime p R) (hL : 2 ≤ a * R) :
    (∑ e ∈ R.divisors,
      (inner ℝ (target ((p * a) * R) - canonical (a * R) hL)
        (differenceCLM (qResidue ((p * a) * e)))) ^ 2) ≤
      (2 * zetaTwo / ((p * a : ℕ) : ℝ) ^ 2) *
        ((1 / ((a * R : ℕ) : ℝ) ^ 2 - 1 / (((p * a) * R : ℕ) : ℝ) ^ 2) ^ 2 +
          leakage (a * R) hL) := by
  exact sum_new_difference_source_sq_le (a * R) ((p * a) * R) (p * a) hL
    (Nat.mul_pos (Nat.mul_pos hp.pos ha) hR) (Nat.mul_pos hp.pos ha) R.divisors
    (actual_admission_rows p a R hp ha hR hcop)

theorem prime_power_admission_source_sq_le (p k R : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
    (hR : 0 < R) (hcop : Nat.Coprime p R) (hL : 2 ≤ p ^ (k - 1) * R) :
    (∑ e ∈ R.divisors,
      (inner ℝ (target (p ^ k * R) - canonical (p ^ (k - 1) * R) hL)
        (differenceCLM (qResidue (p ^ k * e)))) ^ 2) ≤
      (2 * zetaTwo / ((p ^ k : ℕ) : ℝ) ^ 2) *
        ((1 / ((p ^ (k - 1) * R : ℕ) : ℝ) ^ 2 - 1 / ((p ^ k * R : ℕ) : ℝ) ^ 2) ^ 2 +
          leakage (p ^ (k - 1) * R) hL) := by
  have he : p * p ^ (k - 1) = p ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  simpa only [he] using actual_admission_source_sq_le p (p ^ (k - 1)) R hp
    (pow_pos hp.pos _) hR hcop hL

end RiemannResearch.RH.QCRTPrimePowerSourceBudget
