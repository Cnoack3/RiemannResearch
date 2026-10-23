/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.NoorLogarithmDensity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-!
# Rigidity of summable sequences with vanishing sums over multiples

Source: the user's continuation agenda, Section H1. This is the arithmetic
core of the harmonic-mass annihilator argument. The factorial sieve is the
one already formalized in `Analysis.NoorLogarithmDensity`.

The complete-Q first-moment consumer is in `RH.QSignedTailRigidity`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.SummableMultiplesRigidity

def sift (F : ℕ → ℝ) (N k n : ℕ) : ℝ :=
  if 0 < n ∧ k ∣ n ∧ Nat.Coprime (n / k) N.factorial then F n else 0

theorem finite_sieve (F : ℕ → ℝ) (hF0 : F 0 = 0) (Q k n : ℕ) (hQ : Q ≠ 0) :
    (∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d : ℝ) *
      (if k * d ∣ n then F n else 0)) =
    if 0 < n ∧ k ∣ n ∧ Nat.Coprime (n / k) Q then F n else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [hF0]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hkn : k ∣ n
  · have hdiv (d : ℕ) : k * d ∣ n ↔ d ∣ n / k := by
      rw [Nat.dvd_div_iff_mul_dvd hkn]
    calc
      _ = F n * (∑ d ∈ Q.divisors,
          if d ∣ n / k then (ArithmeticFunction.moebius d : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdvd : d ∣ n / k
        · simp only [if_pos hdvd, if_pos ((hdiv d).mpr hdvd)]
          ring
        · have hkdvd : ¬ k * d ∣ n := fun h => hdvd ((hdiv d).mp h)
          simp [hdvd, hkdvd]
      _ = F n * (if Nat.Coprime (n / k) Q then 1 else 0) := by
        rw [← Finset.sum_filter, Noor.moebius_sift Q (n / k) hQ]
      _ = _ := by
        by_cases hc : Nat.Coprime (n / k) Q <;> simp [hnpos, hkn, hc]
  · rw [if_neg (by tauto)]
    apply Finset.sum_eq_zero
    intro d hd
    have hkdvd : ¬ k * d ∣ n := fun h => hkn ((Nat.dvd_mul_right k d).trans h)
    simp [hkdvd]

theorem sift_eventually (F : ℕ → ℝ) (hF0 : F 0 = 0) (k n : ℕ) (hk : 0 < k) :
    ∀ᶠ N : ℕ in atTop, sift F N k n = if n = k then F k else 0 := by
  filter_upwards [eventually_ge_atTop n] with N hN
  by_cases hnk : n = k
  · subst n
    simp [sift, hk, Nat.ne_of_gt hk]
  by_cases hn : n = 0
  · subst n
    simp [sift, (Nat.ne_of_gt hk).symm, hF0]
  have hnpos := Nat.pos_of_ne_zero hn
  by_cases hkn : k ∣ n
  · have hmpos : 0 < n / k := Nat.div_pos (Nat.le_of_dvd hnpos hkn) hk
    have hmdvd : n / k ∣ N.factorial :=
      Nat.dvd_factorial hmpos ((Nat.div_le_self n k).trans hN)
    have hmne : n / k ≠ 1 := by
      intro he
      have hmul := Nat.mul_div_cancel' hkn
      rw [he, mul_one] at hmul
      exact hnk hmul.symm
    have hnc : ¬ Nat.Coprime (n / k) N.factorial := by
      simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_left hmdvd] using hmne
    simp [sift, hnc, hnk]
  · simp [sift, hkn, hnk]

theorem summable_multiples (F : ℕ → ℝ) (hF : Summable F) (k : ℕ) :
    Summable (fun n => if k ∣ n then F n else 0) := by
  apply Summable.of_norm_bounded hF.norm
  intro n
  split_ifs <;> simp

/-- The sums over all positive multiples determine an absolutely summable
sequence, including its signs. This is not a positivity argument. -/
theorem eq_zero_of_multiples_tsum_eq_zero (F : ℕ → ℝ) (hF : Summable F)
    (hF0 : F 0 = 0)
    (hzero : ∀ k : ℕ, 0 < k → (∑' n, if k ∣ n then F n else 0) = 0) :
    F = 0 := by
  classical
  funext k
  by_cases hk0 : k = 0
  · simpa [hk0] using hF0
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hsum (N : ℕ) : (∑' n, sift F N k n) = 0 := by
    have he (n : ℕ) : sift F N k n =
        ∑ d ∈ N.factorial.divisors, (ArithmeticFunction.moebius d : ℝ) *
          (if k * d ∣ n then F n else 0) :=
      (finite_sieve F hF0 N.factorial k n (Nat.factorial_ne_zero N)).symm
    simp only [he]
    rw [Summable.tsum_finsetSum (fun d hd =>
      (summable_multiples F hF (k * d)).mul_left (ArithmeticFunction.moebius d : ℝ))]
    apply Finset.sum_eq_zero
    intro d hd
    rw [tsum_mul_left, hzero (k * d) (Nat.mul_pos hk (Nat.pos_of_mem_divisors hd)),
      mul_zero]
  have hlim : Tendsto (fun N => ∑' n, sift F N k n) atTop (𝓝 (F k)) := by
    have ht := tendsto_tsum_of_dominated_convergence hF.norm
      (f := fun N n => sift F N k n)
      (g := fun n => if n = k then F k else 0)
      (fun n => tendsto_const_nhds.congr'
        ((sift_eventually F hF0 k n hk).mono (fun _ h => h.symm)))
      (Eventually.of_forall (fun N n => by
        dsimp [sift]
        split_ifs <;> simp))
    simpa using ht
  have hlim0 : Tendsto (fun N => ∑' n, sift F N k n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hsum] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
  exact tendsto_nhds_unique hlim hlim0

end RiemannResearch.Analysis.SummableMultiplesRigidity
