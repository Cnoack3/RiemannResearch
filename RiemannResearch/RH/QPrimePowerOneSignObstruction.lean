/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSignedObstruction
import RiemannResearch.RH.QPrimePowerSieveUniform
import RiemannResearch.RH.PrimeSieveSecantLimits
import RiemannResearch.Analysis.SignedBalancedRows
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q obstruction for one-sign-change signed sieves

Source: user-provided QParityHeadContinuationResearch20261020.md, Section 5,
for the proposed positive transport refinement. The finite transport identity
and actual slope-plateau provider remove both a variation bound and a strict
slope-separation hypothesis. This concerns this specific primorial sieve family,
not arbitrary elements of the squarefree span.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability QMellinTransfer PrimePowerTarget
open RiemannResearch.Analysis.SignedBalancedRows

/-- Negatives precede positives in cutoff order; zero coefficients are irrelevant. -/
def NegativeBeforePositive (S : Finset ℕ) (w : ℕ → ℝ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, w i < 0 → 0 < w j → i ≤ j

theorem sieveSlope_primorial_le_of_le (p H K : ℕ) (hp : p.Prime)
    (hpH : p ≤ H) (hHK : H ≤ K) :
    sieveSlope (primorial K) p ≤ sieveSlope (primorial H) p := by
  have ha : Antitone (fun n => sieveSlope (primorial (p + n)) p) := by
    apply antitone_nat_of_succ_le
    intro n
    exact sieveSlope_primorial_succ_le p (p + n) hp (by omega)
  have hh := ha (show H - p ≤ K - p by omega)
  simpa only [Nat.add_sub_of_le hpH, Nat.add_sub_of_le (hpH.trans hHK)] using hh

/-- Equal positive sieve slopes force equal Euler probes, including long plateaux. -/
theorem primePowerEulerFactor_eq_of_slope_eq (p H K : ℕ) (hp : p.Prime)
    (hpH : p ≤ H) (hHK : H ≤ K) (σ : ℝ)
    (he : sieveSlope (primorial K) p = sieveSlope (primorial H) p) :
    primePowerEulerFactor p K σ = primePowerEulerFactor p H σ := by
  let a : ℕ → ℝ := fun n => sieveSlope (primorial (p + n)) p
  let u : ℕ → ℝ := fun n => primePowerEulerFactor p (p + n) σ
  have ha : Antitone a := by
    apply antitone_nat_of_succ_le
    intro n
    exact sieveSlope_primorial_succ_le p (p + n) hp (by omega)
  have hs : ∀ n, a (n + 1) = a n → u (n + 1) = u n := by
    intro n hn
    have hnp : ¬ (p + n + 1).Prime := by
      intro hprime
      have hlt := sieveSlope_primorial_succ_lt p (p + n) hp (by omega) hprime
      change a (n + 1) < a n at hlt
      rw [hn] at hlt
      exact lt_irrefl _ hlt
    exact primePowerEulerFactor_succ_not_prime p (p + n) hnp σ
  have hind : p + (H - p + (K - H)) = K := by omega
  have hh := PrimeSieveSecant.equal_probe_of_equal_slopes a u ha hs
    (H - p) (K - H) (by
      dsimp [a]
      rw [hind, Nat.add_sub_of_le hpH]
      exact he)
  simpa only [u, hind, Nat.add_sub_of_le hpH] using hh

/-- Uniform determinant estimate with the exact zero-gap case included. -/
theorem sieve_determinant_uniform (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ ε > 0, ∃ N : ℕ, p ≤ N ∧ ∀ H ≥ N, ∀ K ≥ H,
      |sieveSlope (primorial H) p * primePowerEulerFactor p K σ -
        sieveSlope (primorial K) p * primePowerEulerFactor p H σ| ≤
      ε * (sieveSlope (primorial H) p - sieveSlope (primorial K) p) := by
  intro ε hε
  obtain ⟨N, hpN, hN⟩ := sieve_intercept_uniform p hp σ hσ hσ1 ε hε
  refine ⟨N, hpN, ?_⟩
  intro H hH K hK
  have hle := sieveSlope_primorial_le_of_le p H K hp (hpN.trans hH) hK
  by_cases he : sieveSlope (primorial K) p = sieveSlope (primorial H) p
  · rw [primePowerEulerFactor_eq_of_slope_eq p H K hp (hpN.trans hH) hK σ he, he]
    simp
  · have hg : 0 < sieveSlope (primorial H) p - sieveSlope (primorial K) p :=
      sub_pos.mpr (lt_of_le_of_ne hle he)
    have hb := (hN H hH K hK).le
    unfold PrimeSieveSecant.intercept at hb
    rw [abs_div, abs_of_pos hg] at hb
    exact (div_le_iff₀ hg).mp hb

/-- One sign change controls the scalar Euler sum without any variation bound. -/
theorem signedSieveVector_oneSign_euler_uniform (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ ε > 0, ∃ N : ℕ, p ≤ N ∧
      ∀ (S : Finset ℕ) (w : ℕ → ℝ),
      (∀ H ∈ S, N ≤ H) →
      (∑ H ∈ S, w H = 1) →
      (∑ H ∈ S, w H * sieveSlope (primorial H) p = 0) →
      NegativeBeforePositive S w →
      |∑ H ∈ S, w H * primePowerEulerFactor p H σ| ≤ ε := by
  intro ε hε
  obtain ⟨N, hpN, hN⟩ := sieve_determinant_uniform p hp σ hσ hσ1 ε hε
  refine ⟨N, hpN, ?_⟩
  intro S w hcut hmass hdrift hsign
  apply signed_probe_bound S w
    (fun H => sieveSlope (primorial H) p) (fun H => primePowerEulerFactor p H σ)
    (fun H hH => sieveSlope_primorial_positive p H hp (hpN.trans (hcut H hH)))
    hmass hdrift ε
  intro i hi j hj hwi hwj
  exact hN i (hcut i hi) j (hsign i hi j hj hwi hwj)

/-- Uniform small Mellin signature, even for unbounded coefficient variation. -/
theorem signedSieveVector_oneSign_mellin_uniform (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1) :
    ∀ ε > 0, ∃ N : ℕ, p ≤ N ∧
      ∀ (S : Finset ℕ) (w : ℕ → ℝ),
      (∀ H ∈ S, N ≤ H) →
      (∑ H ∈ S, w H = 1) →
      (∑ H ∈ S, w H * sieveSlope (primorial H) p = 0) →
      NegativeBeforePositive S w →
      ‖(σ : ℂ) * qMellin (signedSieveVector p S w) σ‖ < ε := by
  intro ε hε
  have hz : 0 < ‖riemannZeta (σ : ℂ)‖ + 1 := by positivity
  obtain ⟨N, hpN, hN⟩ := signedSieveVector_oneSign_euler_uniform p hp σ
    (by linarith) hσ1 (ε / (‖riemannZeta (σ : ℂ)‖ + 1)) (div_pos hε hz)
  refine ⟨N, hpN, ?_⟩
  intro S w hcut hmass hdrift hsign
  rw [signedSieveVector_balanced_mellin_exact p hp S w
    (fun H hH => hpN.trans (hcut H hH)) hdrift σ hσ (ne_of_lt hσ1),
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb := (le_div_iff₀ hz).mp (hN S w hcut hmass hdrift hsign)
  have ha := abs_nonneg (∑ H ∈ S, w H * primePowerEulerFactor p H σ)
  have hn := norm_nonneg (riemannZeta (σ : ℂ))
  by_cases he : (∑ H ∈ S, w H * primePowerEulerFactor p H σ) = 0
  · simp only [he, abs_zero, mul_zero]; exact hε
  · have ha' := abs_pos.mpr he
    nlinarith

theorem signedSieveVector_oneSign_quantitative_lower (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1) :
    ∃ N : ℕ, p ≤ N ∧ ∀ H ≥ N, ∀ (S : Finset ℕ) (w : ℕ → ℝ),
      (∀ K ∈ S, H ≤ K) →
      (∑ K ∈ S, w K = 1) →
      (∑ K ∈ S, w K * sieveSlope (primorial K) p = 0) →
      NegativeBeforePositive S w →
      ((2 * σ - 1) / (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2)) *
        (H : ℝ) ^ (2 * σ - 1) ≤ ‖signedSieveVector p S w - qTarget p hp.one_lt‖ ^ 2 := by
  have hden : 0 < (p : ℝ) ^ σ - 1 := sub_pos.mpr
    (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith))
  obtain ⟨N, hpN, hN⟩ := signedSieveVector_oneSign_mellin_uniform p hp σ hσ hσ1
    (1 / (2 * ((p : ℝ) ^ σ - 1))) (by positivity)
  refine ⟨N, hpN, ?_⟩
  intro H hH S w hcut hmass hdrift hsign
  apply qTarget_head_match_quantitative_lower p hp.one_lt (signedSieveVector p S w)
    σ hσ H (by have := hp.two_le; omega)
  · intro n hn
    exact signedSieveVector_head_of_balanced p hp S w H n
      (fun K hK => max_le ((hpN.trans hH).trans (hcut K hK)) (hcut K hK))
      hn hmass hdrift
  · exact (hN S w (fun K hK => hH.trans (hcut K hK)) hmass hdrift hsign).le

theorem signedSieveVector_oneSign_norm_tendsto_atTop
    (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (H : ℕ → ℕ) (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hH : Tendsto H atTop atTop)
    (hcut : ∀ᶠ j in atTop, ∀ K ∈ S j, H j ≤ K)
    (hmass : ∀ᶠ j in atTop, ∑ K ∈ S j, w j K = 1)
    (hdrift : ∀ᶠ j in atTop, ∑ K ∈ S j, w j K * sieveSlope (primorial K) p = 0)
    (hsign : ∀ᶠ j in atTop, NegativeBeforePositive (S j) (w j)) :
    Tendsto (fun j => ‖signedSieveVector p (S j) (w j)‖) atTop atTop := by
  obtain ⟨N, _, hN⟩ := signedSieveVector_oneSign_quantitative_lower p hp σ hσ hσ1
  apply norm_tendsto_atTop_of_head_lower p hp.one_lt σ hσ H
    (fun j => signedSieveVector p (S j) (w j)) hH
  filter_upwards [hH.eventually (eventually_ge_atTop N), hcut, hmass, hdrift, hsign]
    with j hj hcutj hmassj hdriftj hsignj
  exact hN (H j) hj (S j) (w j) hcutj hmassj hdriftj hsignj

/-- The opposite orientation of a single sign change is infeasible. -/
theorem balanced_sieve_not_positive_before_negative
    (p : ℕ) (hp : p.Prime) (S : Finset ℕ) (w : ℕ → ℝ)
    (hcut : ∀ H ∈ S, p ≤ H)
    (hmass : ∑ H ∈ S, w H = 1)
    (hdrift : ∑ H ∈ S, w H * sieveSlope (primorial H) p = 0)
    (hreverse : ∀ i ∈ S, ∀ j ∈ S, w i < 0 → 0 < w j → j ≤ i) :
    False := by
  exact not_balanced_of_reversed_slopes S w (fun H => sieveSlope (primorial H) p)
    (fun H hH => sieveSlope_primorial_positive p H hp (hcut H hH)) hmass hdrift
    (fun i hi j hj hwi hwj =>
      sieveSlope_primorial_le_of_le p j i hp (hcut j hj) (hreverse i hi j hj hwi hwj))

end RiemannResearch.RH.QPrimePowerSieve
