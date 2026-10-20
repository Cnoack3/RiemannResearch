/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSieve
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Signed primorial sieve heads and complete Gram energy

Source: the user's signed-modification request, 20 October 2026.
This investigation is separate from the two-target Mellin RH criterion.
Every vector is an actual finite legal synthesis with all divisors retained.
Exact finite-head balance is proved; a uniform complete-Q energy bound
for growing heads remains Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets

/-- A finite signed mixture of the actual primorial gcd-class sieves. -/
def signedSieveVector (p : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : QHilbert :=
  ∑ H ∈ S, w H • sieveVector (primorial H) p

theorem signedSieveVector_mem (p : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) :
    signedSieveVector p S w ∈ qSquarefreeCRTSpan := by
  apply qSquarefreeCRTSpan.sum_mem
  intro H hH
  exact qSquarefreeCRTSpan.smul_mem _ (sieveVector_mem_squarefreeSpan _ _
    (primorial_pos H) (squarefree_primorial H))

/-- Exact common head, including both total mass and arithmetic drift. -/
theorem signedSieveVector_head_exact (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (w : ℕ → ℝ) (x n : ℕ)
    (hcut : ∀ H ∈ S, max p x ≤ H) (hn : n ≤ x) :
    qSequence (signedSieveVector p S w) n =
      (∑ H ∈ S, w H) * (Nat.log p n : ℝ) -
        (∑ H ∈ S, w H * sieveSlope (primorial H) p) * (n : ℝ) := by
  change qSequenceLinear (∑ H ∈ S, w H • sieveVector (primorial H) p) n = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ H ∈ S, w H * qSequence (sieveVector (primorial H) p) n) = _
  have he (H : ℕ) (hH : H ∈ S) :
      qSequence (sieveVector (primorial H) p) n =
        (Nat.log p n : ℝ) - sieveSlope (primorial H) p * (n : ℝ) := by
    have hpH : p ≤ H := (le_max_left p x).trans (hcut H hH)
    have hxH : x ≤ H := (le_max_right p x).trans (hcut H hH)
    exact qSequence_sieveVector_head _ _ H n (primorial_pos H) hp
      (squarefree_primorial H) (hp.dvd_primorial_iff.mpr hpH)
      (fun q hq hqH => hq.dvd_primorial_iff.mpr hqH) (hn.trans hxH)
  rw [Finset.sum_congr rfl (fun H hH => congrArg (w H * ·) (he H hH))]
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
  rw [Finset.sum_mul, Finset.sum_mul]

/-- Finite balance supplies an exact target head, without asserting norm control. -/
theorem signedSieveVector_head_of_balanced (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (w : ℕ → ℝ) (x n : ℕ)
    (hcut : ∀ H ∈ S, max p x ≤ H) (hn : n ≤ x)
    (hmass : ∑ H ∈ S, w H = 1)
    (hdrift : ∑ H ∈ S, w H * sieveSlope (primorial H) p = 0) :
    qSequence (signedSieveVector p S w) n = (Nat.log p n : ℝ) := by
  rw [signedSieveVector_head_exact p hp S w x n hcut hn, hmass, hdrift]
  ring

/-- The full infinite-Q Gram energy retains every signed cross term. -/
theorem signedSieveVector_norm_sq_exact (p : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) :
    ‖signedSieveVector p S w‖ ^ 2 =
      ∑ H ∈ S, ∑ K ∈ S, w H * w K *
        inner ℝ (sieveVector (primorial H) p) (sieveVector (primorial K) p) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [signedSieveVector, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  simp_rw [mul_assoc]
  apply Finset.sum_congr rfl
  intro H hH
  apply Finset.sum_congr rfl
  intro K hK
  rw [real_inner_comm]

private theorem sieveSlope_primorial_pos (p H : ℕ) (hp : p.Prime) (hpH : p ≤ H) :
    0 < sieveSlope (primorial H) p := by
  have hdiv := hp.dvd_primorial_iff.mpr hpH
  rw [sieveSlope_eq_totient _ _ (primorial_pos H)
    (Nat.mem_divisors.mpr ⟨hdiv, primorial_ne_zero H⟩)]
  have hquot : 0 < primorial H / p :=
    Nat.div_pos (Nat.le_of_dvd (primorial_pos H) hdiv) hp.pos
  apply div_pos
  · exact_mod_cast (Nat.totient_pos.mpr hquot)
  · exact_mod_cast primorial_pos H

/-- Positive mixtures cannot cancel the strictly positive arithmetic slopes. -/
theorem balanced_sieve_has_negative_weight (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (w : ℕ → ℝ) (hcut : ∀ H ∈ S, p ≤ H)
    (hmass : ∑ H ∈ S, w H = 1)
    (hdrift : ∑ H ∈ S, w H * sieveSlope (primorial H) p = 0) :
    ∃ H ∈ S, w H < 0 := by
  by_contra hneg
  have hnonneg : ∀ H ∈ S, 0 ≤ w H := by
    intro H hH
    exact le_of_not_gt (fun hw => hneg ⟨H, hH, hw⟩)
  have hwzero (H : ℕ) (hH : H ∈ S) : w H = 0 := by
    have hle := Finset.single_le_sum (fun K hK =>
      mul_nonneg (hnonneg K hK) (sieveSlope_primorial_pos p K hp (hcut K hK)).le) hH
    rw [hdrift] at hle
    have he : w H * sieveSlope (primorial H) p = 0 :=
      le_antisymm hle (mul_nonneg (hnonneg H hH)
        (sieveSlope_primorial_pos p H hp (hcut H hH)).le)
    exact (mul_eq_zero.mp he).resolve_right
      (ne_of_gt (sieveSlope_primorial_pos p H hp (hcut H hH)))
  have hz : ∑ H ∈ S, w H = 0 := Finset.sum_eq_zero hwzero
  rw [hmass] at hz
  exact one_ne_zero hz

end RiemannResearch.RH.QPrimePowerSieve
