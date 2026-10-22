/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteClassDirichlet
import RiemannResearch.RH.QRationalTailPoincare
import RiemannResearch.RH.QRationalTailDirichlet
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalCoprimeMinimum
import RiemannResearch.RH.QRationalCoprimeLegality
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QRationalSignedTailLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A coprime three-site lower bound for the actual rational minimum

Source: the established residue-jump identity and a direct three-site
weighted Cauchy--Schwarz argument, user-directed investigation, 20 October 2026.
This gives finite obstructions to error-free signed absorption. A decreasing
lower bound does not obstruct squarefree closure or prove a positive limit.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.Analysis.FiniteClassDirichlet
open ArithmeticCumulative

theorem divisorFit_coprime_jump (L q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime q L) (c : ℕ → ℝ) :
    divisorFit L c 1 + divisorFit L c (q - 1) - divisorFit L c q = 0 := by
  unfold divisorFit
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hd1 : d = 1
  · simp [hd1, residueFraction, Nat.mod_one]
  have hd2 : 2 ≤ d := by have := Nat.pos_of_mem_divisors hd; omega
  have hn : ¬ d ∣ q := by
    intro h
    have hh := Nat.dvd_gcd h (Nat.dvd_of_mem_divisors hd)
    rw [hcop.gcd_eq_one] at hh
    exact hd1 (Nat.dvd_one.mp hh)
  have hh := SquarefreeRadicalDifference.residueFraction_difference d q hd2 hq
  rw [if_neg hn, sub_zero] at hh
  have hfirst : residueFraction d 1 = 1 / (d : ℝ) := by
    simp [residueFraction, Nat.mod_eq_of_lt (by omega : 1 < d)]
  rw [hfirst, ← hh]
  ring

def coprimeThreeSiteResistance (L q : ℕ) : ℝ :=
  1 / weight L 1 + 1 / weight L (q - 1) + 1 / weight L q

/-- Uses every divisor through the actual legal synthesis; no closure assumption. -/
theorem rationalMinimum_coprime_three_site (L q : ℕ) (hq : 3 ≤ q)
    (hqL : q < L) (hcop : Nat.Coprime q L) :
    1 ≤ coprimeThreeSiteResistance L q * (rationalMinimum L - commonAverage L) := by
  have hL : 0 < L := by omega
  let s : Finset ℕ := {1, q - 1, q}
  let r : ℕ → ℝ := fun a => 1 - divisorFit L (rationalCoefficients L) a
  let v : ℕ → ℝ := fun a => (if a = q then -1 else 1) / weight L a
  have hne1 : (1 : ℕ) ≠ q - 1 := by omega
  have hne2 : (1 : ℕ) ≠ q := by omega
  have hne3 : q - 1 ≠ q := by omega
  have hsub : s ⊆ (sites L).erase L := by
    intro a ha
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;>
      apply Finset.mem_erase.mpr <;> constructor
    all_goals first | omega | exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hw (a : ℕ) (ha : a ∈ s) : weight L a ≠ 0 :=
    ne_of_gt (weight_pos_of_mem_sites L a (Finset.mem_erase.mp (hsub ha)).2)
  have hm : (∑ a ∈ s, weight L a * r a * v a) = 1 := by
    have he : (∑ a ∈ s, weight L a * r a * v a) =
        ∑ a ∈ s, (if a = q then -1 else 1) * r a := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [v]
      field_simp [hw a ha]
    rw [he]
    simp only [s, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      hne1, hne2, hne3, or_self, not_false_eq_true, Finset.sum_singleton]
    have hh := divisorFit_coprime_jump L q (by omega) hcop (rationalCoefficients L)
    dsimp [r]
    linarith
  have hv : (∑ a ∈ s, weight L a * v a ^ 2) = coprimeThreeSiteResistance L q := by
    have he : (∑ a ∈ s, weight L a * v a ^ 2) = ∑ a ∈ s, 1 / weight L a := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [v]
      split_ifs <;> field_simp [hw a ha]
    rw [he]
    simp [s, hne1, hne2, hne3, coprimeThreeSiteResistance, add_assoc]
  have hc := weighted_cauchy s (weight L) r v (fun a _ => weight_nonneg L a)
  rw [hm, hv, one_pow] at hc
  have he : (∑ a ∈ s, weight L a * r a ^ 2) ≤ rationalMinimum L - commonAverage L := by
    change (∑ a ∈ s, weight L a * r a ^ 2) ≤
      rationalError L (divisorFit L (rationalCoefficients L)) - commonAverage L
    rw [← residual_edge_energy L hL (divisorFit L (rationalCoefficients L))
      (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl))]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun a _ _ => mul_nonneg (weight_nonneg L a) (sq_nonneg (r a)))
  have hK : 0 ≤ coprimeThreeSiteResistance L q := by
    unfold coprimeThreeSiteResistance weight
    positivity
  nlinarith [mul_le_mul_of_nonneg_right he hK]

/-- A concrete finite criterion disproving an error-free absorption factor. -/
theorem signed_absorption_fails_of_coprime_site (L q : ℕ) (hq : 3 ≤ q)
    (hqL : q < L) (hcop : Nat.Coprime q L) (θ : ℝ) (hθ : θ < 1)
    (hsmall : (5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) -
        (1 - θ) * commonAverage L) * coprimeThreeSiteResistance L q < 1 - θ) :
    rationalSignedTail L < -θ * rationalMinimum L := by
  have hL : 0 < L := by omega
  have hl := rationalMinimum_coprime_three_site L q hq hqL hcop
  have hs := rationalMinimum_signedTail_exact L hL
  have hK : 0 ≤ coprimeThreeSiteResistance L q := by
    unfold coprimeThreeSiteResistance weight
    positivity
  by_contra hn
  have hb : (1 - θ) * rationalMinimum L ≤
      5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) := by linarith
  have hh := mul_le_mul_of_nonneg_right hb hK
  have hh' := mul_le_mul_of_nonneg_left hl (sub_pos.mpr hθ).le
  nlinarith


/-- The reciprocal edge resistance is at most the inverse-square denominator. -/
theorem inverse_weight_le_square (L a : ℕ) (ha : 0 < a) :
    1 / weight L a ≤ (a : ℝ) ^ 2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hw : 0 < weight L a := by unfold weight; positivity
  have hh : 1 / (a : ℝ) ^ 2 ≤ weight L a := by
    unfold weight
    have : 0 ≤ 2 / ((L : ℝ) * (2 * (a : ℝ) + L)) := by positivity
    linarith
  have h := (div_le_iff₀ (sq_pos_of_pos haR)).mp hh
  apply (div_le_iff₀ hw).mpr
  nlinarith

/-- A simple arithmetic lower bound, independent of the number of divisor atoms. -/
theorem rationalMinimum_coprime_polynomial_lower (L q : ℕ) (hq : 3 ≤ q)
    (hqL : q < L) (hcop : Nat.Coprime q L) :
    1 ≤ 2 * (q : ℝ) ^ 2 * (rationalMinimum L - commonAverage L) := by
  have hL : 0 < L := by omega
  have he : 0 ≤ rationalMinimum L - commonAverage L := by
    rw [← rationalMinimum_tail_dirichlet L hL]
    exact Finset.sum_nonneg (fun a _ =>
      div_nonneg (sq_nonneg _) (weight_nonneg L a))
  have hK : coprimeThreeSiteResistance L q ≤ 2 * (q : ℝ) ^ 2 := by
    have h1 := inverse_weight_le_square L 1 (by omega)
    have h2 := inverse_weight_le_square L (q - 1) (by omega)
    have h3 := inverse_weight_le_square L q (by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at h2
    norm_num only [Nat.cast_one, one_pow] at h1
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
    unfold coprimeThreeSiteResistance
    nlinarith
  exact (rationalMinimum_coprime_three_site L q hq hqL hcop).trans
    (mul_le_mul_of_nonneg_right hK he)

/-- The signed tail is already almost minus the whole minimum when q^2/L is small.
This is an upper bound on S, not the lower bound needed for absorption. -/
theorem rationalSignedTail_near_negative_minimum (L q : ℕ) (hq : 3 ≤ q)
    (hqL : q < L) (hcop : Nat.Coprime q L) :
    rationalSignedTail L ≤
      -(1 - 10 * (q : ℝ) ^ 2 / (3 * (L : ℝ))) * rationalMinimum L := by
  have hL : 0 < L := by omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hb : 0 ≤ commonAverage L := by unfold commonAverage; positivity
  have he := rationalMinimum_coprime_polynomial_lower L q hq hqL hcop
  have he' : 1 ≤ 2 * (q : ℝ) ^ 2 * rationalMinimum L := by
    nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) hb]
  have hphi : (Nat.totient L : ℝ) ≤ L := by exact_mod_cast Nat.totient_le L
  have hB : 5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) ≤ 5 / (3 * (L : ℝ)) := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * (L : ℝ) ^ 2)).mpr
    have hh : 5 / (3 * (L : ℝ)) * (3 * (L : ℝ) ^ 2) = 5 * (L : ℝ) := by
      field_simp
    rw [hh]
    linarith
  have hh : 5 / (3 * (L : ℝ)) ≤
      (10 * (q : ℝ) ^ 2 / (3 * (L : ℝ))) * rationalMinimum L := by
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 3 * (L : ℝ))).mpr
    nlinarith
  have hs := rationalMinimum_signedTail_exact L hL
  nlinarith [hB.trans hh]

/-- Exact finite obstruction at the seventh distinct primorial; no optimizer solve. -/
theorem seventh_primorial_signed_absorption_fails :
    rationalSignedTail 510510 < -(1999 / 2000 : ℝ) * rationalMinimum 510510 := by
  have ht : Nat.totient 510510 = 92160 := by
    rw [show 510510 = 17 * 30030 by norm_num,
      Nat.totient_mul (by decide : Nat.Coprime 17 30030),
      show 30030 = 13 * 2310 by norm_num,
      Nat.totient_mul (by decide : Nat.Coprime 13 2310),
      show 2310 = 11 * 210 by norm_num,
      Nat.totient_mul (by decide : Nat.Coprime 11 210),
      show 210 = 7 * 30 by norm_num,
      Nat.totient_mul (by decide : Nat.Coprime 7 30),
      show 30 = 5 * 6 by norm_num,
      Nat.totient_mul (by decide : Nat.Coprime 5 6),
      show 6 = 3 * 2 by norm_num,
      Nat.totient_mul (by decide : Nat.Coprime 3 2)]
    norm_num [Nat.totient_prime (by norm_num : Nat.Prime 17),
      Nat.totient_prime (by norm_num : Nat.Prime 13),
      Nat.totient_prime (by norm_num : Nat.Prime 11),
      Nat.totient_prime (by norm_num : Nat.Prime 7),
      Nat.totient_prime (by norm_num : Nat.Prime 5),
      Nat.totient_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 2)]
  apply signed_absorption_fails_of_coprime_site 510510 19 (by norm_num)
    (by norm_num) (by decide) (1999 / 2000) (by norm_num)
  norm_num [ht, commonAverage, coprimeThreeSiteResistance, weight]

end RiemannResearch.RH.QRationalCoprimeTail
