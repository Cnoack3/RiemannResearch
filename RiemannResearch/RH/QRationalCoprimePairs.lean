/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CoprimePairEnergy
import RiemannResearch.RH.QRationalCoprimeTail
import RiemannResearch.RH.QRationalGcdTail
import RiemannResearch.RH.QRationalCoprimeMinimum
import RiemannResearch.RH.QRationalCoprimeLower
import RiemannResearch.RH.QRationalTailPoincare
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalCoprimeLegality
import RiemannResearch.RH.QRationalSignedTailLimit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Simultaneous coprime-pair energy certificates

Source: direct finite square completion from the established coprime jump
identity, user-directed investigation, 21 October 2026. All residuals are
those of the actual complete-divisor rational minimizer. The result is a
lower bound and does not imply squarefree closure or RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.Analysis.CoprimePairEnergy

def coprimePairSites (Q : Finset ℕ) : Finset ℕ :=
  insert 1 (Q.image (fun q => q - 1) ∪ Q)

def coprimePairConductance (L : ℕ) (Q : Finset ℕ) : ℝ :=
  conductanceSum Q (fun q => weight L (q - 1)) (weight L)

def coprimePairsLower (L : ℕ) (Q : Finset ℕ) : ℝ :=
  effectiveEnergy (weight L 1) (coprimePairConductance L Q)

theorem coprimePairSites_subset (L : ℕ) (hL : 1 < L) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 3 ≤ q ∧ q < L) :
    coprimePairSites Q ⊆ (sites L).erase L := by
  intro a ha
  simp only [coprimePairSites, Finset.mem_insert, Finset.mem_union,
    Finset.mem_image] at ha
  rcases ha with rfl | ⟨q, hq, rfl⟩ | hq
  · exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  · have := hQ q hq
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  · have := hQ a hq
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem sum_coprimePairSites (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 3 ≤ q)
    (hd : Disjoint (Q.image (fun q => q - 1)) Q) (e : ℕ → ℝ) :
    (∑ a ∈ coprimePairSites Q, e a) =
      e 1 + ∑ q ∈ Q, (e (q - 1) + e q) := by
  have h1 : 1 ∉ Q.image (fun q => q - 1) ∪ Q := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨q, hq, he⟩ := Finset.mem_image.mp h
      have := hQ q hq
      omega
    · have := hQ 1 h
      omega
  have hi : (∑ a ∈ Q.image (fun q => q - 1), e a) = ∑ q ∈ Q, e (q - 1) := by
    apply Finset.sum_image
    intro a ha b hb hab
    dsimp only at hab
    have := hQ a ha
    have := hQ b hb
    omega
  rw [coprimePairSites, Finset.sum_insert h1, Finset.sum_union hd, hi,
    Finset.sum_add_distrib]



theorem coprimePairConductance_nonneg (L : ℕ) (Q : Finset ℕ) :
    0 ≤ coprimePairConductance L Q :=
  conductanceSum_nonneg Q _ _ (fun _ _ => weight_nonneg _ _)
    (fun _ _ => weight_nonneg _ _)

/-- Every omitted site and every pair-mean square remains explicit. -/
theorem rational_coprime_pairs_gap (L : ℕ) (hL : 1 < L) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 3 ≤ q ∧ q < L ∧ Nat.Coprime q L)
    (hd : Disjoint (Q.image (fun q => q - 1)) Q) :
    let r : ℕ → ℝ := fun a => 1 - divisorFit L (rationalCoefficients L) a
    let A := coprimePairConductance L Q
    rationalMinimum L - commonAverage L - coprimePairsLower L Q =
      (∑ a ∈ (sites L).erase L \ coprimePairSites Q, weight L a * r a ^ 2) +
      ((weight L 1 + A) * r 1 - A) ^ 2 / (weight L 1 + A) +
      ∑ q ∈ Q, (weight L (q - 1) * r (q - 1) + weight L q * r q) ^ 2 /
        (weight L (q - 1) + weight L q) := by
  dsimp only
  let r : ℕ → ℝ := fun a => 1 - divisorFit L (rationalCoefficients L) a
  have hsub := coprimePairSites_subset L hL Q (fun q hq =>
    ⟨(hQ q hq).1, (hQ q hq).2.1⟩)
  have hdecomp := Finset.sum_sdiff (f := fun a => weight L a * r a ^ 2) hsub
  rw [sum_coprimePairSites Q (fun q hq => (hQ q hq).1) hd] at hdecomp
  have he : (∑ a ∈ (sites L).erase L, weight L a * r a ^ 2) =
      rationalMinimum L - commonAverage L := by
    exact residual_edge_energy L (by omega) _
      (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl))
  rw [he] at hdecomp
  have hw1 : 0 < weight L 1 := by unfold weight; positivity
  have hA := coprimePairConductance_nonneg L Q
  have hwq (q : ℕ) (hq : q ∈ Q) : 0 < weight L (q - 1) + weight L q := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by have := hQ q hq; omega)
    have hpR : (0 : ℝ) < (q - 1 : ℕ) := by
      exact_mod_cast (show 0 < q - 1 by have := hQ q hq; omega)
    unfold weight
    positivity
  have hg := shared_pair_energy_gap Q (fun q => weight L (q - 1)) (weight L)
    (fun q => r (q - 1)) r (weight L 1) (r 1)
    (fun q hq => ne_of_gt (hwq q hq)) (fun q hq => by
      have hj := divisorFit_coprime_jump L q (by have := hQ q hq; omega)
        (hQ q hq).2.2 (rationalCoefficients L)
      dsimp [r]
      linarith) (by change weight L 1 + coprimePairConductance L Q ≠ 0; positivity)
  change weight L 1 * r 1 ^ 2 +
    (∑ q ∈ Q, (weight L (q - 1) * r (q - 1) ^ 2 + weight L q * r q ^ 2)) -
      coprimePairsLower L Q = _ at hg
  dsimp only [r, coprimePairConductance] at hg hdecomp ⊢
  linarith

/-- Simultaneous coprime relations give a lower certificate for the actual minimum. -/
theorem rationalMinimum_coprime_pairs_lower (L : ℕ) (hL : 1 < L) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 3 ≤ q ∧ q < L ∧ Nat.Coprime q L)
    (hd : Disjoint (Q.image (fun q => q - 1)) Q) :
    commonAverage L + coprimePairsLower L Q ≤ rationalMinimum L := by
  have hg := rational_coprime_pairs_gap L hL Q hQ hd
  dsimp only at hg
  have hu : 0 ≤ ∑ a ∈ (sites L).erase L \ coprimePairSites Q,
      weight L a * (1 - divisorFit L (rationalCoefficients L) a) ^ 2 := by
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (weight_nonneg L a) (sq_nonneg _))
  have hp : 0 ≤ ∑ q ∈ Q,
      (weight L (q - 1) * (1 - divisorFit L (rationalCoefficients L) (q - 1)) +
        weight L q * (1 - divisorFit L (rationalCoefficients L) q)) ^ 2 /
      (weight L (q - 1) + weight L q) := by
    exact Finset.sum_nonneg (fun q _ => div_nonneg (sq_nonneg _)
      (add_nonneg (weight_nonneg _ _) (weight_nonneg _ _)))
  have hc : 0 ≤
      ((weight L 1 + coprimePairConductance L Q) *
        (1 - divisorFit L (rationalCoefficients L) 1) - coprimePairConductance L Q) ^ 2 /
      (weight L 1 + coprimePairConductance L Q) :=
    div_nonneg (sq_nonneg _) (add_nonneg (weight_nonneg _ _) (coprimePairConductance_nonneg _ _))
  linarith

/-- Exact rational certificates need only show that the boundary is small
relative to the simultaneous-pair lower bound. -/
theorem signed_absorption_fails_of_coprime_pairs (L : ℕ) (hL : 1 < L) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 3 ≤ q ∧ q < L ∧ Nat.Coprime q L)
    (hd : Disjoint (Q.image (fun q => q - 1)) Q) (θ : ℝ) (hθ : θ < 1)
    (hsmall : 5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2) <
      (1 - θ) * (commonAverage L + coprimePairsLower L Q)) :
    rationalSignedTail L < -θ * rationalMinimum L := by
  have hl := rationalMinimum_coprime_pairs_lower L hL Q hQ hd
  have hs := rationalMinimum_signedTail_exact L (by omega)
  have hh := mul_le_mul_of_nonneg_left hl (sub_pos.mpr hθ).le
  linarith



theorem coprimePairsLower_nonneg (L : ℕ) (Q : Finset ℕ) :
    0 ≤ coprimePairsLower L Q := by
  unfold coprimePairsLower effectiveEnergy
  exact div_nonneg (mul_nonneg (weight_nonneg _ _) (coprimePairConductance_nonneg _ _))
    (add_nonneg (weight_nonneg _ _) (coprimePairConductance_nonneg _ _))

/-- A denominator-preserving quantitative bound on the normalized signed tail. -/
theorem rationalSignedTail_coprime_pairs_ratio_bound
    (L : ℕ) (hL : 1 < L) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, 3 ≤ q ∧ q < L ∧ Nat.Coprime q L)
    (hd : Disjoint (Q.image (fun q => q - 1)) Q) :
    0 ≤ rationalSignedTail L / rationalMinimum L + 1 ∧
    rationalSignedTail L / rationalMinimum L + 1 ≤
      (5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2)) /
        (commonAverage L + coprimePairsLower L Q) := by
  have hb : 0 < commonAverage L := by
    have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    unfold commonAverage
    positivity
  have hl := rationalMinimum_coprime_pairs_lower L hL Q hQ hd
  have hc := coprimePairsLower_nonneg L Q
  have hden : 0 < commonAverage L + coprimePairsLower L Q := by linarith
  have hR : 0 < rationalMinimum L := hden.trans_le hl
  have hs := rationalMinimum_signedTail_exact L (by omega)
  have he : rationalSignedTail L / rationalMinimum L + 1 =
      (5 * (Nat.totient L : ℝ) / (3 * (L : ℝ) ^ 2)) / rationalMinimum L := by
    apply (eq_div_iff (ne_of_gt hR)).mpr
    calc
      (rationalSignedTail L / rationalMinimum L + 1) * rationalMinimum L =
          rationalSignedTail L + rationalMinimum L := by field_simp
      _ = _ := by linarith
  rw [he]
  constructor
  · positivity
  · exact div_le_div_of_nonneg_left (by positivity) hden hl

/-- Twenty small coprime sites at the seventh distinct primorial. -/
def seventhPrimorialPairSites : Finset ℕ :=
  {19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
    61, 67, 71, 73, 79, 83, 89, 97, 101, 103}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
-- Exact normalization expands twenty rational weights and their common denominator.
/-- A stronger exact obstruction, without solving for any optimizer coefficient. -/
theorem seventh_primorial_twenty_pair_absorption_fails :
    rationalSignedTail 510510 < -(9999 / 10000 : ℝ) * rationalMinimum 510510 := by
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
  refine signed_absorption_fails_of_coprime_pairs 510510 (by norm_num)
    seventhPrimorialPairSites ?_ (by decide) (9999 / 10000) (by norm_num) ?_
  · intro q hq
    simp only [seventhPrimorialPairSites, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · norm_num [ht, commonAverage, coprimePairsLower, effectiveEnergy,
      coprimePairConductance, conductanceSum, pairConductance, seventhPrimorialPairSites, weight]

end RiemannResearch.RH.QRationalCoprimeTail
