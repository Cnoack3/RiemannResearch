/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QGcdSampling
import RiemannResearch.NumberTheory.GcdSampleTail
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QResidueConditional
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Quantitative gcd-cell conditioning

Source: the elementary weighted conditional-expectation argument in
`CRTCollocationStabilityResearch20261107.md`, developed from the user's CRT handoff.
All masses and pairings are in the complete inverse-square Q law.
The generic bound below is useful for the instability of the inverse on the
whole trial space. It does not imply growth of the particular canonical lift.
The exact finite Möbius formula also computes the complete sampled tail for
every real exponent from the existing inverse-square gcd-cell masses.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QGcdCellEstimates
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QDivisibilityDensity QCRTFiniteCollocation QGcdSampling
open RiemannResearch.NumberTheory.DivisorEscapeTail

/-- Every gcd cell contains its smallest positive member d. -/
theorem gcdCell_mass_lower (L d : ℕ) (hL : 0 < L) (hd : d ∣ L) :
    1 / (zetaTwo * (d : ℝ)^2) ≤ ‖gcdCell L d‖^2 := by
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd hL
  rw [qNorm_weighted_sq]
  have h := (qSequence_square_summable (gcdCell L d)).le_tsum d
    (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
  simpa only [qSequence_gcdCell L hL d hd d hdp, Nat.gcd_eq_left hd,
    if_pos rfl, ite_true, one_pow, mul_one, positiveQWeight] using h

theorem gcdCell_mass_pos (L d : ℕ) (hL : 0 < L) (hd : d ∣ L) :
    0 < ‖gcdCell L d‖^2 := by
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd hL
  have hdpR : (0 : ℝ) < d := by exact_mod_cast hdp
  exact lt_of_lt_of_le (by have hz := zetaTwo_pos; positivity)
    (gcdCell_mass_lower L d hL hd)

/-- A gcd cell is contained in its divisibility event. -/
theorem gcdCell_mass_upper (L d : ℕ) (hL : 0 < L) (hd : d ∣ L) :
    ‖gcdCell L d‖^2 ≤ 1 / (d : ℝ)^2 := by
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd hL
  rw [← qDivisor_norm_sq d hdp, qNorm_weighted_sq, qNorm_weighted_sq]
  apply (qSequence_square_summable (gcdCell L d)).tsum_le_tsum _
    (qSequence_square_summable (qDivisor d))
  intro n
  by_cases hn : n = 0
  · subst n; simp
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  rw [qSequence_gcdCell L hL d hd n hnp, qSequence_qDivisor]
  by_cases hg : Nat.gcd n L = d
  · have hdn : d ∣ n := by rw [← hg]; exact Nat.gcd_dvd_left n L
    simp [hg, positiveDivisor, hn, hdn]
  · simp only [if_neg hg, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)

/-- Exact conditional value times its cell mass equals the original cell moment. -/
theorem conditional_cell_pairing (L d : ℕ) (hL : 0 < L) (hd : d ∣ L)
    (f : QHilbert) :
    qSequence (conditionalProjection L f) d * ‖gcdCell L d‖^2 =
      inner ℝ f (gcdCell L d) := by
  rw [← conditional_inner L f (gcdCell L d) (gcdCell_mem_cell L hL d),
    qNorm_weighted_sq, qInner_weighted, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  rw [qSequence_gcdCell L hL d hd n hnp]
  by_cases hg : Nat.gcd n L = d
  · have he := conditional_gcd_coordinates L hL f n hnp
    rw [hg] at he
    simp only [if_pos hg, one_pow, mul_one]
    rw [he]
    ring
  · simp [hg]

/-- The conditional vector is exactly its finite gcd-cell expansion. -/
theorem conditional_eq_sample (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    conditionalProjection L f =
      sample L (qSequence (conditionalProjection L f)) := by
  apply qSequence_injective
  funext n
  by_cases hn : n = 0
  · subst n; simp
  rw [qSequence_sample L hL _ n (Nat.pos_of_ne_zero hn)]
  exact (conditional_gcd_coordinates L hL f n (Nat.pos_of_ne_zero hn)).symm

/-- Parseval for the disjoint gcd cells, expressed through original cell moments. -/
theorem conditional_norm_sq_eq_sum (L : ℕ) (hL : 0 < L) (f : QHilbert) :
    ‖conditionalProjection L f‖^2 =
      ∑ d ∈ L.divisors, qSequence (conditionalProjection L f) d *
        inner ℝ f (gcdCell L d) := by
  calc
    _ = inner ℝ (conditionalProjection L f) (conditionalProjection L f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ (conditionalProjection L f)
        (sample L (qSequence (conditionalProjection L f))) := by
      rw [← conditional_eq_sample L hL f]
    _ = _ := by
      simp only [sample, inner_sum, inner_smul_right]
      apply Finset.sum_congr rfl
      intro d hd
      rw [conditional_inner L f _ (gcdCell_mem_cell L hL d)]

/-- A complete-Q projected norm estimate requiring no positivity of f.
Only the single atom d in each gcd cell is used for its denominator. -/
theorem conditional_norm_sq_le_cell_moments (L : ℕ) (hL : 0 < L)
    (f : QHilbert) :
    ‖conditionalProjection L f‖^2 ≤
      ∑ d ∈ L.divisors,
        (zetaTwo * (d : ℝ)^2) * (inner ℝ f (gcdCell L d))^2 := by
  rw [conditional_norm_sq_eq_sum L hL f]
  apply Finset.sum_le_sum
  intro d hdmem
  have hd := Nat.dvd_of_mem_divisors hdmem
  have hdp := Nat.pos_of_mem_divisors hdmem
  have hdpR : (0 : ℝ) < d := by exact_mod_cast hdp
  have hz := zetaTwo_pos
  have hm := gcdCell_mass_lower L d hL hd
  have hm' : 1 ≤ (zetaTwo * (d : ℝ)^2) * ‖gcdCell L d‖^2 := by
    have he := (div_le_iff₀ (by positivity : 0 < zetaTwo * (d : ℝ)^2)).mp hm
    nlinarith
  have hp := conditional_cell_pairing L d hL hd f
  have hnon : 0 ≤ (qSequence (conditionalProjection L f) d)^2 *
      ‖gcdCell L d‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ = (qSequence (conditionalProjection L f) d)^2 * ‖gcdCell L d‖^2 := by
      rw [← hp]
      ring
    _ ≤ ((qSequence (conditionalProjection L f) d)^2 * ‖gcdCell L d‖^2) *
        ((zetaTwo * (d : ℝ)^2) * ‖gcdCell L d‖^2) := by
      nlinarith [mul_nonneg hnon (sub_nonneg.mpr hm')]
    _ = _ := by rw [← hp]; ring

/-- Positive physical f has positive gcd-cell moments. -/
theorem cell_moment_nonneg (L d : ℕ) (hL : 0 < L) (hd : d ∣ L)
    (f : QHilbert) (hf : ∀ n, 0 ≤ qSequence f n) :
    0 ≤ inner ℝ f (gcdCell L d) := by
  rw [qInner_weighted]
  apply tsum_nonneg
  intro n
  by_cases hn : n = 0
  · subst n; simp
  rw [qSequence_gcdCell L hL d hd n (Nat.pos_of_ne_zero hn)]
  have hpos := positiveQWeight_nonneg n
  have hfn := hf n
  split_ifs <;> positivity

/-- For a positive f, its gcd-cell moment is at most its divisibility moment. -/
theorem cell_moment_le_divisor (L d : ℕ) (hL : 0 < L) (hd : d ∣ L)
    (f : QHilbert) (hf : ∀ n, 0 ≤ qSequence f n) :
    inner ℝ f (gcdCell L d) ≤ inner ℝ f (qDivisor d) := by
  rw [qInner_weighted, qInner_weighted]
  apply (qSequence_product_summable f (gcdCell L d)).tsum_le_tsum _
    (qSequence_product_summable f (qDivisor d))
  intro n
  by_cases hn : n = 0
  · subst n; simp
  rw [qSequence_gcdCell L hL d hd n (Nat.pos_of_ne_zero hn), qSequence_qDivisor]
  by_cases hg : Nat.gcd n L = d
  · have hdn : d ∣ n := by rw [← hg]; exact Nat.gcd_dvd_left n L
    simp [hg, positiveDivisor, hn, hdn]
  · simp only [if_neg hg, mul_zero]
    have hpos : 0 ≤ positiveDivisor d n := by
      unfold positiveDivisor
      split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) (hf n)) hpos

/-- The residue at conductor d*b, restricted to multiples of d, is the b residue. -/
theorem residue_divisor_moment (d b : ℕ) (hd : 0 < d) :
    inner ℝ (qResidue (d*b)) (qDivisor d) =
      (1 / (d : ℝ)^2) * inner ℝ qOne (qResidue b) := by
  rw [inner_qDivisor_eq_dilation _ d hd, qInner_eq_inversePowerMean]
  congr 1
  unfold inversePowerMean
  apply tsum_congr
  intro n
  simp only [qSequence_qResidue, qSequence_qOne, qOneSequence,
    Nat.succ_ne_zero, if_false, one_mul]
  rw [QResidueConditional.residueFraction_scale d b (n+1) hd]

/-- Concrete complete-Q estimate on the most ill-conditioned conductor direction.
The denominator ζ(2) is retained by estimating squared moments over cell mass. -/
theorem conditional_residue_norm_sq_le (L : ℕ) (hL : 2 ≤ L) :
    ‖conditionalProjection L (qResidue L)‖^2 ≤
      (L.divisors.card : ℝ) * (2 + Real.log (L : ℝ))^2 /
        (zetaTwo * (L : ℝ)^2) := by
  have hLp : 0 < L := by omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLp
  have hz := zetaTwo_pos
  have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
  calc
    _ ≤ ∑ d ∈ L.divisors,
        (zetaTwo * (d : ℝ)^2) * (inner ℝ (qResidue L) (gcdCell L d))^2 :=
      conditional_norm_sq_le_cell_moments L hLp _
    _ ≤ ∑ _d ∈ L.divisors,
        (2 + Real.log (L : ℝ))^2 / (zetaTwo * (L : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdL := Nat.dvd_of_mem_divisors hdmem
      have hdp := Nat.pos_of_mem_divisors hdmem
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdp
      let b := L / d
      have hb : 0 < b := Nat.div_pos (Nat.le_of_dvd hLp hdL) hdp
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have he : d * b = L := Nat.mul_div_cancel' hdL
      have heR : (d : ℝ) * b = L := by exact_mod_cast he
      have hI0 := cell_moment_nonneg L d hLp hdL (qResidue L)
        (qResidue_physical_nonneg L)
      have hI := cell_moment_le_divisor L d hLp hdL (qResidue L)
        (qResidue_physical_nonneg L)
      have hdil : inner ℝ (qResidue L) (qDivisor d) =
          (1 / (d : ℝ)^2) * inner ℝ qOne (qResidue b) := by
        simpa only [he] using residue_divisor_moment d b hdp
      rw [hdil] at hI
      by_cases hb1 : b = 1
      · simp only [hb1, qResidue_one, inner_zero_right, mul_zero] at hI
        have hIz : inner ℝ (qResidue L) (gcdCell L d) = 0 := le_antisymm hI hI0
        rw [hIz]
        simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero]
        positivity
      have hb2 : 2 ≤ b := by omega
      have hm := qResidue_mean_le_log_div b hb2
      have hbL : b ≤ L := Nat.div_le_self L d
      have hbLR : (b : ℝ) ≤ L := by exact_mod_cast hbL
      have hlog : Real.log (b : ℝ) ≤ Real.log (L : ℝ) := Real.log_le_log hbR hbLR
      have hIupper : inner ℝ (qResidue L) (gcdCell L d) ≤
          (2 + Real.log (L : ℝ)) / (zetaTwo * (d : ℝ) * L) := by
        calc
          _ ≤ (1 / (d : ℝ)^2) * inner ℝ qOne (qResidue b) := hI
          _ ≤ (1 / (d : ℝ)^2) * ((2 + Real.log (b : ℝ)) / (zetaTwo*b)) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
          _ ≤ (1 / (d : ℝ)^2) * ((2 + Real.log (L : ℝ)) / (zetaTwo*b)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by rw [← heR]; field_simp
      have hsq := (sq_le_sq₀ hI0 (by positivity)).mpr hIupper
      calc
        _ ≤ (zetaTwo * (d : ℝ)^2) *
            ((2 + Real.log (L : ℝ)) / (zetaTwo * (d : ℝ) * L))^2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = _ := by field_simp
    _ = _ := by simp [mul_div_assoc]

/-- Any squared stability factor on the full trial space has this unavoidable
scalar lower bound. This does not bound the canonical target-specific lift. -/
theorem trial_stability_factor_necessary (L : ℕ) (hL : 2 ≤ L) (C : ℝ)
    (hC : 0 ≤ C)
    (hstability : ∀ f : trialSpace L,
      ‖(f : QHilbert)‖^2 ≤ C * ‖conditionalProjection L f‖^2) :
    (L : ℝ) - 1 ≤ C * (L.divisors.card : ℝ) * (2 + Real.log (L : ℝ))^2 := by
  have hLp : 0 < L := by omega
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLp
  have hz := zetaTwo_pos
  have h := (qResidue_norm_sq_ge_head L hLp).trans
    ((hstability ⟨qResidue L, residue_mem_trial L L hLp (dvd_refl L)⟩).trans
      (mul_le_mul_of_nonneg_left (conditional_residue_norm_sq_le L hL) hC))
  have he : C * ((L.divisors.card : ℝ) * (2 + Real.log (L : ℝ))^2 /
      (zetaTwo * (L : ℝ)^2)) =
      (C * (L.divisors.card : ℝ) * (2 + Real.log (L : ℝ))^2) /
        (zetaTwo * (L : ℝ)^2) := by ring
  rw [he] at h
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < zetaTwo * (L : ℝ)^2)).mp h

/-- The exact mass of a gcd cell, computed by the finite incidence inverse. -/
theorem gcdCell_moment_eq_finite_moebius (L d : ℕ) :
    inner ℝ qOne (gcdCell L d) =
      ∑ j ∈ L.divisors,
        (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) /
          (j : ℝ) ^ 2 := by
  simp only [gcdCell, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [qOne_inner_qDivisor j (Nat.pos_of_mem_divisors hj)]
  ring

/-- Every finite gcd-sampled moment is an explicit divisor sum. -/
theorem sample_moment_eq_finite_moebius (L : ℕ) (b : ℕ → ℝ) :
    inner ℝ qOne (sample L b) =
      ∑ d ∈ L.divisors, b d *
        ∑ j ∈ L.divisors,
          (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) /
            (j : ℝ) ^ 2 := by
  simp only [sample, inner_sum, inner_smul_right, gcdCell_moment_eq_finite_moebius]

/-- Actual convergence of an arbitrary gcd-sampled inverse-square series.
No growth assumption on b is necessary because its sampled range is finite. -/
theorem gcd_sample_inverse_square_hasSum (L : ℕ) (hL : 0 < L) (b : ℕ → ℝ) :
    HasSum (fun n : ℕ => b (Nat.gcd n L) / (n : ℝ) ^ 2)
      (zetaTwo * inner ℝ qOne (sample L b)) := by
  have hp : HasSum (fun n : ℕ => positiveQWeight n * qSequence qOne n *
      qSequence (sample L b) n) (inner ℝ qOne (sample L b)) := by
    rw [qInner_weighted]
    exact (qSequence_product_summable qOne (sample L b)).hasSum
  apply (hp.mul_left zetaTwo).congr_fun
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero,
      qSequence_zero, mul_zero]
  · have hnp : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
    rw [qSequence_sample L hL b n hnp, qSequence_qOne]
    simp only [qOneSequence, if_neg hn, mul_one]
    unfold positiveQWeight
    field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hnR]

/-- The full gcd-sample tail is computable by two finite divisor sums.
This formula retains every escaping coordinate and holds for all real t. -/
theorem sampleTail_eq_finite_moebius (t : ℝ) (L : ℕ) (hL : 0 < L) :
    sampleTail t L = zetaTwo *
      (∑ d ∈ L.divisors, (d : ℝ) ^ (2 - t) *
        ∑ j ∈ L.divisors,
          (if d ∣ j then (ArithmeticFunction.moebius (j / d) : ℝ) else 0) /
            (j : ℝ) ^ 2) -
      ∑ d ∈ L.divisors, (d : ℝ) ^ (-t) := by
  classical
  let total : ℕ → ℝ := fun n => (Nat.gcd n L : ℝ) ^ (2 - t) / (n : ℝ) ^ 2
  let saved : ℕ → ℝ := fun n => if n ∈ L.divisors then (n : ℝ) ^ (-t) else 0
  have htotal := gcd_sample_inverse_square_hasSum L hL (fun d => (d : ℝ) ^ (2 - t))
  rw [sample_moment_eq_finite_moebius] at htotal
  have hs : Summable saved := by
    apply summable_of_ne_finset_zero (s := L.divisors)
    intro n hn
    simp only [saved, if_neg hn]
  have hfin : (∑' n : ℕ, saved n) = ∑ d ∈ L.divisors, (d : ℝ) ^ (-t) := by
    rw [tsum_eq_sum (s := L.divisors) (by intro n hn; simp only [saved, if_neg hn])]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [saved, if_pos hn]
  have hsplit (n : ℕ) : sampleTerm t L n = total n - saved n := by
    by_cases hn : n ∣ L
    · have hmem : n ∈ L.divisors := Nat.mem_divisors.mpr ⟨hn, ne_of_gt hL⟩
      have hnp : 0 < n := Nat.pos_of_mem_divisors hmem
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
      have hp : (n : ℝ) ^ (2 - t) / (n : ℝ) ^ 2 = (n : ℝ) ^ (-t) := by
        apply (div_eq_iff (pow_ne_zero 2 (ne_of_gt hnR))).mpr
        rw [← Real.rpow_two, ← Real.rpow_add hnR]
        congr 1
        ring
      simp only [sampleTerm, if_pos hn, total, Nat.gcd_eq_left hn,
        saved, if_pos hmem, hp, sub_self]
    · have hmem : n ∉ L.divisors := fun h => hn (Nat.dvd_of_mem_divisors h)
      simp only [sampleTerm, if_neg hn, total, saved, if_neg hmem, sub_zero]
  have hsub := htotal.sub hs.hasSum
  rw [hfin] at hsub
  have hactual := hsub.congr_fun hsplit
  have hz : sampleTerm t L 0 = 0 := by simp [sampleTerm]
  have hshift := hactual.summable.tsum_eq_zero_add
  rw [hz, zero_add] at hshift
  change (∑' n : ℕ, sampleTerm t L (n + 1)) = _
  rw [← hshift]
  exact hactual.tsum_eq

end RiemannResearch.RH.QGcdCellEstimates
