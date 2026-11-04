/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.RH.QFourSiteReciprocalCertificate
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Arithmetic energy gap for the Q/Pareto squarefree displacement

Source: the user's two-residual measure-change handoff, resumed 28 October 2026,
and the checked four-site functional in QSquarefreeBoundary. The proof strategy
combines that arithmetic relation with an exact parameterized energy identity.

Both the limiting residual and the displacement satisfy the four-site relation.
The initial reciprocal bound 89/180 gives displacement coefficient 65520/7921.
The user's 28 October rational certificate improves these to 59/120 and
29280/3481; the further exact certificate 29/59 gives 7080/841. The complete
infinite tail and both energy remainders are retained. These Hilbert estimates
do not establish physical boundedness, polylogarithmic growth, or residual
vanishing. The finite matrix certificates are in QFourSiteReciprocalCertificate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeDisplacementEnergy
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QSquarefreeBoundary QSquarefreeDisplacementRigidity
open QSquarefreeResidualTail ZetaTwoOptimizerStage
/-- The first omitted squarefree coefficient excludes concentration at site one. -/
theorem B_inner_le_four_site_coordinates (f : QHilbert)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    inner ℝ f (B f) ≤ (89 / 180 : ℝ) * ‖f‖ ^ 2 := by
  have hs := qCoordinate_square_summable f
  have hhead := Summable.sum_le_tsum (Finset.range 4)
    (fun n _ => sq_nonneg (f n)) hs
  norm_num [Finset.sum_range_succ] at hhead
  rw [← qNorm_sq f] at hhead
  have hf0 : f 0 = 2 * f 1 + 3 * f 2 - 4 * f 3 := by linarith
  have hcs : (f 0) ^ 2 ≤ 29 * ((f 1) ^ 2 + (f 2) ^ 2 + (f 3) ^ 2) := by
    rw [hf0]
    nlinarith [sq_nonneg (3 * f 1 - 2 * f 2),
      sq_nonneg (4 * f 1 + 2 * f 3), sq_nonneg (4 * f 2 + 3 * f 3)]
  have h0 : 30 * (f 0) ^ 2 ≤ 29 * ‖f‖ ^ 2 := by nlinarith
  have hsB : Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
    intro n
    exact div_le_self (sq_nonneg _) (by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith)
  have hst : Summable (fun n : ℕ => (f (n + 1)) ^ 2) :=
    (summable_nat_add_iff 1).mpr hs
  have hsBt : Summable (fun n : ℕ => (f (n + 1)) ^ 2 / (((n + 1 : ℕ) : ℝ) + 2)) :=
    (summable_nat_add_iff 1).mpr hsB
  have ht : (∑' n : ℕ, (f (n + 1)) ^ 2 / (((n + 1 : ℕ) : ℝ) + 2)) ≤
      (1 / 3 : ℝ) * ∑' n : ℕ, (f (n + 1)) ^ 2 := by
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum _ hsBt (hst.mul_left (1 / 3 : ℝ))
    intro n
    calc
      _ ≤ (f (n + 1)) ^ 2 / 3 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
          (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
      _ = _ := by ring
  have hsplit := hs.tsum_eq_zero_add
  have hBsplit := hsB.tsum_eq_zero_add
  rw [← qNorm_sq f] at hsplit
  rw [← B_inner_tsum f] at hBsplit
  norm_num only [Nat.cast_zero, zero_add] at hBsplit
  nlinarith

/-- The physical four-site relation in the normalized real l2 coordinates. -/
theorem fourSite_coordinates {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0 := by
  have hs (n : ℕ) : qSequence f (n + 1) =
      Real.sqrt zetaTwo * ((n + 1 : ℕ) : ℝ) * f n := by
    rw [qSequence_succ]
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))).mpr
    have hw : (Real.sqrt (qWeight n) * Real.sqrt zetaTwo) *
        ((n + 1 : ℕ) : ℝ) = 1 := by
      rw [QDivisibilityDensity.sqrt_qWeight_mul_sqrt_zetaTwo]
      field_simp
    calc
      f n = f n * ((Real.sqrt (qWeight n) * Real.sqrt zetaTwo) *
        ((n + 1 : ℕ) : ℝ)) := by rw [hw, mul_one]
      _ = _ := by ring
  rw [fourSiteFunctional_apply, hs 3, hs 2, hs 1, hs 0] at hf
  norm_num at hf
  have he : Real.sqrt zetaTwo * (f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3) = 0 := by
    nlinarith [hf]
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (Real.sqrt_pos.mpr zetaTwo_pos))

theorem B_inner_le_four_site {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    inner ℝ f (B f) ≤ (89 / 180 : ℝ) * ‖f‖ ^ 2 :=
  B_inner_le_four_site_coordinates f (fourSite_coordinates hf)

theorem residual_fourSite : fourSiteFunctional limitingResidual = 0 := by
  change fourSiteFunctional (qOne - closure.starProjection qOne) = 0
  rw [map_sub, fourSiteFunctional_qOne,
    fourSiteFunctional_zero_on_closure (closure.starProjection_apply_mem qOne), sub_self]

theorem displacement_fourSite : fourSiteFunctional displacement = 0 :=
  fourSiteFunctional_zero_on_closure displacement_mem

theorem residual_displacement_orthogonal : inner ℝ displacement limitingResidual = 0 :=
  Submodule.inner_right_of_mem_orthogonal displacement_mem
    limitingResidual_mem_squarefree_orthogonal

theorem displacement_normal :
    inner ℝ displacement (B (limitingResidual + displacement)) = ‖displacement‖ ^ 2 := by
  have h := Submodule.inner_right_of_mem_orthogonal displacement_mem witness_mem_orthogonal
  rw [witness, inner_sub_right, real_inner_self_eq_norm_sq,
    pResidual_eq_residual_add_displacement] at h
  exact sub_eq_zero.mp h

/-- Exact arithmetic refinement, retaining both nonnegative remainder terms. -/
theorem arithmetic_displacement_energy_exact :
    ‖limitingResidual‖ ^ 2 = (65520 / 7921 : ℝ) * ‖displacement‖ ^ 2 +
      (180 / 89 : ℝ) * inner ℝ
        (limitingResidual - (182 / 89 : ℝ) • displacement)
        (B (limitingResidual - (182 / 89 : ℝ) • displacement)) +
      (‖limitingResidual + (360 / 89 : ℝ) • displacement‖ ^ 2 -
        (180 / 89 : ℝ) * inner ℝ
          (limitingResidual + (360 / 89 : ℝ) • displacement)
          (B (limitingResidual + (360 / 89 : ℝ) • displacement))) := by
  have h := displacement_energy_remainder_param limitingResidual displacement
    (360 / 89 : ℝ) residual_displacement_orthogonal displacement_normal
  norm_num at h
  simpa only [neg_smul, ← sub_eq_add_neg, map_add, map_sub, map_smul] using h

theorem arithmetic_displacement_energy_bound :
    (65520 / 7921 : ℝ) * ‖displacement‖ ^ 2 ≤ ‖limitingResidual‖ ^ 2 := by
  have hf : fourSiteFunctional
      (limitingResidual + (360 / 89 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site hf
  have hp := B_positive (limitingResidual - (182 / 89 : ℝ) • displacement)
  have he := arithmetic_displacement_energy_exact
  linarith


/-- The improved arithmetic gap is strictly positive on the nonzero-residual branch. -/
theorem arithmetic_displacement_energy_strict (hr : limitingResidual ≠ 0) :
    (65520 / 7921 : ℝ) * ‖displacement‖ ^ 2 < ‖limitingResidual‖ ^ 2 := by
  have hne : limitingResidual - (182 / 89 : ℝ) • displacement ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have ho := residual_displacement_orthogonal
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at ho
    have hd : displacement = 0 := norm_eq_zero.mp
      (by nlinarith [norm_nonneg displacement])
    exact hr (by simpa [hd] using he)
  have hp : 0 < inner ℝ
      (limitingResidual - (182 / 89 : ℝ) • displacement)
      (B (limitingResidual - (182 / 89 : ℝ) • displacement)) :=
    lt_of_le_of_ne (B_positive _) (Ne.symm (fun h => hne (B_faithful _ h)))
  have hf : fourSiteFunctional
      (limitingResidual + (360 / 89 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site hf
  have he := arithmetic_displacement_energy_exact
  linarith


/-! ## Exact rational certificates and the complete infinite tail -/

open QFourSiteReciprocalCertificate

private theorem reciprocal_square_summable (f : QHilbert) :
    Summable (fun n : ℕ => (f n) ^ 2 / ((n : ℝ) + 2)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (qCoordinate_square_summable f)
  intro n
  exact div_le_self (sq_nonneg _) (by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith)

/-- Exact head/tail decomposition, retaining every coordinate n ≥ 4.
The tail is a complete convergent series with every remainder retained. -/
theorem fourSite_gap_head_tail_exact (f : QHilbert) (lam : ℝ)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    lam * ‖f‖ ^ 2 - inner ℝ f (B f) =
      headGap lam (f 1) (f 2) (f 3) +
        ∑' n : ℕ, (lam - 1 / ((n : ℝ) + 6)) * (f (n + 4)) ^ 2 := by
  have hs := qCoordinate_square_summable f
  have hsB := reciprocal_square_summable f
  have hst : Summable (fun n : ℕ => (f (n + 4)) ^ 2) :=
    (summable_nat_add_iff 4).mpr hs
  have hsBt : Summable (fun n : ℕ => (f (n + 4)) ^ 2 / ((n : ℝ) + 6)) := by
    have ht := (summable_nat_add_iff 4).mpr hsB
    norm_num [Nat.cast_add, add_assoc] at ht
    exact ht
  have hsplit := hs.sum_add_tsum_nat_add 4
  have hBsplit := hsB.sum_add_tsum_nat_add 4
  rw [← qNorm_sq f] at hsplit
  rw [← B_inner_tsum f] at hBsplit
  norm_num [Finset.sum_range_succ, add_assoc] at hsplit hBsplit
  have htail :
      (∑' n : ℕ, (lam - 1 / ((n : ℝ) + 6)) * (f (n + 4)) ^ 2) =
        lam * (∑' n : ℕ, (f (n + 4)) ^ 2) -
          ∑' n : ℕ, (f (n + 4)) ^ 2 / ((n : ℝ) + 6) := by
    calc
      _ = ∑' n : ℕ, (lam * (f (n + 4)) ^ 2 -
          (f (n + 4)) ^ 2 / ((n : ℝ) + 6)) :=
        tsum_congr (fun n => by ring)
      _ = _ := by rw [(hst.mul_left lam).tsum_sub hsBt, tsum_mul_left]
  have hf0 : f 0 = 2 * f 1 + 3 * f 2 - 4 * f 3 := by linarith
  rw [htail, ← hsplit, ← hBsplit, hf0]
  unfold headGap
  ring

/-- The complete tail contributes nonnegatively as soon as lam ≥ 1/6. -/
theorem fourSite_tail_nonneg (f : QHilbert) (lam : ℝ) (hlam : (1 / 6 : ℝ) ≤ lam) :
    0 ≤ ∑' n : ℕ, (lam - 1 / ((n : ℝ) + 6)) * (f (n + 4)) ^ 2 := by
  apply tsum_nonneg
  intro n
  apply mul_nonneg _ (sq_nonneg _)
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hi : 1 / ((n : ℝ) + 6) ≤ (1 / 6 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

theorem B_inner_le_four_site_of_headGap (f : QHilbert) (lam : ℝ)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0)
    (hlam : (1 / 6 : ℝ) ≤ lam)
    (hhead : 0 ≤ headGap lam (f 1) (f 2) (f 3)) :
    inner ℝ f (B f) ≤ lam * ‖f‖ ^ 2 := by
  have he := fourSite_gap_head_tail_exact f lam hfour
  have ht := fourSite_tail_nonneg f lam hlam
  linarith

theorem B_inner_le_four_site_coordinates_59_120 (f : QHilbert)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    inner ℝ f (B f) ≤ (59 / 120 : ℝ) * ‖f‖ ^ 2 := by
  apply B_inner_le_four_site_of_headGap f _ hfour (by norm_num)
  rw [headGap_sos_59_120]
  positivity

theorem B_inner_le_four_site_coordinates_29_59 (f : QHilbert)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    inner ℝ f (B f) ≤ (29 / 59 : ℝ) * ‖f‖ ^ 2 := by
  apply B_inner_le_four_site_of_headGap f _ hfour (by norm_num)
  rw [headGap_sos_29_59]
  positivity

theorem B_inner_le_four_site_59_120 {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    inner ℝ f (B f) ≤ (59 / 120 : ℝ) * ‖f‖ ^ 2 :=
  B_inner_le_four_site_coordinates_59_120 f (fourSite_coordinates hf)

theorem B_inner_le_four_site_29_59 {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    inner ℝ f (B f) ≤ (29 / 59 : ℝ) * ‖f‖ ^ 2 :=
  B_inner_le_four_site_coordinates_29_59 f (fourSite_coordinates hf)

/-- Exact limiting-vector energy identity at spectral bound 59/120,
retaining both nonnegative remainders. -/
theorem arithmetic_displacement_energy_exact_59_120 :
    ‖limitingResidual‖ ^ 2 = (29280 / 3481 : ℝ) * ‖displacement‖ ^ 2 +
      (120 / 59 : ℝ) * inner ℝ
        (limitingResidual - (122 / 59 : ℝ) • displacement)
        (B (limitingResidual - (122 / 59 : ℝ) • displacement)) +
      (‖limitingResidual + (240 / 59 : ℝ) • displacement‖ ^ 2 -
        (120 / 59 : ℝ) * inner ℝ
          (limitingResidual + (240 / 59 : ℝ) • displacement)
          (B (limitingResidual + (240 / 59 : ℝ) • displacement))) := by
  have h := displacement_energy_remainder_param limitingResidual displacement
    (240 / 59 : ℝ) residual_displacement_orthogonal displacement_normal
  norm_num at h
  simpa only [neg_smul, ← sub_eq_add_neg, map_add, map_sub, map_smul] using h

theorem arithmetic_displacement_energy_bound_59_120 :
    (29280 / 3481 : ℝ) * ‖displacement‖ ^ 2 ≤ ‖limitingResidual‖ ^ 2 := by
  have hf : fourSiteFunctional
      (limitingResidual + (240 / 59 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site_59_120 hf
  have hp := B_positive (limitingResidual - (122 / 59 : ℝ) • displacement)
  have he := arithmetic_displacement_energy_exact_59_120
  linarith

/-- The improved arithmetic gap is strictly positive on the nonzero-residual branch. -/
theorem arithmetic_displacement_energy_strict_59_120 (hr : limitingResidual ≠ 0) :
    (29280 / 3481 : ℝ) * ‖displacement‖ ^ 2 < ‖limitingResidual‖ ^ 2 := by
  have hne : limitingResidual - (122 / 59 : ℝ) • displacement ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have ho := residual_displacement_orthogonal
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at ho
    have hd : displacement = 0 := norm_eq_zero.mp
      (by nlinarith [norm_nonneg displacement])
    exact hr (by simpa [hd] using he)
  have hp : 0 < inner ℝ
      (limitingResidual - (122 / 59 : ℝ) • displacement)
      (B (limitingResidual - (122 / 59 : ℝ) • displacement)) :=
    lt_of_le_of_ne (B_positive _) (Ne.symm (fun h => hne (B_faithful _ h)))
  have hf : fourSiteFunctional
      (limitingResidual + (240 / 59 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site_59_120 hf
  have he := arithmetic_displacement_energy_exact_59_120
  linarith


/-- Exact limiting-vector energy identity at spectral bound 29/59,
retaining both nonnegative remainders. -/
theorem arithmetic_displacement_energy_exact_29_59 :
    ‖limitingResidual‖ ^ 2 = (7080 / 841 : ℝ) * ‖displacement‖ ^ 2 +
      (59 / 29 : ℝ) * inner ℝ
        (limitingResidual - (60 / 29 : ℝ) • displacement)
        (B (limitingResidual - (60 / 29 : ℝ) • displacement)) +
      (‖limitingResidual + (118 / 29 : ℝ) • displacement‖ ^ 2 -
        (59 / 29 : ℝ) * inner ℝ
          (limitingResidual + (118 / 29 : ℝ) • displacement)
          (B (limitingResidual + (118 / 29 : ℝ) • displacement))) := by
  have h := displacement_energy_remainder_param limitingResidual displacement
    (118 / 29 : ℝ) residual_displacement_orthogonal displacement_normal
  norm_num at h
  simpa only [neg_smul, ← sub_eq_add_neg, map_add, map_sub, map_smul] using h

theorem arithmetic_displacement_energy_bound_29_59 :
    (7080 / 841 : ℝ) * ‖displacement‖ ^ 2 ≤ ‖limitingResidual‖ ^ 2 := by
  have hf : fourSiteFunctional
      (limitingResidual + (118 / 29 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site_29_59 hf
  have hp := B_positive (limitingResidual - (60 / 29 : ℝ) • displacement)
  have he := arithmetic_displacement_energy_exact_29_59
  linarith

/-- The improved arithmetic gap is strictly positive on the nonzero-residual branch. -/
theorem arithmetic_displacement_energy_strict_29_59 (hr : limitingResidual ≠ 0) :
    (7080 / 841 : ℝ) * ‖displacement‖ ^ 2 < ‖limitingResidual‖ ^ 2 := by
  have hne : limitingResidual - (60 / 29 : ℝ) • displacement ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have ho := residual_displacement_orthogonal
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at ho
    have hd : displacement = 0 := norm_eq_zero.mp
      (by nlinarith [norm_nonneg displacement])
    exact hr (by simpa [hd] using he)
  have hp : 0 < inner ℝ
      (limitingResidual - (60 / 29 : ℝ) • displacement)
      (B (limitingResidual - (60 / 29 : ℝ) • displacement)) :=
    lt_of_le_of_ne (B_positive _) (Ne.symm (fun h => hne (B_faithful _ h)))
  have hf : fourSiteFunctional
      (limitingResidual + (118 / 29 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site_29_59 hf
  have he := arithmetic_displacement_energy_exact_29_59
  linarith


theorem B_inner_le_four_site_coordinates_983_2000 (f : QHilbert)
    (hfour : f 0 - 2 * f 1 - 3 * f 2 + 4 * f 3 = 0) :
    inner ℝ f (B f) ≤ (983 / 2000 : ℝ) * ‖f‖ ^ 2 := by
  apply B_inner_le_four_site_of_headGap f _ hfour (by norm_num)
  rw [headGap_sos_983_2000]
  positivity
theorem B_inner_le_four_site_983_2000 {f : QHilbert} (hf : fourSiteFunctional f = 0) :
    inner ℝ f (B f) ≤ (983 / 2000 : ℝ) * ‖f‖ ^ 2 :=
  B_inner_le_four_site_coordinates_983_2000 f (fourSite_coordinates hf)


/-- Improved exact identity; both full-Q energy remainders are retained. -/
theorem arithmetic_displacement_energy_exact_983_2000 :
    ‖limitingResidual‖ ^ 2 = (8136000 / 966289 : ℝ) * ‖displacement‖ ^ 2 +
      (2000 / 983 : ℝ) * inner ℝ
        (limitingResidual - (2034 / 983 : ℝ) • displacement)
        (B (limitingResidual - (2034 / 983 : ℝ) • displacement)) +
      (‖limitingResidual + (4000 / 983 : ℝ) • displacement‖ ^ 2 -
        (2000 / 983 : ℝ) * inner ℝ
          (limitingResidual + (4000 / 983 : ℝ) • displacement)
          (B (limitingResidual + (4000 / 983 : ℝ) • displacement))) := by
  have h := displacement_energy_remainder_param limitingResidual displacement
    (4000 / 983 : ℝ) residual_displacement_orthogonal displacement_normal
  norm_num at h
  simpa only [neg_smul, ← sub_eq_add_neg, map_add, map_sub, map_smul] using h

theorem arithmetic_displacement_energy_bound_983_2000 :
    (8136000 / 966289 : ℝ) * ‖displacement‖ ^ 2 ≤ ‖limitingResidual‖ ^ 2 := by
  have hf : fourSiteFunctional
      (limitingResidual + (4000 / 983 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site_983_2000 hf
  have hp := B_positive (limitingResidual - (2034 / 983 : ℝ) • displacement)
  have he := arithmetic_displacement_energy_exact_983_2000
  linarith

theorem arithmetic_displacement_energy_strict_983_2000 (hr : limitingResidual ≠ 0) :
    (8136000 / 966289 : ℝ) * ‖displacement‖ ^ 2 < ‖limitingResidual‖ ^ 2 := by
  have hne : limitingResidual - (2034 / 983 : ℝ) • displacement ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have ho := residual_displacement_orthogonal
    rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at ho
    have hd : displacement = 0 := norm_eq_zero.mp
      (by nlinarith [norm_nonneg displacement])
    exact hr (by simpa [hd] using he)
  have hp : 0 < inner ℝ
      (limitingResidual - (2034 / 983 : ℝ) • displacement)
      (B (limitingResidual - (2034 / 983 : ℝ) • displacement)) :=
    lt_of_le_of_ne (B_positive _) (Ne.symm (fun h => hne (B_faithful _ h)))
  have hf : fourSiteFunctional
      (limitingResidual + (4000 / 983 : ℝ) • displacement) = 0 := by
    simp only [map_add, map_smul, residual_fourSite, displacement_fourSite,
      smul_zero, add_zero]
  have hu := B_inner_le_four_site_983_2000 hf
  have he := arithmetic_displacement_energy_exact_983_2000
  linarith

end RiemannResearch.RH.QSquarefreeDisplacementEnergy
