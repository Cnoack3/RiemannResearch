/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCofinalDisplacementMoments
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QSixAtomTrialBound
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Harmonic prefixes of finite resolvent iterates

Source: the November 5 displacement research agenda, section 3.
The subspace is the squarefree physical dictionary discussed in B. Bagchi,
*On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation of the
Riemann hypothesis* (2006), Remark 8, arXiv:math/0607733. The prefix
estimates below use the project's Q norm and matched projection displacement.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeDisplacementResolvent

/-- Harmonic mass of one sign on a physical head. -/
def harmonicSideOf (u : QHilbert) (ε : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), max (ε * qSequence u n) 0 / (n : ℝ)

/-- The smaller of the two signed masses of an arbitrary Q-vector. -/
def minimumHarmonicPrefixOf (u : QHilbert) (X : ℕ) : ℝ :=
  min (harmonicSideOf u 1 X) (harmonicSideOf u (-1) X)

/-- The exact unsigned mass less the magnitude of the signed mass. -/
theorem twice_minimumHarmonicPrefixOf (u : QHilbert) (X : ℕ) :
    2 * minimumHarmonicPrefixOf u X =
      (∑ n ∈ Finset.range (X + 1), |qSequence u n| / (n : ℝ)) -
      |∑ n ∈ Finset.range (X + 1), qSequence u n / (n : ℝ)| := by
  have hsum : harmonicSideOf u 1 X + harmonicSideOf u (-1) X =
      ∑ n ∈ Finset.range (X + 1), |qSequence u n| / (n : ℝ) := by
    rw [harmonicSideOf, harmonicSideOf, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [one_mul, neg_one_mul, ← add_div]
    rcases le_total 0 (qSequence u n) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
  have hsub : harmonicSideOf u 1 X - harmonicSideOf u (-1) X =
      ∑ n ∈ Finset.range (X + 1), qSequence u n / (n : ℝ) := by
    rw [harmonicSideOf, harmonicSideOf, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [one_mul, neg_one_mul, ← sub_div]
    rcases le_total 0 (qSequence u n) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  rw [← hsum, ← hsub, minimumHarmonicPrefixOf]
  rcases le_total (harmonicSideOf u 1 X) (harmonicSideOf u (-1) X) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Prefix comparison at a fixed cutoff, including changes of sign. -/
theorem minimumHarmonicPrefixOf_error_sum (u v : QHilbert) (X : ℕ) :
    |minimumHarmonicPrefixOf u X - minimumHarmonicPrefixOf v X| ≤
      ∑ n ∈ Finset.range (X + 1), |qSequence (u - v) n| / (n : ℝ) := by
  let mass (a : QHilbert) := ∑ n ∈ Finset.range (X + 1), |qSequence a n| / (n : ℝ)
  have side (a b : QHilbert) (ε : ℝ) (hε : |ε| = 1) :
      harmonicSideOf a ε X ≤ harmonicSideOf b ε X + mass (a-b) := by
    unfold harmonicSideOf mass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hsub : qSequence (a-b) n = qSequence a n - qSequence b n :=
      congrFun (qSequenceLinear.map_sub a b) n
    have he := le_abs_self (ε * (qSequence a n - qSequence b n))
    rw [abs_mul, hε, one_mul, mul_sub, ← hsub] at he
    exact max_le (by linarith [le_max_left (ε * qSequence b n) 0])
      (add_nonneg (le_max_right _ _) (abs_nonneg _))
  have oneSide (a b : QHilbert) :
      minimumHarmonicPrefixOf a X ≤ minimumHarmonicPrefixOf b X + mass (a-b) := by
    unfold minimumHarmonicPrefixOf
    rcases le_total (harmonicSideOf b 1 X) (harmonicSideOf b (-1) X) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (side a b 1 abs_one)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (side a b (-1) (by norm_num))
  have hsym : mass (v-u) = mass (u-v) := by
    apply Finset.sum_congr rfl
    intro n _
    have h₁ : qSequence (v-u) n = qSequence v n - qSequence u n :=
      congrFun (qSequenceLinear.map_sub v u) n
    have h₂ : qSequence (u-v) n = qSequence u n - qSequence v n :=
      congrFun (qSequenceLinear.map_sub u v) n
    rw [h₁, h₂, abs_sub_comm (qSequence v n)]
  change _ ≤ mass (u-v)
  have ha := oneSide u v
  have hb := oneSide v u
  rw [hsym] at hb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Finite Cauchy–Schwarz uses exactly X positive sites. -/
theorem harmonicAbsPrefix_le_sqrt (u : QHilbert) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), |qSequence u n| / (n : ℝ)) ≤
      Real.sqrt (X : ℝ) * Real.sqrt zetaTwo * ‖u‖ := by
  let a (j : ℕ) := |qSequence u (j + 1)| / ((j + 1 : ℕ) : ℝ)
  have ha (j : ℕ) : a j ^ 2 = zetaTwo * (u j) ^ 2 := by
    rw [← qSequence_weighted_square u j]
    dsimp only [a, positiveQWeight]
    rw [div_pow, sq_abs]
    field_simp [zetaTwo_pos.ne', Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)]
  have hfin := sq_sum_le_card_mul_sum_sq (s := Finset.range X) (f := a)
  simp only [Finset.card_range, ha, ← Finset.mul_sum] at hfin
  have hen : (∑ j ∈ Finset.range X, (u j)^2) ≤ ‖u‖^2 := by
    rw [qNorm_sq]
    exact (qCoordinate_square_summable u).sum_le_tsum _ (fun j _ => sq_nonneg _)
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, div_zero, add_zero]
  change (∑ j ∈ Finset.range X, a j) ≤ _
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg X), Real.sq_sqrt zetaTwo_pos.le]
  calc
    _ ≤ (X : ℝ) * (zetaTwo * ∑ j ∈ Finset.range X, (u j)^2) := hfin
    _ ≤ (X : ℝ) * (zetaTwo * ‖u‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hen zetaTwo_pos.le)
        (Nat.cast_nonneg X)
    _ = _ := by ring

theorem minimumHarmonicPrefixOf_error (u v : QHilbert) (X : ℕ) :
    |minimumHarmonicPrefixOf u X - minimumHarmonicPrefixOf v X| ≤
      Real.sqrt (X : ℝ) * Real.sqrt zetaTwo * ‖u-v‖ :=
  (minimumHarmonicPrefixOf_error_sum u v X).trans (harmonicAbsPrefix_le_sqrt _ X)

/-- The checked complete-Q trial using conductors 2, 3 and 6 improves the
agenda's absolute budget by the factor sqrt(61/900). -/
theorem resolvent_harmonic_prefix_error (X j : ℕ) (hX : X ≤ 9 ^ j) :
    |minimumHarmonicPrefix X - minimumHarmonicPrefixOf (resolventApprox j) X| ≤
      Real.sqrt zetaTwo * Real.sqrt (61 / 7200 : ℝ) := by
  have h3 : qResidue 3 ∈ closure := by
    change qResidue 3 ∈ (Submodule.span ℝ (Set.range squarefreeAtom)).topologicalClosure
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    simp [squarefreeAtom, Nat.prime_three.squarefree]
  have hr := QSixAtomTrialBound.error_le_sixty_one closure
    QParityConditionalTarget.qResidue_two_mem_closure h3
    QParityConditionalTarget.qResidue_six_mem_closure
  change ‖limitingResidual‖ ^ 2 ≤ _ at hr
  have hd : ‖displacement‖ ≤ Real.sqrt (61 / 7200 : ℝ) := by
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 61 / 7200)]
    linarith [displacement_energy_bound]
  have hbound : (X : ℝ) ≤ (9:ℝ)^j := by exact_mod_cast hX
  have hp : ((3:ℝ)^j)^2 = (9:ℝ)^j := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  have hroot : Real.sqrt (X : ℝ) ≤ (3:ℝ)^j :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by rwa [hp]⟩
  have hf : Real.sqrt (X : ℝ) * (1 / 3 : ℝ)^j ≤ 1 := by
    calc
      _ ≤ (3:ℝ)^j * (1 / 3 : ℝ)^j := mul_le_mul_of_nonneg_right hroot (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  calc
    _ ≤ Real.sqrt (X : ℝ) * Real.sqrt zetaTwo * ‖displacement - resolventApprox j‖ :=
      minimumHarmonicPrefixOf_error _ _ _
    _ ≤ Real.sqrt (X : ℝ) * Real.sqrt zetaTwo * ((1 / 3 : ℝ)^j * ‖displacement‖) :=
      mul_le_mul_of_nonneg_left (resolvent_error_norm_le j) (by positivity)
    _ = (Real.sqrt (X : ℝ) * (1 / 3 : ℝ)^j) * (Real.sqrt zetaTwo * ‖displacement‖) := by ring
    _ ≤ 1 * (Real.sqrt zetaTwo * ‖displacement‖) := mul_le_mul_of_nonneg_right hf (by positivity)
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg zetaTwo)

/-- Cofinal finite iteration depths with an arithmetically bounded prefix
imply RH. Depth and sign can both depend on the observed cutoff. -/
theorem riemannHypothesis_of_cofinal_resolvent_prefix (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∃ᶠ X : ℕ in atTop, ∃ j : ℕ, X ≤ 9 ^ j ∧
      minimumHarmonicPrefixOf (resolventApprox j) X ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis := by
  let K := Real.sqrt zetaTwo * Real.sqrt (61 / 7200 : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply riemannHypothesis_of_cofinal_harmonic_polylog B (C + K) hB (add_nonneg hC hK)
  have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply (h.and_eventually (hlog.eventually_ge_atTop 1)).mono
  rintro X ⟨⟨j,hX,hj⟩,hl⟩
  have hp := Real.one_le_rpow hl hB
  have hb := (abs_le.mp (resolvent_harmonic_prefix_error X j hX)).2
  change _ ≤ K at hb
  have hc := mul_le_mul_of_nonneg_left hp hK
  rw [add_mul]
  linarith

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
