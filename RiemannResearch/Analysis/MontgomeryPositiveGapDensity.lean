/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import RiemannResearch.Analysis.OrdinateCollisionCertificate
import RiemannResearch.Analysis.ActualZeroWindowVariance
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.CosineReciprocalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Montgomery's strictly positive-gap conjecture and horizontal multiplicity

Goldston, Lee, Schettler and Suriajaya, *Pair Correlation Conjecture for the
zeros of the Riemann zeta-function I*, §§1–3, (1.5), Propositions 1 and 2,
https://doi.org/10.1112/mtk.70127 and https://arxiv.org/abs/2503.15449.
The conjecture counts strictly positive ordinate differences. The separate
one-sided short-window moment estimate is unconditional in the paper.
We use its consequence for the finite triangle of actual zero occurrences
and keep this analytic input explicit. The exact triangle formula separates
the equal-ordinate atom from the positive gaps before invoking either bound.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open ActualZeroWindowVariance

private def gapStep (d u : ℝ) : ℝ := if 0 < d ∧ d ≤ u then 1 else 0

private def positiveHinge (R d : ℝ) : ℝ := if 0 < d then max (R - d) 0 else 0

/-- Ordered pairs of zero copies whose unfolded difference lies in (0,u],
normalized by T log(T)/(2π), as in GLSS (1.3)–(1.5). -/
def positiveGapMass (T u : ℝ) : ℝ :=
  (∑ i : Copies T, ∑ j : Copies T,
    gapStep (Real.log T / (2 * Real.pi) * (copyOrdinate T j - copyOrdinate T i)) u) /
      (T * Real.log T / (2 * Real.pi))

def sineGapMass (u : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..u, 1 - Real.sinc (Real.pi * x) ^ 2

/-- The strict positive-gap counting formulation of Montgomery's conjecture,
uniform on compact subintervals of (0,∞). -/
def PositiveGapPCC : Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∀ η : ℝ, 0 < η →
    ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b, |positiveGapMass T u - sineGapMass u| ≤ η

/-- The one-sided second moment used in the deduction. GLSS Propositions 1
and 2 give a fixed-width error of order log(2+R) as T tends to infinity,
which is sublinear in R. The existential width is all the argument needs. -/
def ShortWindowSecondMomentUpper : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ᶠ T : ℝ in atTop,
    actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) ≤ R ^ 2 + ε * R

/-- The missing mass from the sine-kernel hole on the positive half-line is 1/2. -/
theorem integral_sinc_sq_pi_Ioi :
    (∫ x in Ioi (0 : ℝ), Real.sinc (Real.pi * x) ^ 2) = 1 / 2 := by
  let q := fun u : ℝ => (1 - Real.cos u) / u ^ 2
  have hscale := integral_comp_mul_right_Ioi q 0 (by positivity : 0 < 2 * Real.pi)
  have he : (∫ x in Ioi (0 : ℝ), Real.sinc (Real.pi * x) ^ 2) =
      ∫ x in Ioi (0 : ℝ), 2 * q (x * (2 * Real.pi)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    dsimp only [q]
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx0),
      show x * (2 * Real.pi) = 2 * (Real.pi * x) by ring, Real.cos_two_mul_eq_one_sub]
    field_simp [Real.pi_ne_zero, hx0]
    ring
  rw [he, integral_const_mul, hscale]
  simp only [zero_mul, smul_eq_mul, q, integral_one_sub_cos_div_sq_Ioi]
  field_simp [Real.pi_ne_zero]

theorem sineGapMass_lower {u : ℝ} (hu : 0 ≤ u) : u - 1 / 2 ≤ sineGapMass u := by
  have hi : IntegrableOn (fun x : ℝ => Real.sinc (Real.pi * x) ^ 2) (Ioi (0 : ℝ)) := by
    by_contra hn
    have hh := integral_undef hn
    rw [integral_sinc_sq_pi_Ioi] at hh
    norm_num at hh
  have hsub : Ioc (0 : ℝ) u ⊆ Ioi 0 := fun _ hx => hx.1
  have hle := setIntegral_mono_set hi (Eventually.of_forall (fun x => sq_nonneg _))
    hsub.eventuallyLE
  rw [integral_sinc_sq_pi_Ioi] at hle
  rw [sineGapMass, intervalIntegral.integral_sub intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_of_le hu]
  simpa only [sub_zero, smul_eq_mul, mul_one] using sub_le_sub_left hle u

theorem positiveGapMass_nonneg {T : ℝ} (hT : 1 < T) (u : ℝ) : 0 ≤ positiveGapMass T u := by
  unfold positiveGapMass
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    unfold gapStep
    split <;> norm_num
  · exact div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity)

theorem positiveGapMass_mono {T : ℝ} (hT : 1 < T) : Monotone (positiveGapMass T) := by
  intro a b hab
  unfold positiveGapMass
  apply div_le_div_of_nonneg_right _ (div_nonneg
    (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity))
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold gapStep
  split_ifs with ha hb hb
  · exact le_rfl
  · exact False.elim (hb ⟨ha.1, ha.2.trans hab⟩)
  · norm_num
  · exact le_rfl

/-- GLSS ES2. On every shrinking unfolded window, the positive pair count
is negligible under the usual counting conjecture alone. -/
theorem shrinking_positive_gap_limit (h : PositiveGapPCC) {u : ℝ → ℝ}
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => positiveGapMass T (u T)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact ha.trans_le (positiveGapMass_nonneg hT _)
  · intro b hb
    let δ := b / 4
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hs : sineGapMass δ ≤ δ := by
      have hint : Continuous (fun x : ℝ => 1 - Real.sinc (Real.pi * x) ^ 2) := by fun_prop
      have hl := intervalIntegral.integral_mono_on hδ.le (hint.intervalIntegrable 0 δ)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 δ)
        (fun x _ => sub_le_self _ (sq_nonneg _))
      simpa [sineGapMass] using hl
    filter_upwards [h δ δ hδ le_rfl δ hδ, hu.eventually (gt_mem_nhds hδ),
      eventually_gt_atTop (1 : ℝ)] with T hp hsmall hT
    apply (positiveGapMass_mono hT (le_of_lt hsmall)).trans_lt
    have he := (abs_le.mp (hp δ ⟨le_rfl, le_rfl⟩)).2
    dsimp [δ] at he hs ⊢
    linarith

private theorem gapStep_of_pos {d : ℝ} (hd : 0 < d) :
    gapStep d = (Ici d).indicator (fun _ => (1 : ℝ)) := by
  funext u
  by_cases hu : d ≤ u <;> simp [gapStep, hd, hu, Set.indicator, Set.mem_Ici]

private theorem gapStep_intervalIntegrable (d : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (gapStep d) volume 0 R := by
  by_cases hd : 0 < d
  · rw [gapStep_of_pos hd, intervalIntegrable_iff_integrableOn_Ioc_of_le hR]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 R)).indicator
      measurableSet_Ici
  · have hz : gapStep d = fun _ => (0 : ℝ) := by
      funext u
      simp [gapStep, hd]
    rw [hz]
    exact intervalIntegrable_const

private theorem integral_gapStep (d : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ u in (0 : ℝ)..R, gapStep d u) = positiveHinge R d := by
  by_cases hd : 0 < d
  · have hi : Ici d ∩ Ioc 0 R = Icc d R := by
      ext u
      change (d ≤ u ∧ 0 < u ∧ u ≤ R) ↔ d ≤ u ∧ u ≤ R
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hd.trans_le h.1, h.2⟩⟩
    rw [gapStep_of_pos hd, intervalIntegral.integral_of_le hR, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, hi]
    by_cases hdr : d ≤ R
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hdr]
      simp [positiveHinge, hd, max_eq_left (sub_nonneg.mpr hdr)]
    · rw [Icc_eq_empty_of_lt (lt_of_not_ge hdr)]
      simp [positiveHinge, hd, max_eq_right (sub_nonpos.mpr (le_of_not_ge hdr))]
  · simp [gapStep, positiveHinge, hd]

private theorem positiveGapMass_intervalIntegrable (T : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (positiveGapMass T) volume 0 R := by
  unfold positiveGapMass
  apply IntervalIntegrable.div_const
  apply intervalIntegrable_iff.mpr
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (gapStep_intervalIntegrable _ hR).def'))

/-- The finite GLSS first-moment identity in unfolded coordinates. It
uses the physical triangle for occurrences already cut off at T and has
no endpoint approximation. Equal ordinates and both orientations are explicit. -/
theorem physicalTriangle_eq_collision_add_positive_gaps {T R : ℝ} (hT : 1 < T) (hR : 0 ≤ R) :
    actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) =
      R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) +
        2 * ∫ u in (0 : ℝ)..R, positiveGapMass T u := by
  classical
  let L := Real.log T / (2 * Real.pi)
  let D := T * Real.log T / (2 * Real.pi)
  let t := copyOrdinate T
  let d := fun i j : Copies T => L * (t j - t i)
  have ht : 0 < T := zero_lt_one.trans hT
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hD : D = T * L := by dsimp [D, L]; ring
  have hD0 : 0 < D := by rw [hD]; exact mul_pos ht hL
  have split (i j : Copies T) : max (R - |d i j|) 0 =
      (if t i = t j then R else 0) + positiveHinge R (d i j) + positiveHinge R (d j i) := by
    have hn : d j i = -d i j := by dsimp [d]; ring
    rcases lt_trichotomy (t i) (t j) with hh | hh | hh
    · have hp : 0 < d i j := mul_pos hL (sub_pos.mpr hh)
      simp [positiveHinge, hh.ne, hn, hp, abs_of_pos hp, not_lt_of_ge hp.le]
    · have hz : d i j = 0 := by simp [d, hh]
      simp [positiveHinge, hh, hn, hz, max_eq_left hR]
    · have hp : d i j < 0 := mul_neg_of_pos_of_neg hL (sub_neg.mpr hh)
      simp [positiveHinge, hh.ne', hn, hp, not_lt_of_ge hp.le, abs_of_neg hp]
  have diag : (∑ i : Copies T, ∑ j : Copies T, if t i = t j then R else 0) =
      R * (actualCollision T : ℝ) := by
    unfold actualCollision occurrenceCollision
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (if t i = t j then R else 0) = R * (if t i = t j then 1 else 0)
    by_cases he : t i = t j <;> simp [he]
  have swap : (∑ i : Copies T, ∑ j : Copies T, positiveHinge R (d j i)) =
      ∑ i : Copies T, ∑ j : Copies T, positiveHinge R (d i j) := Finset.sum_comm
  have total : (∑ i : Copies T, ∑ j : Copies T, max (R - |d i j|) 0) =
      R * (actualCollision T : ℝ) +
        2 * ∑ i : Copies T, ∑ j : Copies T, positiveHinge R (d i j) := by
    simp_rw [split, Finset.sum_add_distrib]
    rw [diag, swap]
    ring
  have scale (i j : Copies T) : max (R / L - |t i - t j|) 0 * L = max (R - |d i j|) 0 := by
    rw [max_mul_of_nonneg _ _ hL.le, sub_mul, div_mul_cancel₀ _ hL.ne', zero_mul]
    dsimp [d]
    rw [abs_mul, abs_of_pos hL, abs_sub_comm (t j) (t i), mul_comm L]
  have physical : actualPhysicalTriangleEnergy T (R / L) * D =
      ∑ i : Copies T, ∑ j : Copies T, max (R - |d i j|) 0 := by
    change ((∑ i : Copies T, ∑ j : Copies T, max (R / L - |t i - t j|) 0) / T) * D = _
    rw [hD, ← mul_assoc, div_mul_cancel₀ _ ht.ne']
    simp only [Finset.sum_mul, scale]
  have pos : (∫ u in (0 : ℝ)..R, positiveGapMass T u) =
      (∑ i : Copies T, ∑ j : Copies T, positiveHinge R (d i j)) / D := by
    unfold positiveGapMass
    rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum (fun j _ => gapStep_intervalIntegrable _ hR)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_gapStep _ hR
    · intro i _
      apply intervalIntegrable_iff.mpr
      exact integrable_finsetSum _ (fun j _ => (gapStep_intervalIntegrable _ hR).def')
  rw [pos]
  change actualPhysicalTriangleEnergy T (R / L) = R * ((actualCollision T : ℝ) / D) + _
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  exact (eq_div_iff hD0.ne').mpr (physical.trans total)

private theorem eventually_gap_lower (h : PositiveGapPCC) {R η : ℝ} (hR : 1 ≤ R) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc (0 : ℝ) R, u - 1 / 2 - η ≤ positiveGapMass T u := by
  filter_upwards [h (1 / 2) R (by norm_num) (by linarith) η hη,
    eventually_gt_atTop (1 : ℝ)] with T hp hT
  intro u hu
  by_cases hlow : 1 / 2 ≤ u
  · have hg := (abs_le.mp (hp u ⟨hlow, hu.2⟩)).1
    linarith only [hg, sineGapMass_lower hu.1]
  · linarith only [positiveGapMass_nonneg hT u, hlow, hη]

/-- GLSS ES1 follows from the strictly positive-gap PCC and the independent
one-sided short-interval second moment. -/
theorem collision_limit_of_positiveGapPCC (h : PositiveGapPCC) (hm : ShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [tendsto_count_div_mainTerm.eventually (lt_mem_nhds ha),
      eventually_gt_atTop (1 : ℝ)] with T hn hT
    have hc := actualCollision_eq_count_add_excess T
    have hle : Ncount 0 T ≤ actualCollision T := by omega
    exact hn.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hle)
      (div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity)))
  · intro b hb
    let η := (b - 1) / 4
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨R, hR, hupper⟩ := hm η hη
    have hR0 := zero_lt_one.trans_le hR
    have hlin (x : ℝ) : HasDerivAt (fun u : ℝ => u ^ 2 / 2 - (1 / 2 + η) * u)
        (x - 1 / 2 - η) x := by
      have h' := (((hasDerivAt_id x).pow 2).div_const 2).sub
        ((hasDerivAt_id x).const_mul (1 / 2 + η))
      convert h' using 1 <;> first | rfl | (simp only [id_eq]; ring)
    have ic : Continuous (fun u : ℝ => u - 1 / 2 - η) := by fun_prop
    have eval : (∫ u in (0 : ℝ)..R, u - 1 / 2 - η) = R ^ 2 / 2 - (1 / 2 + η) * R := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hlin x)
        (ic.intervalIntegrable _ _)]
      ring
    filter_upwards [hupper, eventually_gap_lower h hR hη, eventually_gt_atTop (1 : ℝ)]
      with T hwindow hlower hT
    have harea := intervalIntegral.integral_mono_on hR0.le (ic.intervalIntegrable _ _)
      (positiveGapMass_intervalIntegrable T hR0.le) hlower
    rw [eval] at harea
    rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at hwindow
    let c := (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))
    have hbound : c * R ≤ (1 + 3 * η) * R := by dsimp [c]; linarith only [harea, hwindow]
    have hh : c ≤ 1 + 3 * η := le_of_mul_le_mul_right hbound hR0
    exact lt_of_le_of_lt hh (by dsimp [η]; linarith only [hb])

theorem density_one_of_positiveGapPCC (h : PositiveGapPCC) (hm : ShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  density_one_of_collision_limit (collision_limit_of_positiveGapPCC h hm)

end RiemannResearch.Analysis.MontgomeryPositiveGap
