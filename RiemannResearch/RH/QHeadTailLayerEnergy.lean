/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHeadCrossMoments
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QPolylogMovingHeadEnergy
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.RH.QUniformTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Capped layer-cake identities and negative cumulative variation

Source: the user's missing squarefree positive-moment bound request,
26 October 2026. The exact layer-cake identity retains the endpoint tail.
The unconditional negative-variation estimate does not control the positive
variation that appears with the opposite sign in finite Abel summation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QHeadCrossMoments
open ZetaTwoHilbert QAnnihilatorTailEscape QPolylogTailEnergy
open RiemannResearch.Analysis.LogTailWeights

def cappedTailEnergy (k H : ℕ) (f : QHilbert) : ℝ :=
  ∑ t ∈ Finset.range H,
    (polylogTailProfile k (t + 1) - polylogTailProfile k t) * ‖tail t f‖ ^ 2

theorem sum_profile_increments (k H : ℕ) :
    (∑ t ∈ Finset.range H,
      (polylogTailProfile k (t + 1) - polylogTailProfile k t)) =
        polylogTailProfile k H := by
  induction H with
  | zero => simp [polylogTailProfile_eq]
  | succ H ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem headCross_self (H : ℕ) (f : QHilbert) :
    headCross H f f = ‖f‖ ^ 2 - ‖tail H f‖ ^ 2 := by
  have h := inner_eq_headCross_add_tail H f f
  simp only [real_inner_self_eq_norm_sq] at h
  linarith

theorem weightedHeadCross_self (k H : ℕ) (f : QHilbert) :
    weightedHeadCross k H f f = weightedHeadEnergy k H f := by
  unfold weightedHeadCross weightedHeadEnergy
  apply Finset.sum_congr rfl
  intro n hn
  simp only [polylogWeightedEnergyTerm, pow_two, mul_assoc]

/-- Exact capped layer-cake identity. The final physical tail is retained. -/
theorem cappedTailEnergy_exact (k H : ℕ) (f : QHilbert) :
    cappedTailEnergy k H f = weightedHeadEnergy k H f +
      polylogTailProfile k H * ‖tail H f‖ ^ 2 := by
  have ha := weightedHeadCross_abel k H f f
  rw [weightedHeadCross_self] at ha
  simp_rw [headCross_self] at ha
  have hs :
      (∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          (‖f‖ ^ 2 - ‖tail t f‖ ^ 2)) =
        (∑ t ∈ Finset.range H,
          (polylogTailProfile k (t + 1) - polylogTailProfile k t)) * ‖f‖ ^ 2 -
        cappedTailEnergy k H f := by
    unfold cappedTailEnergy
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hs, sum_profile_increments] at ha
  nlinarith

/-- The capped layer energy is bounded by the complete weighted energy. -/
theorem cappedTailEnergy_le_total (k H : ℕ) (f : QHilbert)
    (hs : Summable (polylogWeightedEnergyTerm k f)) :
    cappedTailEnergy k H f ≤ ∑' n : ℕ, polylogWeightedEnergyTerm k f n := by
  have hq : Summable (fun j : ℕ => positiveQWeight (j + (H + 1)) *
      qSequence f (j + (H + 1)) ^ 2) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => positiveQWeight n * qSequence f n ^ 2)
      (H + 1)).mpr (qSequence_square_summable f)
  have ht : Summable (fun j : ℕ => polylogWeightedEnergyTerm k f (j + (H + 1))) :=
    (summable_nat_add_iff (f := polylogWeightedEnergyTerm k f) (H + 1)).mpr hs
  have hb (j : ℕ) : polylogTailProfile k H *
      (positiveQWeight (j + (H + 1)) * qSequence f (j + (H + 1)) ^ 2) ≤
      polylogWeightedEnergyTerm k f (j + (H + 1)) := by
    have hp := polylogTailProfile_monotone k (by omega : H ≤ j + (H + 1))
    have h := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (positiveQWeight_nonneg (j + (H + 1)))
        (sq_nonneg (qSequence f (j + (H + 1)))))
    simpa only [polylogWeightedEnergyTerm, mul_assoc] using h
  have hsum := (hq.mul_left (polylogTailProfile k H)).tsum_le_tsum hb ht
  rw [tsum_mul_left] at hsum
  have he := hs.sum_add_tsum_nat_add (H + 1)
  rw [cappedTailEnergy_exact, tail_energy_physical]
  change (∑ n ∈ Finset.range (H + 1), polylogWeightedEnergyTerm k f n) +
    polylogTailProfile k H *
      (∑' j : ℕ, positiveQWeight (j + H + 1) * qSequence f (j + H + 1) ^ 2) ≤ _
  simp only [Nat.add_assoc] at hsum ⊢
  linarith

/-- The negative cumulative variation has the sign opposite to the missing
positive-variation upper bound in the RH criterion. -/
def negativeCrossVariation (k H : ℕ) (b e : QHilbert) : ℝ :=
  ∑ t ∈ Finset.range H,
    (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
      max (-headCross t b e) 0

theorem negativeCrossVariation_le_source_layer (k H : ℕ) (b u : QHilbert)
    (horth : inner ℝ b (u - b) = 0) :
    negativeCrossVariation k H b (u - b) ≤ cappedTailEnergy k H u / 4 := by
  have hterm (t : ℕ) : max (-headCross t b (u - b)) 0 ≤ ‖tail t u‖ ^ 2 / 4 := by
    apply max_le
    · have h := headCross_lower t b u horth
      linarith
    · positivity
  have hs : negativeCrossVariation k H b (u - b) ≤
      ∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          (‖tail t u‖ ^ 2 / 4) := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_left (hterm t)
      (sub_nonneg.mpr (polylogTailProfile_monotone k (Nat.le_succ t)))
  simpa only [cappedTailEnergy, Finset.sum_div, mul_div_assoc] using hs

theorem negativeCrossVariation_le_source_total (k H : ℕ) (b u : QHilbert)
    (horth : inner ℝ b (u - b) = 0)
    (hu : Summable (polylogWeightedEnergyTerm k u)) :
    negativeCrossVariation k H b (u - b) ≤
      (∑' n : ℕ, polylogWeightedEnergyTerm k u n) / 4 := by
  exact (negativeCrossVariation_le_source_layer k H b u horth).trans
    (div_le_div_of_nonneg_right (cappedTailEnergy_le_total k H u hu) (by norm_num))

/-- The complete signed norm identity, before replacing a cumulative moment by
its positive part. -/
theorem tail_energy_eq_twice_headCross_add_source_sub_square
    (H : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0) :
    ‖tail H b‖ ^ 2 = 2 * headCross H b (u - b) + ‖tail H u‖ ^ 2 -
      ‖tail H b - tail H u‖ ^ 2 := by
  rw [headCross_eq_tail_energy H b u horth, norm_sub_sq_real]
  ring

/-- Exact signed decomposition, retaining both cumulative signs and the whole
nonnegative remainder. -/
theorem cappedTailEnergy_signed_split (k H : ℕ) (b u : QHilbert)
    (horth : inner ℝ b (u - b) = 0) :
    cappedTailEnergy k H b =
      2 * (positiveCrossVariation k H b (u - b) -
        negativeCrossVariation k H b (u - b)) +
      cappedTailEnergy k H u - cappedTailEnergy k H (b - u) := by
  unfold cappedTailEnergy positiveCrossVariation negativeCrossVariation
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hm : max (headCross t b (u - b)) 0 -
      max (-headCross t b (u - b)) 0 = headCross t b (u - b) := by
    rcases le_total 0 (headCross t b (u - b)) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  have he := tail_energy_eq_twice_headCross_add_source_sub_square t b u horth
  rw [tail_sub]
  nlinarith [congrArg
    (fun x : ℝ => (polylogTailProfile k (t + 1) - polylogTailProfile k t) * x) he,
    congrArg (fun x : ℝ =>
      (polylogTailProfile k (t + 1) - polylogTailProfile k t) * x) hm]

theorem cappedTailEnergy_le_positive_variation_add_source
    (k H : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0) :
    cappedTailEnergy k H b ≤
      2 * positiveCrossVariation k H b (u - b) + cappedTailEnergy k H u := by
  have hterm (t : ℕ) : ‖tail t b‖ ^ 2 ≤
      2 * max (headCross t b (u - b)) 0 + ‖tail t u‖ ^ 2 := by
    have he := tail_energy_eq_twice_headCross_add_source_sub_square t b u horth
    have hm := le_max_left (headCross t b (u - b)) 0
    nlinarith [sq_nonneg ‖tail t b - tail t u‖]
  have hs : cappedTailEnergy k H b ≤
      ∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          (2 * max (headCross t b (u - b)) 0 + ‖tail t u‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_left (hterm t)
      (sub_nonneg.mpr (polylogTailProfile_monotone k (Nat.le_succ t)))
  convert hs using 1
  unfold positiveCrossVariation cappedTailEnergy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem weightedHeadEnergy_le_positive_variation_add_source_total
    (k H : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0)
    (hu : Summable (polylogWeightedEnergyTerm k u)) :
    weightedHeadEnergy k H b ≤
      2 * positiveCrossVariation k H b (u - b) +
        (∑' n : ℕ, polylogWeightedEnergyTerm k u n) := by
  have h := cappedTailEnergy_le_positive_variation_add_source k H b u horth
  have hs := cappedTailEnergy_le_total k H u hu
  have he := cappedTailEnergy_exact k H b
  have hn : 0 ≤ polylogTailProfile k H * ‖tail H b‖ ^ 2 :=
    mul_nonneg (polylogTailProfile_nonneg k H) (sq_nonneg _)
  linarith

/-- Positive variation differs from correction layer energy by at most the
geometric mean of the correction and source layer energies. -/
theorem positiveCrossVariation_sub_layer_quadratic
    (k H : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0) (c : ℝ) :
    2 * c * (positiveCrossVariation k H b (u - b) - cappedTailEnergy k H b) ≤
      c ^ 2 * cappedTailEnergy k H b + cappedTailEnergy k H u := by
  have hterm (t : ℕ) :
      2 * c * (max (headCross t b (u - b)) 0 - ‖tail t b‖ ^ 2) ≤
        c ^ 2 * ‖tail t b‖ ^ 2 + ‖tail t u‖ ^ 2 := by
    rw [headCross_eq_tail_energy t b u horth]
    by_cases hm : 0 ≤ ‖tail t b‖ ^ 2 - inner ℝ (tail t b) (tail t u)
    · rw [max_eq_left hm]
      have hn := sq_nonneg ‖c • tail t b + tail t u‖
      simp only [norm_add_sq_real, norm_smul, real_inner_smul_left,
        Real.norm_eq_abs, mul_pow, sq_abs] at hn
      nlinarith
    · rw [max_eq_right (le_of_not_ge hm)]
      have hn := sq_nonneg ‖tail t b - tail t u‖
      rw [norm_sub_sq_real] at hn
      have hbu : ‖tail t b‖ ^ 2 ≤ ‖tail t u‖ ^ 2 := by
        nlinarith
      have hp := mul_nonneg (sq_nonneg (c + 1)) (sq_nonneg ‖tail t b‖)
      nlinarith
  have hs :
      (∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          (2 * c * (max (headCross t b (u - b)) 0 - ‖tail t b‖ ^ 2))) ≤
      ∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          (c ^ 2 * ‖tail t b‖ ^ 2 + ‖tail t u‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_left (hterm t)
      (sub_nonneg.mpr (polylogTailProfile_monotone k (Nat.le_succ t)))
  have hl :
      (∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          (2 * c * (max (headCross t b (u - b)) 0 - ‖tail t b‖ ^ 2))) =
      2 * c * (positiveCrossVariation k H b (u - b) - cappedTailEnergy k H b) := by
    unfold positiveCrossVariation cappedTailEnergy
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hr :
      (∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) *
          (c ^ 2 * ‖tail t b‖ ^ 2 + ‖tail t u‖ ^ 2)) =
      c ^ 2 * cappedTailEnergy k H b + cappedTailEnergy k H u := by
    unfold cappedTailEnergy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rwa [hl, hr] at hs

/-- The exact quadratic comparison requires no summability hypothesis. -/
theorem positiveCrossVariation_sub_layer_sq_le
    (k H : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0) :
    (positiveCrossVariation k H b (u - b) - cappedTailEnergy k H b) ^ 2 ≤
      cappedTailEnergy k H b * cappedTailEnergy k H u := by
  let D := positiveCrossVariation k H b (u - b) - cappedTailEnergy k H b
  let X := cappedTailEnergy k H b
  let S := cappedTailEnergy k H u
  have hX : 0 ≤ X := by
    apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg
      (sub_nonneg.mpr (polylogTailProfile_monotone k (Nat.le_succ t)))
      (sq_nonneg _)
  have hq (c : ℝ) : 2 * c * D ≤ c ^ 2 * X + S :=
    positiveCrossVariation_sub_layer_quadratic k H b u horth c
  change D ^ 2 ≤ X * S
  by_cases hx : X = 0
  · have hd : D = 0 := by
      by_contra hd
      have hh := hq ((S + 1) / (2 * D))
      rw [hx] at hh
      have he : 2 * ((S + 1) / (2 * D)) * D = S + 1 := by
        field_simp [hd]
      rw [he] at hh
      linarith
    rw [hd, hx]
    norm_num
  · have hh := mul_le_mul_of_nonneg_right (hq (D / X)) hX
    have hl : (2 * (D / X) * D) * X = 2 * D ^ 2 := by
      field_simp [hx]
    have hr : ((D / X) ^ 2 * X + S) * X = D ^ 2 + S * X := by
      field_simp [hx]
    rw [hl, hr] at hh
    nlinarith

/-- A convenient rational upper bound, reverse to the previously established
source-plus-positive-variation control of correction energy. -/
theorem positiveCrossVariation_le_layer_add_source
    (k H : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0) :
    positiveCrossVariation k H b (u - b) ≤
      3 / 2 * cappedTailEnergy k H b + cappedTailEnergy k H u / 2 := by
  have h := positiveCrossVariation_sub_layer_quadratic k H b u horth 1
  norm_num at h
  linarith

open Filter
open scoped Topology

/-- For a summable weighted source, even a cofinal bound on positive variation
is equivalent to complete weighted summability of the correction. -/
theorem weightedEnergy_summable_iff_frequently_positiveCrossVariation_bounded
    (k : ℕ) (b u : QHilbert) (horth : inner ℝ b (u - b) = 0)
    (hu : Summable (polylogWeightedEnergyTerm k u)) :
    Summable (polylogWeightedEnergyTerm k b) ↔
      ∃ C : ℝ, ∃ᶠ H : ℕ in atTop,
        positiveCrossVariation k H b (u - b) ≤ C := by
  constructor
  · intro hb
    refine ⟨3 / 2 * (∑' n : ℕ, polylogWeightedEnergyTerm k b n) +
      (∑' n : ℕ, polylogWeightedEnergyTerm k u n) / 2,
      (Eventually.of_forall ?_).frequently⟩
    intro H
    have hp := positiveCrossVariation_le_layer_add_source k H b u horth
    have hbl := cappedTailEnergy_le_total k H b hb
    have hul := cappedTailEnergy_le_total k H u hu
    linarith
  · rintro ⟨C, hC⟩
    have hh : ∃ᶠ H : ℕ in atTop, weightedHeadEnergy k H b ≤
        2 * C + (∑' n : ℕ, polylogWeightedEnergyTerm k u n) := by
      apply hC.mono
      intro H hH
      have he := weightedHeadEnergy_le_positive_variation_add_source_total
        k H b u horth hu
      linarith
    exact (weightedEnergy_summable_of_frequently_moving_head_bound
      k (fun _ : ℕ => b) b tendsto_const_nhds id tendsto_id
      (2 * C + (∑' n : ℕ, polylogWeightedEnergyTerm k u n)) hh).1

/-- A bounded source layer budget makes the correction layer and positive
variation budgets equivalent, uniformly for an arbitrary indexed family. -/
theorem uniform_cappedTailEnergy_iff_positiveCrossVariation
    {ι : Type*} (k : ℕ) (H : ι → ℕ) (b u : ι → QHilbert)
    (horth : ∀ i, inner ℝ (b i) (u i - b i) = 0)
    (S : ℝ) (hs : ∀ i, cappedTailEnergy k (H i) (u i) ≤ S) :
    (∃ C : ℝ, ∀ i, cappedTailEnergy k (H i) (b i) ≤ C) ↔
    (∃ C : ℝ, ∀ i, positiveCrossVariation k (H i) (b i) (u i - b i) ≤ C) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨3 / 2 * C + S / 2, ?_⟩
    intro i
    have hp := positiveCrossVariation_le_layer_add_source k (H i) (b i) (u i) (horth i)
    have hc := hC i
    have hsi := hs i
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨2 * C + S, ?_⟩
    intro i
    have hp := cappedTailEnergy_le_positive_variation_add_source
      k (H i) (b i) (u i) (horth i)
    have hc := hC i
    have hsi := hs i
    linarith

theorem cappedTailEnergy_le_profile_norm_sq (k H : ℕ) (f : QHilbert) :
    cappedTailEnergy k H f ≤ polylogTailProfile k H * ‖f‖ ^ 2 := by
  have hs : cappedTailEnergy k H f ≤
      ∑ t ∈ Finset.range H,
        (polylogTailProfile k (t + 1) - polylogTailProfile k t) * ‖f‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left _
      (sub_nonneg.mpr (polylogTailProfile_monotone k (Nat.le_succ t)))
    have hn := tail_norm_le t f
    nlinarith [norm_nonneg (tail t f), norm_nonneg f]
  rwa [← Finset.sum_mul, sum_profile_increments] at hs


end RiemannResearch.RH.QHeadCrossMoments
