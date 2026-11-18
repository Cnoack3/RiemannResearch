/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFejerDensity
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.OrdinateCollisionCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sensitivity of the raw form factor to two added occurrences

Two labeled zeros at a fresh common height model a reflected off-line pair.
Their contribution to the ordered equal-height count is four. Only two of
these pairs belong to the same labeled zero. The exact Fourier perturbation
uses the genuine ordinates in its cross term and the existing Cauchy row bound.
-/

noncomputable section
open Filter
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate OrdinateCollisionCertificate MontgomeryLocalMass MontgomeryPoisson

private theorem kernelEnergy_add_two_at_height {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (τ : ℝ) (k : ℝ → ℝ) :
    kernelEnergy (Sum.elim t (fun _ : Fin 2 => τ)) k =
      kernelEnergy t k + 2 * (∑ i, k (t i - τ)) + 2 * (∑ i, k (τ - t i)) + 4 * k 0 := by
  classical
  unfold kernelEnergy
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sub_self,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem occurrenceCollision_cast_eq_kernelEnergy {ι : Type*} [Fintype ι]
    (t : ι → ℝ) : (occurrenceCollision t : ℝ) =
      kernelEnergy t (fun d => if d = 0 then 1 else 0) := by
  classical
  simp only [occurrenceCollision, kernelEnergy, sub_eq_zero, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem occurrenceCollision_add_two_at_fresh_height {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (τ : ℝ) (hfresh : ∀ i, t i ≠ τ) :
    occurrenceCollision (Sum.elim t (fun _ : Fin 2 => τ)) = occurrenceCollision t + 4 := by
  classical
  have he : (occurrenceCollision (Sum.elim t (fun _ : Fin 2 => τ)) : ℝ) =
      (occurrenceCollision t : ℝ) + 4 := by
    rw [occurrenceCollision_cast_eq_kernelEnergy (Sum.elim t (fun _ : Fin 2 => τ)),
      occurrenceCollision_cast_eq_kernelEnergy t, kernelEnergy_add_two_at_height]
    simp [sub_eq_zero, hfresh, fun i => (hfresh i).symm]
  exact_mod_cast he

/-- The raw statistic of the actual cutoff with two additional copies at `τ`
and with its original normalization. -/
def formFactorWithTwoAtHeight (T τ α : ℝ) : ℝ :=
  (pairSum (Sum.elim (copyOrdinate T) (fun _ : Fin 2 => τ)) (α * Real.log T)).re /
    (T * Real.log T / (2 * Real.pi))

theorem formFactorWithTwoAtHeight_sub_eq (T τ α : ℝ) :
    formFactorWithTwoAtHeight T τ α - formFactor T α =
      4 * (1 + ∑ i : Copies T, cauchyWeight (τ - copyOrdinate T i) *
        Real.cos ((α * Real.log T) * (τ - copyOrdinate T i))) /
        (T * Real.log T / (2 * Real.pi)) := by
  let k := fun d : ℝ => cauchyWeight d * Real.cos ((α * Real.log T) * d)
  have hneg (d : ℝ) : k (-d) = k d := by
    simp [k, cauchyWeight_neg, mul_neg, Real.cos_neg]
  have hflip (i : Copies T) : k (copyOrdinate T i - τ) = k (τ - copyOrdinate T i) := by
    rw [← hneg (τ - copyOrdinate T i), neg_sub]
  have h0 : k 0 = 1 := by simp [k, cauchyWeight]
  unfold formFactorWithTwoAtHeight formFactor
  rw [pairSum_re_cos, pairSum_re_cos, ← sub_div]
  change (kernelEnergy (Sum.elim (copyOrdinate T) (fun _ : Fin 2 => τ)) k -
    kernelEnergy (copyOrdinate T) k) / _ = 4 * (1 + ∑ i : Copies T, k (τ - copyOrdinate T i)) / _
  rw [kernelEnergy_add_two_at_height]
  simp only [hflip, h0]
  ring

/-- An inserted pair is invisible at the leading normalized Fourier scale,
uniformly in frequency and in the insertion height. -/
theorem eventually_formFactorWithTwoAtHeight_sub_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ τ α : ℝ,
      |formFactorWithTwoAtHeight T τ α - formFactor T α| ≤ C / T := by
  obtain ⟨B, hB, hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨8 * Real.pi * (1 + 2 * B), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T hT hlog
  intro τ α
  let w := fun i : Copies T => cauchyWeight (τ - copyOrdinate T i)
  let z := fun i : Copies T => Real.cos ((α * Real.log T) * (τ - copyOrdinate T i))
  let D := T * Real.log T / (2 * Real.pi)
  have hT0 : 0 < T := by linarith only [hT]
  have hL : 0 < Real.log T := zero_lt_one.trans_le hlog
  have hD : 0 < D := div_pos (mul_pos hT0 hL) (by positivity)
  have habs : |∑ i, w i * z i| ≤ ∑ i, w i := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    have hw : 0 ≤ w i := cauchyWeight_nonneg _
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_of_le_one_right hw (Real.abs_cos_le_one _)
  have hlog3 : Real.log (T + 3) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (T ^ 2) := by
        apply Real.log_le_log (by positivity)
        nlinarith only [hT, mul_nonneg hT0.le (sub_nonneg.mpr hT)]
      _ = _ := by norm_num [Real.log_pow]
  have hnorm : |1 + ∑ i, w i * z i| ≤ 1 + B * Real.log (T + 3) := calc
    _ ≤ |(1 : ℝ)| + |∑ i, w i * z i| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_one]
      exact add_le_add le_rfl (habs.trans (hrow T hT0.le τ))
  have hnorm' : |1 + ∑ i, w i * z i| ≤ (1 + 2 * B) * Real.log T := calc
    _ ≤ 1 + B * Real.log (T + 3) := hnorm
    _ ≤ Real.log T + B * (2 * Real.log T) :=
      add_le_add hlog (mul_le_mul_of_nonneg_left hlog3 hB.le)
    _ = _ := by ring
  rw [formFactorWithTwoAtHeight_sub_eq]
  change |4 * (1 + ∑ i, w i * z i) / D| ≤ _
  rw [abs_div, abs_of_pos hD, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ (4 * ((1 + 2 * B) * Real.log T)) / D :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm' (by positivity)) hD.le
    _ = _ := by dsimp [D]; field_simp [hL.ne', hT0.ne', Real.pi_ne_zero]; ring

/-- Add two separately labeled occurrences to a finite ordinate configuration. -/
def appendOrdinatePair {ι : Type*} (t : ι → ℝ) (a b : ℝ) : ι ⊕ Bool → ℝ :=
  Sum.elim t (fun q => cond q a b)

theorem kernelEnergy_appendOrdinatePair {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (a b : ℝ) (k : ℝ → ℝ) :
    kernelEnergy (appendOrdinatePair t a b) k =
      kernelEnergy t k + (∑ i : ι, (k (t i - a) + k (t i - b))) +
      (∑ i : ι, (k (a - t i) + k (b - t i))) + k (a - b) + k (b - a) + 2 * k 0 := by
  classical
  unfold kernelEnergy appendOrdinatePair
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, Sum.elim_inl, Sum.elim_inr,
    cond_true, cond_false, sub_self, Finset.sum_add_distrib]
  ring

/-- Replacing two isolated heights by two distinct labels at one fresh height
changes a localized kernel only through its value at zero. -/
theorem isolated_ordinate_replacement_energy_eq {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (a b c δ : ℝ) (k : ℝ → ℝ)
    (ha : ∀ i, δ ≤ |t i - a|) (hb : ∀ i, δ ≤ |t i - b|)
    (hc : ∀ i, δ ≤ |t i - c|) (hab : δ ≤ |a - b|)
    (hk : ∀ x, δ ≤ |x| → k x = 0) :
    kernelEnergy (appendOrdinatePair t c c) k =
      kernelEnergy (appendOrdinatePair t a b) k + 2 * k 0 := by
  have hflip {x y : ℝ} (h : δ ≤ |x - y|) : δ ≤ |y - x| := by rwa [abs_sub_comm]
  rw [kernelEnergy_appendOrdinatePair, kernelEnergy_appendOrdinatePair]
  simp [fun i => hk _ (ha i), fun i => hk _ (hb i), fun i => hk _ (hc i),
    fun i => hk _ (hflip (ha i)), fun i => hk _ (hflip (hb i)),
    fun i => hk _ (hflip (hc i)), hk _ hab, hk _ (hflip hab)] <;> ring

/-- All strictly positive ordinate-gap counts below the separation scale are
preserved exactly by an isolated reflected-pair replacement. -/
theorem isolated_ordinate_replacement_positive_count_eq {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (a b c δ u : ℝ)
    (ha : ∀ i, δ ≤ |t i - a|) (hb : ∀ i, δ ≤ |t i - b|)
    (hc : ∀ i, δ ≤ |t i - c|) (hab : δ ≤ |a - b|) (hu : u < δ) :
    kernelEnergy (appendOrdinatePair t c c) (fun x => if 0 < x ∧ x ≤ u then 1 else 0) =
      kernelEnergy (appendOrdinatePair t a b) (fun x => if 0 < x ∧ x ≤ u then 1 else 0) := by
  have hk (x : ℝ) (hx : δ ≤ |x|) :
      (if 0 < x ∧ x ≤ u then (1 : ℝ) else 0) = 0 := by
    apply if_neg
    intro h
    rw [abs_of_pos h.1] at hx
    exact (not_lt_of_ge hx) (h.2.trans_lt hu)
  simpa using isolated_ordinate_replacement_energy_eq t a b c δ
    (fun x => if 0 < x ∧ x ≤ u then 1 else 0) ha hb hc hab hk

/-- The same replacement adds exactly two ordered equal-ordinate pairs. -/
theorem isolated_ordinate_replacement_collision_eq {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (a b c δ : ℝ) (hδ : 0 < δ)
    (ha : ∀ i, δ ≤ |t i - a|) (hb : ∀ i, δ ≤ |t i - b|)
    (hc : ∀ i, δ ≤ |t i - c|) (hab : δ ≤ |a - b|) :
    occurrenceCollision (appendOrdinatePair t c c) =
      occurrenceCollision (appendOrdinatePair t a b) + 2 := by
  have hk (x : ℝ) (hx : δ ≤ |x|) : (if x = 0 then (1 : ℝ) else 0) = 0 := by
    exact if_neg (abs_pos.mp (hδ.trans_le hx))
  have he := isolated_ordinate_replacement_energy_eq t a b c δ
    (fun x => if x = 0 then 1 else 0) ha hb hc hab hk
  rw [← occurrenceCollision_cast_eq_kernelEnergy,
    ← occurrenceCollision_cast_eq_kernelEnergy] at he
  have he' : (occurrenceCollision (appendOrdinatePair t c c) : ℝ) =
      (occurrenceCollision (appendOrdinatePair t a b) : ℝ) + 2 := by simpa using he
  exact_mod_cast he'

end RiemannResearch.Analysis.MontgomeryFormFactor
