/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

/-!
# Finite strict-tail layer cake

The exact finite identity retains both endpoints and uses the strict bad
condition `δ < x i`. Replacing a strict indicator by an inclusive indicator
inside the integral changes only a Lebesgue-null singleton.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteStrictTail

variable {ι : Type*}

def tail (s : Finset ι) (x : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if t < x i then 1 else 0

def badSum (s : Finset ι) (x : ι → ℝ) (φ : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∑ i ∈ s, if δ < x i then φ (x i) else 0

theorem intervalIntegrable_strict_cut (f : ℝ → ℝ) (hf : Continuous f)
    (δ M x : ℝ) :
    IntervalIntegrable (fun t => if t < x then f t else 0) volume δ M := by
  have h := (hf.intervalIntegrable (μ := volume) δ M).def'.indicator
    (t := Set.Iio x) measurableSet_Iio
  have heq : (fun t => if t < x then f t else 0) = (Set.Iio x).indicator f := by
    funext t
    by_cases ht : t < x <;> simp [ht]
  rw [heq]
  exact intervalIntegrable_iff.mpr h

/-- A single copy contributes only over its strict sublevel interval. Changing
the endpoint indicator from `<` to `≤` changes a null singleton only. -/
theorem integral_strict_cut (φ f : ℝ → ℝ) (hf : Continuous f)
    (hderiv : ∀ t, HasDerivAt φ (f t) t)
    (δ M x : ℝ) (hδM : δ ≤ M) (hxM : x ≤ M) :
    (∫ t in δ..M, if t < x then f t else 0) =
      if δ < x then φ x - φ δ else 0 := by
  by_cases hx : δ < x
  · rw [if_pos hx]
    calc
      _ = ∫ t in δ..M, Set.indicator {t : ℝ | t ≤ x} f t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne x] with t ht hmem
        have hlt : t < x ↔ t ≤ x :=
          ⟨le_of_lt, fun h => lt_of_le_of_ne h ht⟩
        by_cases htx : t < x
        · simp only [Set.indicator, Set.mem_ofPred_eq, if_pos htx,
            if_pos (hlt.mp htx)]
        · simp only [Set.indicator, Set.mem_ofPred_eq, if_neg htx,
            if_neg (fun h => htx (hlt.mpr h))]
      _ = ∫ t in δ..x, f t :=
        intervalIntegral.integral_indicator (f := f) ⟨hx.le, hxM⟩
      _ = φ x - φ δ :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hderiv t) (hf.intervalIntegrable δ x)
  · rw [if_neg hx]
    have hxδ : x ≤ δ := le_of_not_gt hx
    calc
      _ = ∫ _t in δ..M, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hδM
        intro t ht
        simp only [if_neg (not_lt.mpr (hxδ.trans ht.1.le))]
      _ = 0 := by simp

theorem intervalIntegrable_tail_mul (s : Finset ι) (x : ι → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) (δ M : ℝ) :
    IntervalIntegrable (fun t => tail s x t * f t) volume δ M := by
  have heq : (fun t => tail s x t * f t) =
      (fun t => ∑ i ∈ s, if t < x i then f t else 0) := by
    funext t
    simp only [tail, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [heq]
  apply intervalIntegrable_iff.mpr
  exact integrable_finsetSum s (fun i _ =>
    (intervalIntegrable_strict_cut f hf δ M (x i)).def')

/-- Exact finite layer cake, with both finite-height endpoints retained. -/
theorem layerCake (s : Finset ι) (x : ι → ℝ) (φ f : ℝ → ℝ)
    (hf : Continuous f) (hderiv : ∀ t, HasDerivAt φ (f t) t)
    (δ M : ℝ) (hδM : δ ≤ M) (hxM : ∀ i ∈ s, x i ≤ M) :
    badSum s x φ δ = φ δ * tail s x δ +
      ∫ t in δ..M, tail s x t * f t := by
  classical
  have heq : (fun t => tail s x t * f t) =
      (fun t => ∑ i ∈ s, if t < x i then f t else 0) := by
    funext t
    simp only [tail, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  have hint : (∫ t in δ..M, tail s x t * f t) =
      ∑ i ∈ s, if δ < x i then φ (x i) - φ δ else 0 := by
    rw [heq, intervalIntegral.integral_finsetSum
      (fun i _ => intervalIntegrable_strict_cut f hf δ M (x i))]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_strict_cut φ f hf hderiv δ M (x i) hδM (hxM i hi)
  rw [hint]
  unfold badSum tail
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

theorem tail_nonneg (s : Finset ι) (x : ι → ℝ) (t : ℝ) :
    0 ≤ tail s x t := by
  exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem tail_le_card (s : Finset ι) (x : ι → ℝ) (t : ℝ) :
    tail s x t ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ _i ∈ s, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => by split_ifs <;> norm_num)
    _ = _ := by simp

end RiemannResearch.Analysis.FiniteStrictTail
