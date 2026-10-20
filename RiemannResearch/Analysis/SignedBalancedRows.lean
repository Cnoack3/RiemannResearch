/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sharp coefficient variation of balanced signed rows

Source: the user-provided Two_Prime_Mellin_Parity_Handoff_2026-10-20,
Section 7, for the signed mass-one and drift-zero constraints. The finite
inequality below strengthens the negative-weight consequence to an optimal
total-variation bound. It does not assert any Hilbert norm bound.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.SignedBalancedRows

/-- Exact finite slack identity, before imposing either balance constraint
or an interval restriction on the slopes. -/
theorem totalVariation_slack_identity {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ) :
    (a - b) * (∑ i ∈ S, |w i|) -
        (a + b) * (∑ i ∈ S, w i) +
        2 * (∑ i ∈ S, w i * slope i) =
      ∑ i ∈ S, ((|w i| + w i) * (slope i - b) +
        (|w i| - w i) * (a - slope i)) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- For a balanced row the excess variation is exactly the signed endpoint
slack. This equality retains the information discarded by the lower bound. -/
theorem totalVariation_gap_exact {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0) :
    (a - b) * (∑ i ∈ S, |w i|) - (a + b) =
      ∑ i ∈ S, ((|w i| + w i) * (slope i - b) +
        (|w i| - w i) * (a - slope i)) := by
  simpa only [hmass, hbal, mul_one, mul_zero, add_zero] using
    totalVariation_slack_identity S w slope a b

/-- Each endpoint-slack summand is nonnegative when its slope is in the interval. -/
theorem totalVariation_slack_nonneg {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a) :
    0 ≤ ∑ i ∈ S, ((|w i| + w i) * (slope i - b) +
      (|w i| - w i) * (a - slope i)) := by
  apply Finset.sum_nonneg
  intro i hi
  have hplus : 0 ≤ |w i| + w i := by linarith [neg_abs_le (w i)]
  have hminus : 0 ≤ |w i| - w i := sub_nonneg.mpr (le_abs_self (w i))
  exact add_nonneg
    (mul_nonneg hplus (sub_nonneg.mpr (hlo i hi)))
    (mul_nonneg hminus (sub_nonneg.mpr (hhi i hi)))

/-- A signed row with mass one and zero moment must pay for the width of
the interval containing its positive slopes. No positivity assumptions are
needed for this undivided finite algebraic inequality. -/
theorem totalVariation_gap {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0) :
    a + b ≤ (a - b) * (∑ i ∈ S, |w i|) := by
  have he := totalVariation_gap_exact S w slope a b hmass hbal
  have hs := totalVariation_slack_nonneg S w slope a b hlo hhi
  linarith

/-- The exact minimum possible variation for slopes in a fixed positive interval. -/
theorem totalVariation_lower {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ) (hba : b < a)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0) :
    (a + b) / (a - b) ≤ ∑ i ∈ S, |w i| := by
  apply (div_le_iff₀ (sub_pos.mpr hba)).mpr
  simpa only [mul_comm] using totalVariation_gap S w slope a b hlo hhi hmass hbal

/-- Bounded variation prevents all slopes from approaching the same positive
value relative to their maximum. -/
theorem slope_ratio_le_of_totalVariation_le {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b M : ℝ)
    (ha : 0 < a) (hba : b < a) (hM : 0 ≤ M)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0)
    (hvar : ∑ i ∈ S, |w i| ≤ M) :
    b / a ≤ (M - 1) / (M + 1) := by
  have hgap := totalVariation_gap S w slope a b hlo hhi hmass hbal
  have hbound := mul_le_mul_of_nonneg_left hvar (sub_pos.mpr hba).le
  apply (div_le_div_iff₀ ha (by linarith : 0 < M + 1)).mpr
  nlinarith

/-- The endpoint pair has mass one. -/
theorem endpoint_mass (a b : ℝ) (hba : b < a) :
    -b / (a - b) + a / (a - b) = 1 := by
  field_simp [ne_of_gt (sub_pos.mpr hba)]
  ring

/-- The endpoint pair exactly cancels the positive slopes. -/
theorem endpoint_moment (a b : ℝ) :
    (-b / (a - b)) * a + (a / (a - b)) * b = 0 := by
  ring

/-- Sharpness: the two endpoint weights attain the lower variation bound. -/
theorem endpoint_totalVariation (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    |-b / (a - b)| + |a / (a - b)| = (a + b) / (a - b) := by
  have hg : 0 < a - b := sub_pos.mpr hba
  have ha : 0 < a := hb.trans hba
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hg.le),
    abs_of_nonneg (div_nonneg ha.le hg.le)]
  ring


theorem transport_determinant_exact {ι : Type*}
    (S : Finset ι) (u v a f : ι → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, u i * v j * (a i * f j - a j * f i)) =
      (∑ i ∈ S, u i * a i) * (∑ j ∈ S, v j * f j) -
      (∑ i ∈ S, u i * f i) * (∑ j ∈ S, v j * a j) := by
  have he (i j : ι) : u i * v j * (a i * f j - a j * f i) =
      (u i * a i) * (v j * f j) - (u i * f i) * (v j * a j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

theorem transport_mass_exact {ι : Type*}
    (S : Finset ι) (u v a : ι → ℝ)
    (hmass : (∑ i ∈ S, v i) - (∑ i ∈ S, u i) = 1)
    (hbal : (∑ i ∈ S, u i * a i) = (∑ i ∈ S, v i * a i)) :
    (∑ i ∈ S, ∑ j ∈ S, u i * v j * (a i - a j)) =
      ∑ i ∈ S, u i * a i := by
  have he := transport_determinant_exact S u v a (fun _ => 1)
  simp only [mul_one] at he
  rw [he, ← hbal]
  calc
    _ = (∑ i ∈ S, u i * a i) *
        ((∑ i ∈ S, v i) - (∑ i ∈ S, u i)) := by ring
    _ = _ := by rw [hmass, mul_one]

/-- A finite balanced signed row inherits a uniform determinant bound.
The factorization keeps plateau pairs and never divides by a slope gap. -/
theorem transport_probe_bound {ι : Type*}
    (S : Finset ι) (u v a f : ι → ℝ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hmass : (∑ i ∈ S, v i) - (∑ i ∈ S, u i) = 1)
    (hbal : (∑ i ∈ S, u i * a i) = (∑ i ∈ S, v i * a i))
    (ht : 0 < ∑ i ∈ S, u i * a i)
    (ε : ℝ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, 0 < u i → 0 < v j →
      |a i * f j - a j * f i| ≤ ε * (a i - a j)) :
    |(∑ j ∈ S, v j * f j) - (∑ i ∈ S, u i * f i)| ≤ ε := by
  have hb : |∑ i ∈ S, ∑ j ∈ S, u i * v j * (a i * f j - a j * f i)| ≤
      ε * (∑ i ∈ S, ∑ j ∈ S, u i * v j * (a i - a j)) := by
    calc
      _ ≤ ∑ i ∈ S, |∑ j ∈ S, u i * v j * (a i * f j - a j * f i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, |u i * v j * (a i * f j - a j * f i)| := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, ε * (u i * v j * (a i - a j)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hui : u i = 0
        · simp [hui]
        by_cases hvj : v j = 0
        · simp [hvj]
        have hp := hpair i hi j hj (lt_of_le_of_ne (hu i hi) (Ne.symm hui))
          (lt_of_le_of_ne (hv j hj) (Ne.symm hvj))
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hu i hi) (hv j hj))]
        nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (hu i hi) (hv j hj))]
      _ = _ := by simp_rw [Finset.mul_sum]
  rw [transport_determinant_exact, ← hbal,
    show (∑ i ∈ S, u i * a i) * (∑ j ∈ S, v j * f j) -
      (∑ i ∈ S, u i * f i) * (∑ i ∈ S, u i * a i) =
      (∑ i ∈ S, u i * a i) *
        ((∑ j ∈ S, v j * f j) - (∑ i ∈ S, u i * f i)) by ring,
    abs_mul, abs_of_pos ht, transport_mass_exact S u v a hmass hbal] at hb
  nlinarith

/-- Apply transport to the positive and negative parts of a mass-one row. -/
theorem signed_probe_bound {ι : Type*}
    (S : Finset ι) (w a f : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * a i = 0)
    (ε : ℝ)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, w i < 0 → 0 < w j →
      |a i * f j - a j * f i| ≤ ε * (a i - a j)) :
    |∑ i ∈ S, w i * f i| ≤ ε := by
  let u : ι → ℝ := fun i => max (-w i) 0
  let v : ι → ℝ := fun i => max (w i) 0
  have hu : ∀ i ∈ S, 0 ≤ u i := fun i _ => le_max_right _ _
  have hv : ∀ i ∈ S, 0 ≤ v i := fun i _ => le_max_right _ _
  have hw (i : ι) : v i - u i = w i := by
    dsimp [u, v]
    by_cases h : 0 ≤ w i
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · have hh : w i ≤ 0 := (lt_of_not_ge h).le
      rw [max_eq_right hh, max_eq_left (neg_nonneg.mpr hh)]
      ring
  have hsum (g : ι → ℝ) :
      (∑ i ∈ S, v i * g i) - (∑ i ∈ S, u i * g i) =
      ∑ i ∈ S, w i * g i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← sub_mul, hw]
  have hm : (∑ i ∈ S, v i) - (∑ i ∈ S, u i) = 1 := by
    simpa only [mul_one, hmass] using hsum (fun _ => 1)
  have hb : (∑ i ∈ S, u i * a i) = (∑ i ∈ S, v i * a i) := by
    have hh := hsum a
    rw [hbal] at hh
    linarith
  have ht : 0 < ∑ i ∈ S, u i * a i := by
    have hn : 0 ≤ ∑ i ∈ S, u i * a i := Finset.sum_nonneg
      (fun i hi => mul_nonneg (hu i hi) (ha i hi).le)
    by_contra h
    have hz : ∑ i ∈ S, u i * a i = 0 := le_antisymm (le_of_not_gt h) hn
    have hvzero : ∀ i ∈ S, v i = 0 := by
      intro i hi
      have hle := Finset.single_le_sum
        (fun j hj => mul_nonneg (hv j hj) (ha j hj).le) hi
      rw [← hb, hz] at hle
      nlinarith [hv i hi, ha i hi]
    have hvsum : ∑ i ∈ S, v i = 0 := Finset.sum_eq_zero hvzero
    have husum : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg hu
    linarith
  have hh := transport_probe_bound S u v a f hu hv hm hb ht ε
    (fun i hi j hj hui hvj => hpair i hi j hj
      (by dsimp [u] at hui; have hh := (lt_max_iff.mp hui).resolve_right (lt_irrefl 0); linarith)
      (by dsimp [v] at hvj; exact (lt_max_iff.mp hvj).resolve_right (lt_irrefl 0)))
  rwa [hsum] at hh


/-- A mass-one, zero-moment row cannot put all positive coefficients at
slopes at least as large as all negative coefficients. -/
theorem not_balanced_of_reversed_slopes {ι : Type*}
    (S : Finset ι) (w a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * a i = 0)
    (horder : ∀ i ∈ S, ∀ j ∈ S, w i < 0 → 0 < w j → a i ≤ a j) :
    False := by
  have hh := signed_probe_bound S w a (fun _ => 1) ha hmass hbal (-1)
    (by
      intro i hi j hj hwi hwj
      simp only [mul_one]
      rw [abs_of_nonpos (sub_nonpos.mpr (horder i hi j hj hwi hwj))]
      ring_nf
      exact le_rfl)
  simp only [mul_one, hmass, abs_one] at hh
  norm_num at hh

end RiemannResearch.Analysis.SignedBalancedRows
