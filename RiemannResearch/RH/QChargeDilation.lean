/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDifferenceLimits
import RiemannResearch.RH.QDisplacementTranslationCarry
import RiemannResearch.RH.QSquarefreeResponsePhysicalTail
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.FieldSimp

/-! # Finite dilations and one-sided Möbius charges

The nonnegative floor remainder is smaller than the dilation. Comparing
physical values at n and tn thus needs only one side of the charges. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QChargeDilation
open Pareto ZetaTwoHilbert QDisplacementTranslationCarry ArithmeticCumulative

theorem dilation_floor_split (t n m : ℕ) (hm : 0 < m) :
    (t * n) / m = t * (n / m) + (t * (n % m)) / m := by
  have he : t * n = t * (n % m) + m * (t * (n / m)) := by
    calc
      t * n = t * (n % m + m * (n / m)) := congrArg (t * ·) (Nat.mod_add_div n m).symm
      _ = _ := by ring
  rw [he, Nat.add_mul_div_left _ _ hm, Nat.add_comm]

theorem finite_dilation (f : ℕ → ℝ) (hf : f 0 = 0) (t n : ℕ) (ht : 0 < t) :
    f (t * n) = (t : ℝ) * f n +
      ∑ m ∈ Finset.Icc 1 (t * n), mobiusDifference m f * ((t * (n % m) / m : ℕ) : ℝ) := by
  have hn : n ≤ t * n := by
    simpa using Nat.mul_le_mul_right n (show 1 ≤ t by omega)
  rw [finite_floor_reconstruction f hf (t * n) (t * n) le_rfl,
    finite_floor_reconstruction f hf (t * n) n hn, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dilation_floor_split t n m (Finset.mem_Icc.mp hm).1]
  push_cast
  ring

/-- Taking sigma = 1 uses only negative charges, and sigma = -1 only positive charges. -/
theorem oneSided_le_of_charge_rows (f : QHilbert) (σ C : ℝ) (n : ℕ)
    (hC : ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H,
      max (-(σ * mobiusDifference m (qSequence f))) 0 * residueFraction m n) ≤ C) :
    σ * qSequence f n ≤ C := by
  have hc : 0 ≤ C := by simpa using hC 0
  by_cases hn : n = 0
  · simpa [hn, qSequence_zero] using hc
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hcof : Tendsto (fun t : ℕ => t * n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    apply eventually_atTop.2
    refine ⟨b, fun t ht => ht.trans ?_⟩
    simpa using Nat.mul_le_mul_left t hn0
  have hlim : Tendsto (fun t : ℕ => qSequence f (t * n) / (t : ℝ)) atTop (𝓝 0) := by
    have h := ((qSequence_div_nat_tendsto_zero f).comp hcof).mul_const (n : ℝ)
    rw [zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
    change qSequence f (t * n) / ((t * n : ℕ) : ℝ) * n = _
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    rw [Nat.cast_mul]
    field_simp [hnR, htR]
  have lim := (hlim.const_mul σ).add_const C
  rw [mul_zero, zero_add] at lim
  apply ge_of_tendsto lim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
  let b := fun m => mobiusDifference m (qSequence f)
  let e := fun m => ((t * (n % m) / m : ℕ) : ℝ)
  let s := Finset.Icc 1 (t * n)
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hbudget : (∑ m ∈ s, -(σ * b m) * e m) ≤ (t : ℝ) * C := by
    calc
      _ ≤ ∑ m ∈ s, (t : ℝ) * (max (-(σ * b m)) 0 * residueFraction m n) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
        have he : e m ≤ (t : ℝ) * residueFraction m n := by
          change ((t * (n % m) / m : ℕ) : ℝ) ≤ (t : ℝ) * (((n % m : ℕ) : ℝ) / (m : ℝ))
          rw [← mul_div_assoc]
          apply (le_div_iff₀ hmR).mpr
          exact_mod_cast Nat.div_mul_le_self (t * (n % m)) m
        calc
          _ ≤ max (-(σ * b m)) 0 * ((t : ℝ) * residueFraction m n) :=
            mul_le_mul (le_max_left _ _) he (Nat.cast_nonneg _) (le_max_right _ _)
          _ = _ := by ring
      _ = (t : ℝ) * ∑ m ∈ s, max (-(σ * b m)) 0 * residueFraction m n :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC (t * n)) htR.le
  have heq : qSequence f (t * n) =
      (t : ℝ) * qSequence f n + ∑ m ∈ s, b m * e m :=
    finite_dilation _ (qSequence_zero _) t n (by omega)
  have hrewrite : (∑ m ∈ s, -(σ * b m) * e m) =
      -σ * ∑ m ∈ s, b m * e m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hsum : (∑ m ∈ s, b m * e m) = qSequence f (t * n) - (t : ℝ) * qSequence f n := by
    linarith only [heq]
  rw [hrewrite, hsum] at hbudget
  change σ * qSequence f n ≤ σ * (qSequence f (t * n) / (t : ℝ)) + C
  calc
    _ ≤ (σ * qSequence f (t * n) + (t : ℝ) * C) / (t : ℝ) :=
      (le_div_iff₀ htR).mpr (by nlinarith only [hbudget])
    _ = _ := by field_simp [htR.ne']

/-- Bounding the unweighted one-sided charge prefixes gives a single
one-sided bound at all physical sites. -/
theorem oneSided_le_of_charge_prefix (f : QHilbert) (σ C : ℝ)
    (hC : ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H,
      max (-(σ * mobiusDifference m (qSequence f))) 0) ≤ C) (n : ℕ) :
    σ * qSequence f n ≤ C := by
  apply oneSided_le_of_charge_rows f σ C n
  intro H
  apply le_trans _ (hC H)
  apply Finset.sum_le_sum
  intro m hm
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  apply mul_le_of_le_one_right (le_max_right _ _)
  change ((n % m : ℕ) : ℝ) / (m : ℝ) ≤ 1
  rw [div_le_iff₀ hmR, one_mul]
  exact_mod_cast (Nat.mod_lt n hm0).le

/-- A uniform bound on the negative or positive Möbius charges of the actual
displacement suffices for RH. -/
theorem riemannHypothesis_of_one_sided_charges (σ C : ℝ) (hσ : |σ| = 1)
    (hC : ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H,
      max (-(σ * mobiusDifference m (qSequence QSquarefreeDisplacementRigidity.displacement))) 0) ≤ C) :
    RiemannHypothesis := by
  apply QSquarefreeDisplacementRigidity.riemannHypothesis_of_one_sided_bounded_displacement σ C hσ
    (by simpa using hC 0)
  exact oneSided_le_of_charge_prefix _ σ C hC

open QSquarefreeDisplacementRigidity ArithmeticCumulative

/-- At each good physical cutoff the sign and the nonnegative row majorant
may both vary. The complete signed-charge condition is needed only at the
finitely many physical sites in that prefix. -/
theorem riemannHypothesis_of_cofinal_charge_row_harmonic (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : ∃ᶠ X : ℕ in atTop, ∃ (σ : ℝ) (u : ℕ → ℝ), |σ| = 1 ∧
      (∀ n ≤ X, 0 ≤ u n) ∧
      (∀ n ≤ X, ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H,
        max (-(σ * mobiusDifference m (qSequence displacement))) 0 * residueFraction m n) ≤ u n) ∧
      (∑ n ∈ Finset.range (X + 1), u n / (n : ℝ)) ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_harmonic_polylog B C hB hC
  apply h.mono
  rintro X ⟨σ, u, hσ, hu, hr, hs⟩
  have hmin : minimumHarmonicPrefix X ≤ harmonicSide σ X := by
    rcases le_total 0 σ with hh | hh
    · have he : σ = 1 := (abs_of_nonneg hh).symm.trans hσ
      rw [he]
      exact min_le_left _ _
    · rw [abs_of_nonpos hh] at hσ
      have he : σ = -1 := by linarith
      rw [he]
      exact min_le_right _ _
  apply hmin.trans (le_trans _ hs)
  apply Finset.sum_le_sum
  intro n hn
  have hn' : n ≤ X := by have := Finset.mem_range.mp hn; omega
  exact div_le_div_of_nonneg_right
    (max_le (oneSided_le_of_charge_rows displacement σ (u n) n (hr n hn')) (hu n hn'))
    (Nat.cast_nonneg n)

/-- Either sign of the charges may have finite mass after subtracting a
constant's Möbius profile. The bound on the displacement shifts by |σc|. -/
theorem riemannHypothesis_of_shifted_one_sided_charges (c σ C : ℝ) (hσ : |σ| = 1)
    (hC : ∀ H : ℕ, (∑ m ∈ Finset.Icc 1 H, max (-(σ *
      (mobiusDifference m (qSequence displacement) - c * (ArithmeticFunction.moebius m : ℝ)))) 0)
        ≤ C) : RiemannHypothesis := by
  let f : QHilbert := displacement - c • qOne
  have hf : qSequence f = fun n => qSequence displacement n - c * qOneSequence n := by
    funext n
    change qSequenceLinear (displacement - c • qOne) n = _
    rw [map_sub, map_smul]
    change qSequence displacement n - c * qSequence qOne n = _
    rw [qSequence_qOne]
  have hmone (m : ℕ) (hm : 0 < m) :
      mobiusDifference m qOneSequence = (ArithmeticFunction.moebius m : ℝ) := by
    have h := charges_of_constant_on_positives qOneSequence (by simp [qOneSequence])
      (fun n hn => by simp [qOneSequence, Nat.ne_of_gt hn]) m hm
    simpa only [qOneSequence, one_ne_zero, if_false, one_mul] using h
  have hb (m : ℕ) (hm : 0 < m) :
      mobiusDifference m (qSequence f) =
        mobiusDifference m (qSequence displacement) - c * (ArithmeticFunction.moebius m : ℝ) := by
    rw [hf, mobiusDifference_sub_fn, mobiusDifference_const_mul_fn, hmone m hm]
  have bound := oneSided_le_of_charge_prefix f σ C (fun H => by
    apply le_trans _ (hC H)
    apply Finset.sum_le_sum
    intro m hm
    rw [hb m (Finset.mem_Icc.mp hm).1])
  have hC0 : 0 ≤ C := by simpa using hC 0
  apply riemannHypothesis_of_one_sided_bounded_displacement σ (C + |σ * c|) hσ
    (add_nonneg hC0 (abs_nonneg _))
  intro n
  by_cases hn : n = 0
  · simpa only [hn, qSequence_zero, mul_zero] using add_nonneg hC0 (abs_nonneg (σ * c))
  · have h := bound n
    rw [hf] at h
    simp only [qOneSequence, if_neg hn, mul_one, mul_sub] at h
    linarith [le_abs_self (σ * c)]

end RiemannResearch.RH.QChargeDilation
