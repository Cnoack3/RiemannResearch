/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Critical power moments of a two-part defect

Source: the elementary floor-defect estimate in the user-provided Mertens notes.
Summing at the cutoff-dependent transition gives a uniformly bounded absolute
row sum, even though the cutoff-independent harmonic majorant diverges.
-/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

namespace RiemannResearch.Analysis

/-- Summing the actual minimum permits the critical exponents. The real
splitting point `X` avoids a floor error. -/
theorem summable_min_power_row (A B β X : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ : 0 < β) (hβ1 : β < 1) (hX : 1 ≤ X) :
    let f := fun n : ℕ => min (A * ((n : ℝ) + 1) ^ (β - 1))
      (B * ((n : ℝ) + 1) ^ (β - 2))
    Summable f ∧ ∑' n, f n ≤ A * X ^ β / β + B * X ^ (β - 1) / (1 - β) := by
  let f (t : ℝ) := min (A * t ^ (β - 1)) (B * t ^ (β - 2))
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t :=
    le_min (mul_nonneg hA (Real.rpow_nonneg ht _)) (mul_nonneg hB (Real.rpow_nonneg ht _))
  have hf : AntitoneOn f (Ici (1 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    exact min_le_min
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)) hA)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)) hB)
  have hm : Measurable f := by dsimp only [f]; fun_prop
  have fint (y : ℝ) (hy : 0 < y) : IntegrableOn f (Ioi y) := by
    refine ((integrableOn_Ioi_rpow_of_lt (show β - 2 < -1 by linarith) hy).const_mul B).mono'
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos t (hy.trans ht).le)]
    exact min_le_right _ _
  have hcast : 0 < ((1:ℕ):ℝ) := by norm_num
  have hfcast : AntitoneOn f (Ici ((1:ℕ):ℝ)) := by simpa only [Nat.cast_one] using hf
  have hs₀ : Summable (fun n : ℕ => f n) :=
    hfcast.summable_of_integrableOn_Ioi (N := 1) (fint _ hcast)
      (fun t ht => hpos t (hcast.trans ht).le)
  have hs : Summable (fun n : ℕ => f (n + 1 : ℕ)) := (summable_nat_add_iff 1).mpr hs₀
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := f) 1 hfcast
    (fint _ hcast) (fun t ht => hpos t (hcast.trans ht).le)
  have hsum : (∑' n : ℕ, f (n + 1 : ℕ)) ≤ f 1 + ∫ t in Ioi (1 : ℝ), f t := by
    rw [hs.tsum_eq_zero_add]
    simpa only [Nat.zero_add, Nat.cast_one] using add_le_add (le_rfl : f 1 ≤ f 1) htail
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hlower : (∫ t in (1:ℝ)..X, f t) ≤ A * ((X ^ β - 1) / β) := by
    have hi : IntervalIntegrable f volume 1 X :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).2
        ((fint 1 zero_lt_one).mono_set Ioc_subset_Ioi_self)
    have hr : -1 < β-1 := by linarith
    calc
      _ ≤ ∫ t in (1:ℝ)..X, A * t ^ (β-1) :=
        intervalIntegral.integral_mono_on hX hi
          ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul A) (fun _ _ => min_le_left _ _)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr),
          show β-1+1 = β by ring, Real.one_rpow]
  have hupper : (∫ t in Ioi X, f t) ≤ B * (X ^ (β-1) / (1-β)) := by
    have ht : β - 2 < -1 := by linarith
    calc
      _ ≤ ∫ t in Ioi X, B * t ^ (β-2) :=
        setIntegral_mono_on (fint X hX0) ((integrableOn_Ioi_rpow_of_lt ht hX0).const_mul B)
          measurableSet_Ioi (fun _ _ => min_le_right _ _)
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt ht hX0,
          show β-2+1 = β-1 by ring]
        congr 1
        rw [show 1-β = -(β-1) by ring, div_neg, neg_div]
  have hone : f 1 ≤ A := by simpa [f] using
    (min_le_left (A * (1:ℝ)^(β-1)) (B * (1:ℝ)^(β-2)))
  have h := add_le_add hone (add_le_add hlower hupper)
  rw [intervalIntegral.integral_interval_add_Ioi (fint 1 zero_lt_one) (fint X hX0)] at h
  have hgap : A * β ≤ A * 1 := mul_le_mul_of_nonneg_left hβ1.le hA
  have hlow : A + A * ((X ^ β - 1) / β) ≤ A * X ^ β / β := by
    apply (le_div_iff₀ hβ).2
    have hEq : (A + A * ((X ^ β - 1) / β)) * β = A * β + A * (X ^ β - 1) := by
      field_simp [hβ.ne'] <;> ring
    rw [hEq]
    linarith only [hgap]
  have hfinal : (∑' n : ℕ, f (n+1 : ℕ)) ≤ A * X ^ β / β + B * X ^ (β-1) / (1-β) := by
    calc
      _ ≤ A + (A * ((X ^ β - 1) / β) + B * (X ^ (β-1) / (1-β))) := hsum.trans h
      _ = (A + A * ((X ^ β - 1) / β)) + B * X ^ (β-1) / (1-β) := by ring
      _ ≤ _ := add_le_add hlow le_rfl
  simpa only [f, Nat.cast_add, Nat.cast_one] using And.intro hs hfinal

/-- If the two estimates balance at `N^(1+a)`, the row has a uniform critical
norm. The equation for `β` is equivalent to `β = a / (1+a)` when `a>0`. -/
theorem critical_power_kernel_bound (N a β : ℝ) (hN : 1 ≤ N) (ha : 0 < a)
    (hβ : 0 < β) (hβ1 : β < 1) (hcrit : (1 + a) * β = a) :
    let F := fun n : ℕ => min (N ^ (-a) * ((n : ℝ) + 1) ^ (β-1))
      (N * ((n : ℝ)+1) ^ (β-2))
    Summable F ∧ ∑' n, F n ≤ 1 / β + 1 / (1 - β) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hX : 1 ≤ N ^ (1 + a) := Real.one_le_rpow hN (by linarith)
  obtain ⟨hs, hb⟩ := summable_min_power_row (N^(-a)) N β (N^(1+a))
    (Real.rpow_nonneg hN0.le _) hN0.le hβ hβ1 hX
  have h1 : N ^ (-a) * (N ^ (1+a)) ^ β = 1 := by
    rw [← Real.rpow_mul hN0.le, hcrit, ← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero]
  have h2 : N * (N ^ (1+a)) ^ (β-1) = 1 := by
    rw [← Real.rpow_mul hN0.le, show (1+a)*(β-1) = -1 by linarith only [hcrit],
      Real.rpow_neg hN0.le, Real.rpow_one, mul_inv_cancel₀ hN0.ne']
  rw [h1, h2] at hb
  exact ⟨hs, hb⟩

end RiemannResearch.Analysis
