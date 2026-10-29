/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.WeightedConstraintEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete weighted energy for disjoint shared-site families

Source: user-provided multi-fiber argument, 29 October 2026.
This module supplies the physical-support assembly required by
`WeightedConstraintEnergy.shared_family_completion`. The exact identity keeps
every omitted coordinate and every completed-square remainder.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.WeightedSharedFamilyEnergy
open WeightedConstraintEnergy

def tailPair (m : ℕ) : Finset ℕ := {m - 1, m}

def familySites (d : ℕ) (T : Finset ℕ) : Finset ℕ :=
  insert d ((Finset.Ico 1 d) ∪ T.biUnion tailPair)

def Separated (T : Finset ℕ) : Prop :=
  ∀ m ∈ T, ∀ n ∈ T, m ≠ n → Disjoint (tailPair m) (tailPair n)

theorem sum_familySites (f : ℕ → ℝ) {d : ℕ} {T : Finset ℕ}
    (ht : ∀ m ∈ T, d + 1 < m) (hs : Separated T) :
    (∑ n ∈ familySites d T, f n) =
      (∑ n ∈ Finset.Ico 1 d, f n) + f d +
        ∑ m ∈ T, (f (m - 1) + f m) := by
  have hd : d ∉ (Finset.Ico 1 d) ∪ T.biUnion tailPair := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := (Finset.mem_Ico.mp h).2
      omega
    · obtain ⟨m, hm, h⟩ := Finset.mem_biUnion.mp h
      have := ht m hm
      simp only [tailPair, Finset.mem_insert, Finset.mem_singleton] at h
      omega
  have hh : Disjoint (Finset.Ico 1 d) (T.biUnion tailPair) := by
    apply Finset.disjoint_left.mpr
    intro n hn ht'
    obtain ⟨m, hm, hn'⟩ := Finset.mem_biUnion.mp ht'
    have := ht m hm
    have := (Finset.mem_Ico.mp hn).2
    simp only [tailPair, Finset.mem_insert, Finset.mem_singleton] at hn'
    omega
  have hp : (∑ n ∈ T.biUnion tailPair, f n) =
      ∑ m ∈ T, (f (m - 1) + f m) := by
    rw [Finset.sum_biUnion hs]
    apply Finset.sum_congr rfl
    intro m hm
    have hne : m - 1 ≠ m := by have := ht m hm; omega
    simp [tailPair, hne]
  rw [familySites, Finset.sum_insert hd, Finset.sum_union hh, hp]
  ring

def familyConductance (a : ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∑ m ∈ T, 1 / (a (m - 1) + a m)

def familyRemainder (a f : ℕ → ℝ) (d : ℕ) (T : Finset ℕ) : ℝ :=
  (1 / a d + familyConductance a T) *
      (f d - a d * familyConductance a T / (1 + a d * familyConductance a T)) ^ 2 +
    ∑ m ∈ T,
      ((f (m - 1) - a (m - 1) * (1 - f d) / (a (m - 1) + a m)) ^ 2 /
        a (m - 1) +
       (f m + a m * (1 - f d) / (a (m - 1) + a m)) ^ 2 / a m)

def familyOmittedEnergy (a f : ℕ → ℝ) (d : ℕ) (T : Finset ℕ) : ℝ :=
  ∑' n : {n : ℕ // n ∉ familySites d T}, f n ^ 2 / a n

theorem familyConductance_nonneg (a : ℕ → ℝ) (T : Finset ℕ)
    (ha : ∀ n, 0 ≤ a n) : 0 ≤ familyConductance a T := by
  unfold familyConductance
  exact Finset.sum_nonneg (fun m _ => div_nonneg (by norm_num) (add_nonneg (ha _) (ha _)))

theorem familyRemainder_nonneg (a f : ℕ → ℝ) (d : ℕ) (T : Finset ℕ)
    (ha : ∀ n, 0 ≤ a n) : 0 ≤ familyRemainder a f d T := by
  unfold familyRemainder
  apply add_nonneg
  · exact mul_nonneg (add_nonneg (div_nonneg (by norm_num) (ha _))
      (familyConductance_nonneg a T ha)) (sq_nonneg _)
  · exact Finset.sum_nonneg (fun m _ => add_nonneg
      (div_nonneg (sq_nonneg _) (ha _)) (div_nonneg (sq_nonneg _) (ha _)))

theorem familyOmittedEnergy_nonneg (a f : ℕ → ℝ) (d : ℕ) (T : Finset ℕ)
    (ha : ∀ n, 0 ≤ a n) : 0 ≤ familyOmittedEnergy a f d T :=
  tsum_nonneg (fun n => div_nonneg (sq_nonneg _) (ha n))

/-- Each fresh positive pair strictly improves the shared-site correction;
the shared physical coordinate is counted only once. -/
theorem family_correction_insert_strict (a : ℕ → ℝ) (d : ℕ) (T : Finset ℕ)
    {m : ℕ} (hm : m ∉ T) (ha : ∀ n, 0 ≤ a n)
    (hp : 0 < a (m - 1) + a m) :
    familyConductance a T / (1 + a d * familyConductance a T) <
      familyConductance a (insert m T) / (1 + a d * familyConductance a (insert m T)) := by
  apply schur_correction_strict_mono (a d) _ _ (ha d)
    (familyConductance_nonneg a T ha)
  unfold familyConductance
  rw [Finset.sum_insert hm]
  have hpos : 0 < 1 / (a (m - 1) + a m) := one_div_pos.mpr hp
  linarith

theorem complete_family_split (a f : ℕ → ℝ) {d : ℕ} {T : Finset ℕ}
    (ht : ∀ m ∈ T, d + 1 < m) (hs : Separated T)
    (hf : Summable (fun n => f n ^ 2 / a n))
    (hh : ∀ n, 0 < n → n < d → f n = 1) :
    (∑' n, f n ^ 2 / a n) =
      (∑ n ∈ Finset.Ico 1 d, 1 / a n) + f d ^ 2 / a d +
      (∑ m ∈ T, (f (m - 1) ^ 2 / a (m - 1) + f m ^ 2 / a m)) +
      familyOmittedEnergy a f d T := by
  have hhead : (∑ n ∈ Finset.Ico 1 d, f n ^ 2 / a n) =
      ∑ n ∈ Finset.Ico 1 d, 1 / a n := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnd⟩ := Finset.mem_Ico.mp hn
    rw [hh n (by omega) hnd, one_pow]
  calc
    _ = (∑ n ∈ familySites d T, f n ^ 2 / a n) +
        familyOmittedEnergy a f d T :=
      (hf.sum_add_tsum_subtype_compl (familySites d T)).symm
    _ = _ := by rw [sum_familySites _ ht hs, hhead]

/-- Complete energy equals the head plus the shared-site correction, all
square remainders, and the entire infinite complementary series. -/
theorem complete_family_completion (a f : ℕ → ℝ) {d : ℕ} {T : Finset ℕ}
    (ht : ∀ m ∈ T, d + 1 < m) (hs : Separated T)
    (hf : Summable (fun n => f n ^ 2 / a n))
    (hh : ∀ n, 0 < n → n < d → f n = 1)
    (ha : ∀ n, 0 ≤ a n) (had : 0 < a d)
    (hap : ∀ m ∈ T, 0 < a (m - 1) ∧ 0 < a m)
    (hr : ∀ m ∈ T, f d + f (m - 1) - f m = 1) :
    (∑' n, f n ^ 2 / a n) =
      (∑ n ∈ Finset.Ico 1 d, 1 / a n) +
      familyConductance a T / (1 + a d * familyConductance a T) +
      familyRemainder a f d T + familyOmittedEnergy a f d T := by
  have hS := familyConductance_nonneg a T ha
  have hD : 1 + a d * familyConductance a T ≠ 0 := by positivity
  have h := shared_family_completion T (a d) (f d)
    (fun m => a (m - 1)) a (fun m => f (m - 1)) f had.ne'
    (fun m hm => (hap m hm).1.ne') (fun m hm => (hap m hm).2.ne')
    (fun m hm => (add_pos (hap m hm).1 (hap m hm).2).ne') hr hD
  rw [complete_family_split a f ht hs hf hh]
  rw [add_assoc] at h
  change f d ^ 2 / a d + _ =
    familyConductance a T / (1 + a d * familyConductance a T) +
    familyRemainder a f d T at h
  linarith

theorem complete_family_lower_bound (a f : ℕ → ℝ) {d : ℕ} {T : Finset ℕ}
    (ht : ∀ m ∈ T, d + 1 < m) (hs : Separated T)
    (hf : Summable (fun n => f n ^ 2 / a n))
    (hh : ∀ n, 0 < n → n < d → f n = 1)
    (ha : ∀ n, 0 ≤ a n) (had : 0 < a d)
    (hap : ∀ m ∈ T, 0 < a (m - 1) ∧ 0 < a m)
    (hr : ∀ m ∈ T, f d + f (m - 1) - f m = 1) :
    (∑ n ∈ Finset.Ico 1 d, 1 / a n) +
      familyConductance a T / (1 + a d * familyConductance a T) ≤
        ∑' n, f n ^ 2 / a n := by
  rw [complete_family_completion a f ht hs hf hh ha had hap hr]
  have hR := familyRemainder_nonneg a f d T ha
  have hO := familyOmittedEnergy_nonneg a f d T ha
  linarith

end RiemannResearch.Analysis.WeightedSharedFamilyEnergy
