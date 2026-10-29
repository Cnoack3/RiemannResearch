/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Weighted three-site and shared-site energy completions

Source: user-provided general squarefree-head energy argument, 29 October
2026; the shared-site extension follows by successive scalar completions.
The complete omitted-coordinate series is retained.

The scalar identities and complete-series decomposition were kernel checked;
the accompanying research memorandum records verification scope.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.WeightedConstraintEnergy

theorem three_site_completion (A B C x y z t : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hS : A + B + C ≠ 0) (h : x + y - z = t) :
    x ^ 2 / A + y ^ 2 / B + z ^ 2 / C =
      t ^ 2 / (A + B + C) +
      (x - A * t / (A + B + C)) ^ 2 / A +
      (y - B * t / (A + B + C)) ^ 2 / B +
      (z + C * t / (A + B + C)) ^ 2 / C := by
  have hz : z = x + y - t := by linarith
  rw [hz]
  field_simp [hA, hB, hC, hS]
  <;> ring

theorem three_site_lower_bound (A B C x y z t : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : x + y - z = t) :
    t ^ 2 / (A + B + C) ≤ x ^ 2 / A + y ^ 2 / B + z ^ 2 / C := by
  rw [three_site_completion A B C x y z t hA.ne' hB.ne' hC.ne'
    (by positivity) h]
  have h1 := div_nonneg (sq_nonneg (x - A * t / (A + B + C))) hA.le
  have h2 := div_nonneg (sq_nonneg (y - B * t / (A + B + C))) hB.le
  have h3 := div_nonneg (sq_nonneg (z + C * t / (A + B + C))) hC.le
  linarith

/-- A prescribed head together with three distinct sites beyond it. -/
def headThreeSites (d m : ℕ) : Finset ℕ :=
  insert d (insert (m - 1) (insert m (Finset.Ico 1 d)))

theorem sum_headThreeSites (f : ℕ → ℝ) {d m : ℕ}
    (hm : d + 1 < m) :
    (∑ k ∈ headThreeSites d m, f k) =
      (∑ k ∈ Finset.Ico 1 d, f k) + f d + f (m - 1) + f m := by
  have h1 : d ∉ insert (m - 1) (insert m (Finset.Ico 1 d)) := by
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  have h2 : m - 1 ∉ insert m (Finset.Ico 1 d) := by
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  have h3 : m ∉ Finset.Ico 1 d := by
    simp only [Finset.mem_Ico]
    omega
  rw [headThreeSites, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_insert h3]
  ring

/-- Denominators may vanish off the selected positive sites; in particular
the physical zero coordinate has zero weight under Lean's total division. -/
def omittedEnergy (a f : ℕ → ℝ) (d m : ℕ) : ℝ :=
  ∑' k : {n : ℕ // n ∉ headThreeSites d m}, f k ^ 2 / a k

theorem omittedEnergy_nonneg (a f : ℕ → ℝ) (d m : ℕ)
    (ha : ∀ k, 0 ≤ a k) : 0 ≤ omittedEnergy a f d m :=
  tsum_nonneg (fun k => div_nonneg (sq_nonneg _) (ha k))

theorem complete_head_three_split (a f : ℕ → ℝ) {d m : ℕ}
    (hm : d + 1 < m) (hf : Summable (fun k => f k ^ 2 / a k))
    (hh : ∀ k, 0 < k → k < d → f k = 1) :
    (∑' k, f k ^ 2 / a k) =
      (∑ k ∈ Finset.Ico 1 d, 1 / a k) +
      f d ^ 2 / a d + f (m - 1) ^ 2 / a (m - 1) + f m ^ 2 / a m +
      omittedEnergy a f d m := by
  have hhead : (∑ k ∈ Finset.Ico 1 d, f k ^ 2 / a k) =
      ∑ k ∈ Finset.Ico 1 d, 1 / a k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    rw [hh k (by omega) hk'.2, one_pow]
  calc
    _ = (∑ k ∈ headThreeSites d m, f k ^ 2 / a k) +
        omittedEnergy a f d m :=
      (hf.sum_add_tsum_subtype_compl (headThreeSites d m)).symm
    _ = _ := by rw [sum_headThreeSites _ hm, hhead]

def threeSiteRemainder (A B C x y z : ℝ) : ℝ :=
  (x - A / (A + B + C)) ^ 2 / A +
  (y - B / (A + B + C)) ^ 2 / B +
  (z + C / (A + B + C)) ^ 2 / C

theorem threeSiteRemainder_nonneg (A B C x y z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ threeSiteRemainder A B C x y z := by
  unfold threeSiteRemainder
  positivity

/-- Exact complete series identity before dropping any nonnegative term. -/
theorem complete_head_three_completion (a f : ℕ → ℝ) {d m : ℕ}
    (hm : d + 1 < m) (hf : Summable (fun k => f k ^ 2 / a k))
    (hh : ∀ k, 0 < k → k < d → f k = 1)
    (hA : 0 < a d) (hB : 0 < a (m - 1)) (hC : 0 < a m)
    (hrel : f d + f (m - 1) - f m = 1) :
    (∑' k, f k ^ 2 / a k) =
      (∑ k ∈ Finset.Ico 1 d, 1 / a k) +
      1 / (a d + a (m - 1) + a m) +
      threeSiteRemainder (a d) (a (m - 1)) (a m) (f d) (f (m - 1)) (f m) +
      omittedEnergy a f d m := by
  have h := three_site_completion (a d) (a (m - 1)) (a m)
    (f d) (f (m - 1)) (f m) 1 hA.ne' hB.ne' hC.ne'
    (by positivity) hrel
  simp only [one_pow, mul_one] at h
  rw [complete_head_three_split a f hm hf hh]
  unfold threeSiteRemainder
  linarith

theorem complete_head_three_lower_bound (a f : ℕ → ℝ) {d m : ℕ}
    (hm : d + 1 < m) (hf : Summable (fun k => f k ^ 2 / a k))
    (hh : ∀ k, 0 < k → k < d → f k = 1) (ha : ∀ k, 0 ≤ a k)
    (hA : 0 < a d) (hB : 0 < a (m - 1)) (hC : 0 < a m)
    (hrel : f d + f (m - 1) - f m = 1) :
    (∑ k ∈ Finset.Ico 1 d, 1 / a k) +
      1 / (a d + a (m - 1) + a m) ≤ ∑' k, f k ^ 2 / a k := by
  rw [complete_head_three_completion a f hm hf hh hA hB hC hrel]
  have hr := threeSiteRemainder_nonneg (a d) (a (m - 1)) (a m)
    (f d) (f (m - 1)) (f m) hA.le hB.le hC.le
  have ho := omittedEnergy_nonneg a f d m ha
  linarith

theorem pair_completion (b c y z t : ℝ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b + c ≠ 0) (h : y - z = t) :
    y ^ 2 / b + z ^ 2 / c = t ^ 2 / (b + c) +
      (y - b * t / (b + c)) ^ 2 / b +
      (z + c * t / (b + c)) ^ 2 / c := by
  have hz : z = y - t := by linarith
  rw [hz]
  field_simp [hb, hc, hbc]
  <;> ring

/-- The scalar Schur complement for rows sharing one physical site. -/
theorem shared_site_completion (a S x : ℝ)
    (ha : a ≠ 0) (hD : 1 + a * S ≠ 0) :
    x ^ 2 / a + S * (1 - x) ^ 2 =
      S / (1 + a * S) +
      (1 / a + S) * (x - a * S / (1 + a * S)) ^ 2 := by
  field_simp [ha, hD]
  <;> ring

/-- Finite shared-site family; applications must separately ensure that their
physical tail pairs are distinct before identifying this sum with energy. -/
theorem shared_family_completion {ι : Type*} (T : Finset ι)
    (a x : ℝ) (b c y z : ι → ℝ)
    (ha : a ≠ 0) (hb : ∀ i ∈ T, b i ≠ 0)
    (hc : ∀ i ∈ T, c i ≠ 0) (hbc : ∀ i ∈ T, b i + c i ≠ 0)
    (hrel : ∀ i ∈ T, x + y i - z i = 1)
    (hD : 1 + a * (∑ i ∈ T, 1 / (b i + c i)) ≠ 0) :
    x ^ 2 / a + (∑ i ∈ T, (y i ^ 2 / b i + z i ^ 2 / c i)) =
      (∑ i ∈ T, 1 / (b i + c i)) /
        (1 + a * (∑ i ∈ T, 1 / (b i + c i))) +
      (1 / a + (∑ i ∈ T, 1 / (b i + c i))) *
        (x - a * (∑ i ∈ T, 1 / (b i + c i)) /
          (1 + a * (∑ i ∈ T, 1 / (b i + c i)))) ^ 2 +
      ∑ i ∈ T, ((y i - b i * (1 - x) / (b i + c i)) ^ 2 / b i +
        (z i + c i * (1 - x) / (b i + c i)) ^ 2 / c i) := by
  have hp (i : ι) (hi : i ∈ T) :=
    pair_completion (b i) (c i) (y i) (z i) (1 - x)
      (hb i hi) (hc i hi) (hbc i hi) (by linarith [hrel i hi])
  have he : (∑ i ∈ T, (y i ^ 2 / b i + z i ^ 2 / c i)) =
      (∑ i ∈ T, 1 / (b i + c i)) * (1 - x) ^ 2 +
      ∑ i ∈ T, ((y i - b i * (1 - x) / (b i + c i)) ^ 2 / b i +
        (z i + c i * (1 - x) / (b i + c i)) ^ 2 / c i) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = _ := hp i hi
      _ = _ := by ring
  rw [he, ← add_assoc, shared_site_completion a _ x ha hD]

theorem schur_correction_increment (a S T : ℝ)
    (hS : 1 + a * S ≠ 0) (hT : 1 + a * T ≠ 0) :
    T / (1 + a * T) - S / (1 + a * S) =
      (T - S) / ((1 + a * T) * (1 + a * S)) := by
  have hS' : 1 + S * a ≠ 0 := by simpa only [mul_comm] using hS
  have hT' : 1 + T * a ≠ 0 := by simpa only [mul_comm] using hT
  field_simp [hS, hT, hS', hT']
  <;> ring

/-- Every added positive conductance strictly improves the shared-site bound. -/
theorem schur_correction_strict_mono (a S T : ℝ)
    (ha : 0 ≤ a) (hS : 0 ≤ S) (hST : S < T) :
    S / (1 + a * S) < T / (1 + a * T) := by
  have hT : 0 ≤ T := le_trans hS hST.le
  have hDS : 0 < 1 + a * S := by positivity
  have hDT : 0 < 1 + a * T := by positivity
  have h := schur_correction_increment a S T hDS.ne' hDT.ne'
  have hp : 0 < (T - S) / ((1 + a * T) * (1 + a * S)) :=
    div_pos (sub_pos.mpr hST) (mul_pos hDT hDS)
  linarith

end RiemannResearch.Analysis.WeightedConstraintEnergy
