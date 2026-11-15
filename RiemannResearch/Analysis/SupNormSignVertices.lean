/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sup-norm finite-source operator norms occur at sign vertices

Source: Reciprocal_Head_Investigation_2026-11-07.md, Section 4.
The domain is the ordinary finite Pi space, whose norm is the supremum norm.
No Euclidean-domain identification is made. The proof rounds coordinates
one at a time by the exact two-endpoint convex decomposition.
-/

noncomputable section
namespace ContinuousLinearMap
variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A sign vector dominating every vector of the closed unit cube. -/
theorem exists_sign_vector_norm_ge (T : (ι → ℝ) →L[ℝ] H)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∃ y : ι → ℝ, (∀ i, y i = -1 ∨ y i = 1) ∧ ‖T x‖ ≤ ‖T y‖ := by
  classical
  have hfinite : ∀ s : Finset ι, ∃ y : ι → ℝ,
      (∀ i ∈ s, y i = -1 ∨ y i = 1) ∧
      (∀ i ∉ s, y i = x i) ∧ ‖T x‖ ≤ ‖T y‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨x, by simp, by simp, le_rfl⟩
    | @insert i s his ih =>
      obtain ⟨y, hys, hout, hnorm⟩ := ih
      have hyi : |y i| ≤ 1 := by rw [hout i his]; exact hx i
      let lo := Function.update y i (-1)
      let hi := Function.update y i 1
      let α : ℝ := (1 + y i) / 2
      let β : ℝ := (1 - y i) / 2
      have hα : 0 ≤ α := by dsimp [α]; linarith [(abs_le.mp hyi).1]
      have hβ : 0 ≤ β := by dsimp [β]; linarith [(abs_le.mp hyi).2]
      have hsum : α + β = 1 := by dsimp [α, β]; ring
      have hrepr : α • hi + β • lo = y := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [hi, lo, α, β]
          ring
        · simp [hi, lo, hji, α, β]
          ring
      have hbound : ‖T y‖ ≤ max ‖T lo‖ ‖T hi‖ := by
        calc
          ‖T y‖ = ‖α • T hi + β • T lo‖ := by rw [← hrepr, map_add, map_smul, map_smul]
          _ ≤ ‖α • T hi‖ + ‖β • T lo‖ := norm_add_le _ _
          _ = α * ‖T hi‖ + β * ‖T lo‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hα, abs_of_nonneg hβ]
          _ ≤ max ‖T lo‖ ‖T hi‖ := by
            have h1 := mul_le_mul_of_nonneg_left (le_max_right ‖T lo‖ ‖T hi‖) hα
            have h2 := mul_le_mul_of_nonneg_left (le_max_left ‖T lo‖ ‖T hi‖) hβ
            calc
              _ ≤ α * max ‖T lo‖ ‖T hi‖ + β * max ‖T lo‖ ‖T hi‖ := add_le_add h1 h2
              _ = max ‖T lo‖ ‖T hi‖ := by rw [← add_mul, hsum, one_mul]
      let z := if ‖T lo‖ ≤ ‖T hi‖ then hi else lo
      have hzi : z i = -1 ∨ z i = 1 := by
        dsimp [z]
        split_ifs <;> simp [hi, lo]
      have hzsame : ∀ j, j ≠ i → z j = y j := by
        intro j hji
        dsimp [z]
        split_ifs <;> simp [hi, lo, hji]
      have hzNorm : max ‖T lo‖ ‖T hi‖ = ‖T z‖ := by
        dsimp [z]
        split_ifs with h
        · exact max_eq_right h
        · exact max_eq_left (le_of_not_ge h)
      refine ⟨z, ?_, ?_, hnorm.trans (hbound.trans_eq hzNorm)⟩
      · intro j hj
        by_cases hji : j = i
        · simpa [hji] using hzi
        · rw [hzsame j hji]
          exact hys j (Finset.mem_of_mem_insert_of_ne hj hji)
      · intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hj (Finset.mem_insert_self _ _)
        have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
        rw [hzsame j hji, hout j hjs]
  obtain ⟨y, hy, _, hnorm⟩ := hfinite Finset.univ
  exact ⟨y, fun i => hy i (Finset.mem_univ i), hnorm⟩

def signVertex (b : ι → Bool) : ι → ℝ := fun i => if b i then 1 else -1

theorem signVertex_norm_le_one (b : ι → Bool) : ‖signVertex b‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  simp only [signVertex, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- A finite sup-domain operator attains its norm on a sign vertex. -/
theorem exists_signVertex_opNorm (T : (ι → ℝ) →L[ℝ] H) :
    ∃ b : ι → Bool, ‖T‖ = ‖T (signVertex b)‖ := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ
    (fun b : ι → Bool => ‖T (signVertex b)‖) Finset.univ_nonempty
  have hmax : ∀ y : ι → ℝ, (∀ i, y i = -1 ∨ y i = 1) →
      ‖T y‖ ≤ ‖T (signVertex b)‖ := by
    intro y hy
    let c : ι → Bool := fun i => decide (y i = 1)
    have hc : signVertex c = y := by
      funext i
      rcases hy i with hi | hi <;> norm_num [signVertex, c, hi]
    rw [← hc]
    exact hb c (Finset.mem_univ c)
  have hbound : ‖T‖ ≤ ‖T (signVertex b)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _)
    intro x
    by_cases hx : x = 0
    · simp [hx]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := (1 / ‖x‖) • x
    have hy : ∀ i, |y i| ≤ 1 := by
      intro i
      have hx' : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
      dsimp [y]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_div, abs_one,
        abs_of_nonneg (norm_nonneg x)]
      simpa only [one_div_mul_eq_div] using (div_le_one hn).mpr hx'
    obtain ⟨z, hz, hyz⟩ := exists_sign_vector_norm_ge T y hy
    have h := hyz.trans (hmax z hz)
    have he : ‖T y‖ = ‖T x‖ / ‖x‖ := by
      simp [y, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn.le, div_eq_mul_inv, mul_comm]
    rw [he] at h
    exact (div_le_iff₀ hn).mp h
  refine ⟨b, le_antisymm hbound ?_⟩
  calc
    ‖T (signVertex b)‖ ≤ ‖T‖ * ‖signVertex b‖ := T.le_opNorm _
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left (signVertex_norm_le_one b) (norm_nonneg _)
    _ = ‖T‖ := mul_one _

end ContinuousLinearMap
