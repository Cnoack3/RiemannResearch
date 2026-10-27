/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete nonnegative jump energies

Source: the user's countable prime-resampling/Poincare formalization request,
27 October 2026. Every energy is ENNReal-valued, so a divergent nonnegative
series has value infinity. Finite-head exhaustion and Tonelli equalities
are proved before any exit-rate estimate.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.Analysis.CountableJumpEnergy
variable {α ι : Type*}

/-- The complete reversible-jump normalization, including its factor one half. -/
def countableJumpEnergy (W : α → α → ℝ≥0∞) (g : α → ℝ) : ℝ≥0∞ :=
  ∑' x, ∑' y, W x y * ENNReal.ofReal ((g x - g y) ^ 2 / 2)

def finiteSetEnergy (W : α → α → ℝ≥0∞) (g : α → ℝ) (S : Finset α) : ℝ≥0∞ :=
  ∑ x ∈ S, ∑ y ∈ S, W x y * ENNReal.ofReal ((g x - g y) ^ 2 / 2)

/-- The pair-indexed representation is an exact Tonelli identity. -/
theorem countableJumpEnergy_eq_tsum_prod (W : α → α → ℝ≥0∞) (g : α → ℝ) :
    countableJumpEnergy W g =
      ∑' e : α × α, W e.1 e.2 * ENNReal.ofReal ((g e.1 - g e.2) ^ 2 / 2) := by
  exact ENNReal.tsum_prod.symm

/-- Exact equivalence with one half of the full squared-difference sum. -/
theorem countableJumpEnergy_eq_half (W : α → α → ℝ≥0∞) (g : α → ℝ) :
    countableJumpEnergy W g =
      (1 / 2 : ℝ≥0∞) * ∑' x, ∑' y, W x y * ENNReal.ofReal ((g x - g y) ^ 2) := by
  have hterm (x y : α) : W x y * ENNReal.ofReal ((g x - g y) ^ 2 / 2) =
      (1 / 2 : ℝ≥0∞) * (W x y * ENNReal.ofReal ((g x - g y) ^ 2)) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    simp only [div_eq_mul_inv, one_mul]
    ac_rfl
  unfold countableJumpEnergy
  simp_rw [hterm, ENNReal.tsum_mul_left]

/-- Exact decomposition over any countable family of nonnegative conductances. -/
theorem countableJumpEnergy_tsum_weights (W : ι → α → α → ℝ≥0∞) (g : α → ℝ) :
    countableJumpEnergy (fun x y => ∑' i, W i x y) g =
      ∑' i, countableJumpEnergy (W i) g := by
  unfold countableJumpEnergy
  simp_rw [← ENNReal.tsum_mul_right]
  calc
    _ = ∑' x, ∑' i, ∑' y,
        W i x y * ENNReal.ofReal ((g x - g y) ^ 2 / 2) := by
      apply tsum_congr
      intro x
      exact ENNReal.tsum_comm
    _ = _ := ENNReal.tsum_comm

/-- Diagonal self-loops contribute exactly zero, even for infinite weights. -/
theorem countableJumpEnergy_offDiagonal [DecidableEq α] (W : α → α → ℝ≥0∞) (g : α → ℝ) :
    countableJumpEnergy (fun x y => if x = y then 0 else W x y) g =
      countableJumpEnergy W g := by
  classical
  apply tsum_congr
  intro x
  apply tsum_congr
  intro y
  by_cases h : x = y
  · subst y; simp
  · simp [h]

theorem finiteSetEnergy_le (W : α → α → ℝ≥0∞) (g : α → ℝ) (S : Finset α) :
    finiteSetEnergy W g S ≤ countableJumpEnergy W g := by
  calc
    _ ≤ ∑ x ∈ S, ∑' y, W x y * ENNReal.ofReal ((g x - g y) ^ 2 / 2) := by
      exact Finset.sum_le_sum (fun x hx => ENNReal.sum_le_tsum S)
    _ ≤ _ := ENNReal.sum_le_tsum S

/-- Finite square heads determine the entire energy, including infinity. -/
theorem countableJumpEnergy_le_iff (W : α → α → ℝ≥0∞) (g : α → ℝ) (C : ℝ≥0∞) :
    countableJumpEnergy W g ≤ C ↔ ∀ S : Finset α, finiteSetEnergy W g S ≤ C := by
  classical
  constructor
  · intro h S
    exact (finiteSetEnergy_le W g S).trans h
  · intro h
    rw [countableJumpEnergy_eq_tsum_prod, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro T
    let S : Finset α := T.image Prod.fst ∪ T.image Prod.snd
    have hsub : T ⊆ S ×ˢ S := by
      intro e he
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    calc
      _ ≤ ∑ e ∈ S ×ˢ S,
          W e.1 e.2 * ENNReal.ofReal ((g e.1 - g e.2) ^ 2 / 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)
      _ = finiteSetEnergy W g S := by rw [Finset.sum_product]; rfl
      _ ≤ _ := h S

theorem countableJumpEnergy_eq_iSup_finiteSetEnergy
    (W : α → α → ℝ≥0∞) (g : α → ℝ) :
    countableJumpEnergy W g = ⨆ S : Finset α, finiteSetEnergy W g S := by
  apply le_antisymm
  · exact (countableJumpEnergy_le_iff W g _).mpr (fun S => le_iSup _ S)
  · exact iSup_le (finiteSetEnergy_le W g)

theorem finiteSetEnergy_mono (W : α → α → ℝ≥0∞) (g : α → ℝ)
    {S T : Finset α} (h : S ⊆ T) : finiteSetEnergy W g S ≤ finiteSetEnergy W g T := by
  classical
  calc
    _ ≤ ∑ x ∈ S, ∑ y ∈ T, W x y * ENNReal.ofReal ((g x - g y) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => zero_le)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => zero_le)

/-- Literal finite physical heads exhaust the entire countable energy. -/
theorem countableJumpEnergy_eq_iSup_range
    (W : ℕ → ℕ → ℝ≥0∞) (g : ℕ → ℝ) :
    countableJumpEnergy W g = ⨆ N : ℕ, finiteSetEnergy W g (Finset.range N) := by
  apply le_antisymm
  · apply (countableJumpEnergy_le_iff W g _).mpr
    intro S
    let N := S.sup id + 1
    have hsub : S ⊆ Finset.range N := by
      intro n hn
      have h := Finset.le_sup (f := id) hn
      apply Finset.mem_range.mpr
      dsimp [N]
      exact Nat.lt_succ_of_le h
    exact (finiteSetEnergy_mono W g hsub).trans (le_iSup (fun N : ℕ => finiteSetEnergy W g (Finset.range N)) N)
  · exact iSup_le (fun N => finiteSetEnergy_le W g (Finset.range N))

/-- Every contraction of pairwise differences decreases the complete energy. -/
theorem energy_mono_of_abs_sub_le (W : α → α → ℝ≥0∞) (f g : α → ℝ)
    (h : ∀ x y, |f x - f y| ≤ |g x - g y|) :
    countableJumpEnergy W f ≤ countableJumpEnergy W g := by
  apply ENNReal.tsum_le_tsum
  intro x
  apply ENNReal.tsum_le_tsum
  intro y
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply ENNReal.ofReal_le_ofReal
  have hs := mul_self_le_mul_self (abs_nonneg _) (h x y)
  nlinarith [sq_abs (f x - f y), sq_abs (g x - g y)]

theorem countableJumpEnergy_mono_weights (W V : α → α → ℝ≥0∞) (g : α → ℝ)
    (h : ∀ x y, W x y ≤ V x y) : countableJumpEnergy W g ≤ countableJumpEnergy V g := by
  exact ENNReal.tsum_le_tsum (fun x => ENNReal.tsum_le_tsum
    (fun y => mul_le_mul_of_nonneg_right (h x y) (by positivity)))

/-- The complete symmetric energy is at most twice its full exit-weighted
square budget. All sums and inequalities are infinity-safe. -/
theorem countableJumpEnergy_le_twice_rate (W : α → α → ℝ≥0∞) (g : α → ℝ)
    (hsym : ∀ x y, W x y = W y x) :
    countableJumpEnergy W g ≤
      2 * ∑' x, (∑' y, W x y) * ENNReal.ofReal ((g x) ^ 2) := by
  have hpoint (x y : α) : ENNReal.ofReal ((g x - g y) ^ 2 / 2) ≤
      ENNReal.ofReal ((g x) ^ 2) + ENNReal.ofReal ((g y) ^ 2) := by
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g x + g y)]
  have hfirst : (∑' x, ∑' y, W x y * ENNReal.ofReal ((g x) ^ 2)) =
      ∑' x, (∑' y, W x y) * ENNReal.ofReal ((g x) ^ 2) := by
    simp_rw [ENNReal.tsum_mul_right]
  have hsecond : (∑' x, ∑' y, W x y * ENNReal.ofReal ((g y) ^ 2)) =
      ∑' x, (∑' y, W x y) * ENNReal.ofReal ((g x) ^ 2) := by
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro x
    simp_rw [hsym _ x, ENNReal.tsum_mul_right]
  calc
    _ ≤ ∑' x, ∑' y, W x y *
        (ENNReal.ofReal ((g x) ^ 2) + ENNReal.ofReal ((g y) ^ 2)) :=
      ENNReal.tsum_le_tsum (fun x => ENNReal.tsum_le_tsum
        (fun y => mul_le_mul_of_nonneg_left (hpoint x y) (by positivity)))
    _ = (∑' x, ∑' y, W x y * ENNReal.ofReal ((g x) ^ 2)) +
        (∑' x, ∑' y, W x y * ENNReal.ofReal ((g y) ^ 2)) := by
      simp_rw [mul_add, ENNReal.tsum_add]
    _ = _ := by rw [hfirst, hsecond, two_mul]

theorem countableJumpEnergy_le_of_rate_le (W : α → α → ℝ≥0∞) (g : α → ℝ)
    (r : α → ℝ≥0∞) (hsym : ∀ x y, W x y = W y x)
    (hrate : ∀ x, (∑' y, W x y) ≤ r x) :
    countableJumpEnergy W g ≤ 2 * ∑' x, r x * ENNReal.ofReal ((g x) ^ 2) := by
  exact (countableJumpEnergy_le_twice_rate W g hsym).trans
    (mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum
      (fun x => mul_le_mul_of_nonneg_right (hrate x) (by positivity))) (by positivity))

/-- Changing a zero-mass state does not change a complete jump energy. -/
theorem countableJumpEnergy_congr_off_zero
    (W : ℕ → ℕ → ℝ≥0∞) (hleft : ∀ n, W 0 n = 0) (hright : ∀ n, W n 0 = 0)
    (f g : ℕ → ℝ) (hfg : ∀ n : ℕ, n ≠ 0 → f n = g n) :
    countableJumpEnergy W f = countableJumpEnergy W g := by
  unfold countableJumpEnergy
  apply tsum_congr
  intro n
  apply tsum_congr
  intro m
  by_cases hn : n = 0
  · subst n
    simp [hleft]
  by_cases hm : m = 0
  · subst m
    simp [hright]
  rw [hfg n hn, hfg m hm]

end RiemannResearch.Analysis.CountableJumpEnergy
