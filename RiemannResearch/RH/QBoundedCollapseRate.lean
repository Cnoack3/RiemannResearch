import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative complete-Q collapse from a small physical head slope

Source: user-provided CRT-carry memorandum, Theorem 4.2, and the
19 October 2026 continuation. The complete inverse-square tail is the
existing `QFiniteEnergyBounds.norm_sq_le_head_tail`.

For the manuscript's Haar optimizer one has B=4 and t=(3/4)^M.
This module formalizes the quantitative analytic implication of those
two bounds. It does NOT yet construct the Haar optimizer, prove the
Haar primitive diagonalization, or prove its prime-product bounds.

-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QBoundedCollapseRate
open ZetaTwoHilbert ZetaTwoProbability

/-- Exact cutoff estimate; the term B^2/K bounds the entire infinite tail. -/
theorem norm_sq_cutoff (f : QHilbert) (B t : ℝ)
    (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hbounded : ∀ n, |qSequence f n| ≤ B)
    (hhead : ∀ n, |qSequence f n| ≤ B * (n : ℝ) * t)
    (K : ℕ) (hK : 0 < K) :
    ‖f‖ ^ 2 ≤ (B ^ 2 / zetaTwo) * ((K : ℝ) * t ^ 2 + 1 / (K : ℝ)) := by
  have hsum : (∑ n ∈ Finset.range K,
      (qSequence f (n+1)) ^ 2 / (n+1 : ℝ) ^ 2) ≤
        (K : ℝ) * (B ^ 2 * t ^ 2) := by
    calc
      _ ≤ ∑ n ∈ Finset.range K, B ^ 2 * t ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos : (0 : ℝ) < (n+1 : ℝ) := by positivity
        have hh : |qSequence f (n+1)| ≤ B * (n+1 : ℝ) * t := by
          simpa only [Nat.cast_add, Nat.cast_one] using hhead (n+1)
        have hb := (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (mul_nonneg hB hnpos.le) ht)).mpr hh
        simp only [sq_abs, mul_pow] at hb
        apply (div_le_iff₀ (sq_pos_of_pos hnpos)).mpr
        nlinarith [hb]
      _ = _ := by simp
  have h := QFiniteEnergyBounds.norm_sq_le_head_tail f K hK B hB hbounded
  calc
    ‖f‖ ^ 2 ≤ (1/zetaTwo) *
        ((K : ℝ) * (B ^ 2 * t ^ 2) + B ^ 2 / (K : ℝ)) := by
      exact h.trans (mul_le_mul_of_nonneg_left
        (add_le_add hsum le_rfl) (one_div_pos.mpr zetaTwo_pos).le)
    _ = _ := by ring

/-- With a cutoff comparable to 1/t the squared Q norm is O(t), rather
than just qualitatively convergent by dominated convergence. -/
theorem norm_sq_rate (f : QHilbert) (B t : ℝ)
    (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hbounded : ∀ n, |qSequence f n| ≤ B)
    (hhead : ∀ n, |qSequence f n| ≤ B * (n : ℝ) * t)
    (K : ℕ) (hK : 0 < K)
    (hlo : 1 ≤ (K : ℝ) * t) (hhi : (K : ℝ) * t ≤ 2) :
    ‖f‖ ^ 2 ≤ (3 * B ^ 2 / zetaTwo) * t := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hinv : 1 / (K : ℝ) ≤ t := by
    apply (div_le_iff₀ hKR).mpr
    nlinarith
  have hprod : (K : ℝ) * t ^ 2 ≤ 2 * t := by
    have h := mul_le_mul_of_nonneg_right hhi ht
    nlinarith
  have hnonneg : 0 ≤ B ^ 2 / zetaTwo :=
    div_nonneg (sq_nonneg B) zetaTwo_pos.le
  calc
    ‖f‖ ^ 2 ≤ (B ^ 2 / zetaTwo) *
        ((K : ℝ) * t ^ 2 + 1 / (K : ℝ)) :=
      norm_sq_cutoff f B t hB ht hbounded hhead K hK
    _ ≤ (B ^ 2 / zetaTwo) * (3*t) :=
      mul_le_mul_of_nonneg_left (by linarith) hnonneg
    _ = _ := by ring

end RiemannResearch.RH.QBoundedCollapseRate
