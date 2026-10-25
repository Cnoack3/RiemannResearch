/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative saturation from relative capacity gains

Source: the squarefree-capacity research agenda supplied on 24 October 2026.
This elementary finite-sum argument retains the relative-gain hypothesis;
it supplies no arithmetic lower bound for a Schur complement.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.RelativeGainSaturation

def mass (b : ℕ → ℝ) (N : ℕ) : ℝ := ∑ j ∈ Finset.range N, b j

theorem mass_nonneg {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (N : ℕ) :
    0 ≤ mass b N :=
  Finset.sum_nonneg fun j _ => hb j

/-- The finite relative-gain budget is bounded by the accumulated gain. -/
theorem mass_deficit_le {k b : ℕ → ℝ} (hmono : Monotone k)
    (hb : ∀ j, 0 ≤ b j)
    (hgain : ∀ j, b j * (1 - k j) ≤ k (j + 1) - k j) (N : ℕ) :
    (1 - k N) * mass b N ≤ k N - k 0 := by
  induction N with
  | zero => simp [mass]
  | succ N ih =>
    have hs := mass_nonneg hb N
    have hd : 0 ≤ k (N + 1) - k N := sub_nonneg.mpr (hmono (Nat.le_succ N))
    have hdropS := mul_nonneg hd hs
    have hdropB := mul_nonneg hd (hb N)
    have hg := hgain N
    simp only [mass, Finset.sum_range_succ] at ih ⊢
    change 0 ≤ ∑ j ∈ Finset.range N, b j at hs
    change 0 ≤ (k (N + 1) - k N) * (∑ j ∈ Finset.range N, b j) at hdropS
    nlinarith

/-- A quantitative, logarithm-free defect bound. -/
theorem defect_mul_one_add_mass_le {k b : ℕ → ℝ} (hmono : Monotone k)
    (hb : ∀ j, 0 ≤ b j)
    (hgain : ∀ j, b j * (1 - k j) ≤ k (j + 1) - k j) (N : ℕ) :
    (1 - k N) * (1 + mass b N) ≤ 1 - k 0 := by
  have h := mass_deficit_le hmono hb hgain N
  nlinarith

theorem defect_le_div_one_add_mass {k b : ℕ → ℝ} (hmono : Monotone k)
    (hb : ∀ j, 0 ≤ b j)
    (hgain : ∀ j, b j * (1 - k j) ≤ k (j + 1) - k j) (N : ℕ) :
    1 - k N ≤ (1 - k 0) / (1 + mass b N) := by
  apply (le_div_iff₀ (by linarith [mass_nonneg hb N])).mpr
  exact defect_mul_one_add_mass_le hmono hb hgain N

theorem limiting_mass_deficit_le {k b : ℕ → ℝ} {L : ℝ}
    (hmono : Monotone k) (hb : ∀ j, 0 ≤ b j)
    (hgain : ∀ j, b j * (1 - k j) ≤ k (j + 1) - k j)
    (hupper : ∀ j, k j ≤ L) (N : ℕ) :
    (1 - L) * mass b N ≤ L - k 0 := by
  have h := mass_deficit_le hmono hb hgain N
  have hs := mass_nonneg hb N
  have hd := mul_nonneg (sub_nonneg.mpr (hupper N)) hs
  have hu := hupper N
  nlinarith

theorem upper_eq_one_of_cofinal_mass {k b : ℕ → ℝ} {L : ℝ}
    (hmono : Monotone k) (hb : ∀ j, 0 ≤ b j)
    (hgain : ∀ j, b j * (1 - k j) ≤ k (j + 1) - k j)
    (hupper : ∀ j, k j ≤ L) (hL : L ≤ 1)
    (hlarge : ∀ R : ℝ, ∃ N, R ≤ mass b N) : L = 1 := by
  by_contra hne
  have hpos : 0 < 1 - L := sub_pos.mpr (lt_of_le_of_ne hL hne)
  obtain ⟨N, hN⟩ := hlarge ((L - k 0 + 1) / (1 - L))
  have hlo : L - k 0 + 1 ≤ mass b N * (1 - L) := (div_le_iff₀ hpos).mp hN
  have hhi := limiting_mass_deficit_le hmono hb hgain hupper N
  nlinarith

/-- The exact relative increase, with nonzero finite defect required by consumers. -/
def exactGain (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  (k (j + 1) - k j) / (1 - k j)

theorem exactGain_mul_deficit {k : ℕ → ℝ} (hlt : ∀ j, k j < 1) (j : ℕ) :
    exactGain k j * (1 - k j) = k (j + 1) - k j := by
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr (hlt j)))

theorem exactGain_bounds {k : ℕ → ℝ} (hmono : Monotone k)
    (hlt : ∀ j, k j < 1) (j : ℕ) :
    0 ≤ exactGain k j ∧ exactGain k j < 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr (hmono (Nat.le_succ j)))
      (sub_nonneg.mpr (hlt j).le)
  · apply (div_lt_one (sub_pos.mpr (hlt j))).mpr
    linarith [hlt (j + 1)]

theorem defect_succ_eq {k : ℕ → ℝ} (hlt : ∀ j, k j < 1) (j : ℕ) :
    1 - k (j + 1) = (1 - k j) * (1 - exactGain k j) := by
  have h := exactGain_mul_deficit hlt j
  nlinarith

theorem defect_eq_product {k : ℕ → ℝ} (hlt : ∀ j, k j < 1) (N : ℕ) :
    1 - k N = (1 - k 0) * ∏ j ∈ Finset.range N, (1 - exactGain k j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [defect_succ_eq hlt N, ih, Finset.prod_range_succ]
    ring

end RiemannResearch.Analysis.RelativeGainSaturation
