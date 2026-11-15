/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexLittlewoodZeros
import RiemannResearch.Analysis.ConreyBaluyotMollifiedBoundary
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact Littlewood identity and the mollifier-zero correction

For F = zeta M on a positive-height rectangle with zero-free border, split
the weighted analytic order of F exactly into the orders of zeta and M.
The second theorem retains the entire nonnegative M contribution in the
zeta-zero count bound.

These are consequences of the proved Littlewood and analytic-order
identities, not a new mollified-moment estimate. Principal normalization at
both right corners is retained when the whole right side lies in the slit
plane. The actual uniform anchor discharges this condition in the dyadic
normalized theorem.
-/

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Exact signed Littlewood identity for the actual mollified product.
The mollifier's weighted zero contribution is retained, not discarded.
The logarithm lifts are compatible around the rectangle. The bottom-right
value is principal; so is the top-right value whenever the entire right side
lies in the slit plane. -/
theorem exists_mollifiedZeta_littlewood_identity_with_remainder
    (σ y ε : ℝ) {a b H T : ℝ}
    (hab : a ≤ b) (hHT : H ≤ T) (hH : 0 < H)
    (hborder : ∀ s ∈ RectangleBorder
      ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I),
        mollifiedZeta σ y ε s ≠ 0) :
    ∃ (Z : Finset ℂ) (B U : ℝ → ℂ),
      (∀ s, s ∈ Z ↔ s ∈ Rectangle
        ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) ∧
          mollifiedZeta σ y ε s = 0) ∧
      Continuous B ∧ Continuous U ∧
      (∀ x ∈ Icc a b, exp (B x) =
        mollifiedZeta σ y ε ((x : ℂ) + (H : ℂ) * I)) ∧
      (∀ x ∈ Icc a b, exp (U x) =
        mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I)) ∧
      logRectangleBoundary (mollifiedZeta σ y ε)
        (fun x => (B x).im) (fun x => (U x).im) a b H T =
        2 * Real.pi * ((∑ ρ ∈ Z,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - a)) +
          ∑ ρ ∈ Z, (analyticOrderNatAt (nonstandardMollifier σ y ε) ρ : ℝ) *
            (ρ.re - a)) ∧
      0 ≤ ∑ ρ ∈ Z, (analyticOrderNatAt (nonstandardMollifier σ y ε) ρ : ℝ) *
        (ρ.re - a) ∧
      B b = log (mollifiedZeta σ y ε ((b : ℂ) + (H : ℂ) * I)) ∧
      ((∀ t ∈ Icc H T, mollifiedZeta σ y ε ((b : ℂ) + (t : ℂ) * I) ∈ slitPlane) →
        U b = log (mollifiedZeta σ y ε ((b : ℂ) + (T : ℂ) * I))) := by
  classical
  let z : ℂ := (a : ℂ) + (H : ℂ) * I
  let w : ℂ := (b : ℂ) + (T : ℂ) * I
  let F := mollifiedZeta σ y ε
  have hre : z.re ≤ w.re := by simpa [z, w] using hab
  have him : z.im ≤ w.im := by simpa [z, w] using hHT
  have hFmul : F = riemannZeta * nonstandardMollifier σ y ε := by
    funext s
    rfl
  have hFanalytic : AnalyticOnNhd ℂ F {s : ℂ | 0 < s.im} := by
    intro s hs
    have hsne : s ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      exact (ne_of_gt hs) hh
    exact analyticAt_mollifiedZeta σ y ε hsne
  have hpos : ∀ s ∈ Rectangle z w, 0 < s.im := by
    intro s hs
    have hi := hs.2
    rw [Set.uIcc_of_le him] at hi
    have hz : 0 < z.im := by simpa [z] using hH
    exact lt_of_lt_of_le hz hi.1
  have hf : AnalyticOnNhd ℂ F (Rectangle z w) :=
    fun s hs => hFanalytic s (hpos s hs)
  obtain ⟨Z, B, U, hZ, hBc, hUc, hBe, hUe, hboundary, hBb, hUb⟩ :=
    Complex.exists_logRectangleBoundary_eq_weighted_zeros hab hHT hf hborder
  have hzBorder : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have horderz : analyticOrderAt F z ≠ ⊤ := by
    have heq : analyticOrderAt F z = 0 :=
      (hFanalytic z (by simpa [z] using hH)).analyticOrderAt_eq_zero.mpr
        (hborder z hzBorder)
    simp [heq]
  have hadd : ∀ ρ ∈ Z, analyticOrderNatAt F ρ =
      analyticOrderNatAt riemannZeta ρ +
        analyticOrderNatAt (nonstandardMollifier σ y ε) ρ := by
    intro ρ hρ
    have hrect := ((hZ ρ).mp hρ).1
    have hρim := hpos ρ hrect
    have hρne : ρ ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      exact (ne_of_gt hρim) hh
    have hForder : analyticOrderAt F ρ ≠ ⊤ :=
      hFanalytic.analyticOrderAt_ne_top_of_isPreconnected
        (convex_halfSpace_im_gt 0).isPreconnected
        (by simpa [z] using hH) hρim horderz
    have hζorder : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      intro htop
      apply hForder
      rw [hFmul]
      exact analyticOrderAt_mul_eq_top_of_left
        (g := nonstandardMollifier σ y ε) htop
    have hMorder : analyticOrderAt (nonstandardMollifier σ y ε) ρ ≠ ⊤ := by
      intro htop
      apply hForder
      rw [hFmul]
      exact analyticOrderAt_mul_eq_top_of_right (f := riemannZeta) htop
    rw [hFmul]
    exact analyticOrderNatAt_mul (analyticAt_riemannZeta hρne)
      (analyticAt_nonstandardMollifier σ y ε ρ) hζorder hMorder
  refine ⟨Z, B, U, hZ, hBc, hUc, hBe, hUe, ?_, ?_, hBb, hUb⟩
  · rw [hboundary, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hadd ρ hρ, Nat.cast_add, add_mul]
  · apply Finset.sum_nonneg
    intro ρ hρ
    have hr := ((hZ ρ).mp hρ).1.1
    rw [Set.uIcc_of_le hre] at hr
    have ha : a ≤ ρ.re := by simpa [z] using hr.1
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ha)


/-- The same compatible boundary lifts bound every right-hand zeta-zero
count. The entire nonnegative mollifier-zero mass is subtracted before
division by the margin. Z is the product-zero set; zeta multiplicity is zero
at its points where zeta does not vanish. -/
theorem exists_mollifiedZeta_littlewood_count_bound
    (σ y ε : ℝ) {a b H T : ℝ}
    (hab : a ≤ b) (hHT : H ≤ T) (hH : 0 < H)
    (hborder : ∀ s ∈ RectangleBorder
      ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I),
        mollifiedZeta σ y ε s ≠ 0) :
    ∃ (Z : Finset ℂ) (B U : ℝ → ℂ),
      (∀ s, s ∈ Z ↔ s ∈ Rectangle
        ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) ∧
          mollifiedZeta σ y ε s = 0) ∧
      Continuous B ∧ Continuous U ∧
      (∀ x ∈ Icc a b, exp (B x) =
        mollifiedZeta σ y ε ((x : ℂ) + (H : ℂ) * I)) ∧
      (∀ x ∈ Icc a b, exp (U x) =
        mollifiedZeta σ y ε ((x : ℂ) + (T : ℂ) * I)) ∧
      ∀ α : ℝ, a < α →
        ((∑ ρ ∈ Z.filter (fun s => α ≤ s.re),
            analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
          (logRectangleBoundary (mollifiedZeta σ y ε)
              (fun x => (B x).im) (fun x => (U x).im) a b H T /
                (2 * Real.pi) -
            ∑ ρ ∈ Z, (analyticOrderNatAt (nonstandardMollifier σ y ε) ρ : ℝ) *
              (ρ.re - a)) / (α - a) := by
  classical
  obtain ⟨Z, B, U, hZ, hBc, hUc, hBe, hUe, hid, _, _, _⟩ :=
    exists_mollifiedZeta_littlewood_identity_with_remainder σ y ε hab hHT hH hborder
  refine ⟨Z, B, U, hZ, hBc, hUc, hBe, hUe, ?_⟩
  intro α hα
  have hmass :
      (α - a) * ((∑ ρ ∈ Z.filter (fun s => α ≤ s.re),
          analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - a) := by
    calc
      (α - a) * ((∑ ρ ∈ Z.filter (fun s => α ≤ s.re),
          analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) =
        ∑ ρ ∈ Z.filter (fun s => α ≤ s.re),
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (α - a) := by
            push_cast
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ρ _
            ring
      _ ≤ ∑ ρ ∈ Z.filter (fun s => α ≤ s.re),
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - a) := by
            apply Finset.sum_le_sum
            intro ρ hρ
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            exact sub_le_sub_right (Finset.mem_filter.mp hρ).2 a
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - a) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro ρ hρ _
            have hr := ((hZ ρ).mp hρ).1.1
            have hre : (((a : ℂ) + (H : ℂ) * I)).re ≤
                (((b : ℂ) + (T : ℂ) * I)).re := by simpa using hab
            rw [Set.uIcc_of_le hre] at hr
            have ha : a ≤ ρ.re := by simpa using hr.1
            exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ha)
  apply (le_div_iff₀ (sub_pos.mpr hα)).mpr
  rw [hid]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hpi]
  linarith

end RiemannResearch.Analysis.ConreyBaluyot
