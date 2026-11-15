/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotWeightedRectangle
import Mathlib.Analysis.Complex.Convex

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- On a positive-height rectangle whose boundary is zero-free for the actual
mollified product, the normalized weighted log-derivative integral majorizes
the weighted analytic-multiplicity sum of all zeta zeros in the rectangle. -/
theorem zeta_weighted_zeros_le_mollifiedZeta_rectangle_integral
    (σ y ε : ℝ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hzpos : 0 < z.im)
    (hborder : ∀ s ∈ RectangleBorder z w, mollifiedZeta σ y ε s ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ s ∈ Rectangle z w, mollifiedZeta σ y ε s = 0 ↔ s ∈ Z) ∧
      (Z : Set ℂ) ⊆ Rectangle z w ∧
      (∀ s ∈ Rectangle z w, riemannZeta s = 0 → s ∈ Z) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)) ≤
        (RectangleIntegral' (fun s => (s - (z.re : ℂ)) *
          logDeriv (mollifiedZeta σ y ε) s) z w).re := by
  classical
  let F := mollifiedZeta σ y ε
  have hFmul : F = riemannZeta * nonstandardMollifier σ y ε := by
    funext s
    rfl
  obtain ⟨Z, hZ, hZsub, hweighted⟩ :=
    mollifiedZeta_rectangle_weighted_zero_identity σ y ε hre him hzpos hborder
  have hzBorder : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hFanalytic : AnalyticOnNhd ℂ F {s : ℂ | 0 < s.im} := by
    intro s hs
    change 0 < s.im at hs
    have hsne : s ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    exact analyticAt_mollifiedZeta σ y ε hsne
  have horderz : analyticOrderAt F z ≠ ⊤ := by
    have heq : analyticOrderAt F z = 0 :=
      (hFanalytic z hzpos).analyticOrderAt_eq_zero.mpr (hborder z hzBorder)
    simp [heq]
  refine ⟨Z, hZ, hZsub, ?_, ?_⟩
  · intro s hs hzero
    apply (hZ s hs).mp
    simp [mollifiedZeta, hzero]
  · rw [hweighted]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hrect := hZsub hρ
    have hρim : 0 < ρ.im := by
      have hi := hrect.2
      rw [Set.uIcc_of_le him] at hi
      exact lt_of_lt_of_le hzpos hi.1
    have hρne : ρ ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    have hForder : analyticOrderAt F ρ ≠ ⊤ :=
      hFanalytic.analyticOrderAt_ne_top_of_isPreconnected
        (convex_halfSpace_im_gt 0).isPreconnected hzpos hρim horderz
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
    have hadd : analyticOrderNatAt F ρ =
        analyticOrderNatAt riemannZeta ρ +
          analyticOrderNatAt (nonstandardMollifier σ y ε) ρ := by
      rw [hFmul]
      exact analyticOrderNatAt_mul (analyticAt_riemannZeta hρne)
          (analyticAt_nonstandardMollifier σ y ε ρ) hζorder hMorder
    have hnat : analyticOrderNatAt riemannZeta ρ ≤ analyticOrderNatAt F ρ := by
      omega
    have hreal : (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
        (analyticOrderNatAt F ρ : ℝ) := by exact_mod_cast hnat
    apply mul_le_mul_of_nonneg_right hreal
    have hr := hrect.1
    rw [Set.uIcc_of_le hre] at hr
    linarith [hr.1]


/-- There is a finite set of exactly the zeta zeros in the rectangle, counted
with analytic multiplicity, whose weighted sum is bounded by the actual
mollified product's normalized weighted log-derivative contour integral. -/
theorem exists_zeta_rectangle_weighted_zero_bound
    (σ y ε : ℝ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hzpos : 0 < z.im)
    (hborder : ∀ s ∈ RectangleBorder z w, mollifiedZeta σ y ε s ≠ 0) :
    ∃ A : Finset ℂ,
      (∀ s, s ∈ A ↔ s ∈ Rectangle z w ∧ riemannZeta s = 0) ∧
      (∑ ρ ∈ A, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re)) ≤
        (RectangleIntegral' (fun s => (s - (z.re : ℂ)) *
          logDeriv (mollifiedZeta σ y ε) s) z w).re := by
  classical
  obtain ⟨Z, hZ, hZsub, hzeta, hbound⟩ :=
    zeta_weighted_zeros_le_mollifiedZeta_rectangle_integral σ y ε hre him hzpos hborder
  let A := Z.filter (fun s => riemannZeta s = 0)
  refine ⟨A, ?_, ?_⟩
  · intro s
    constructor
    · intro hs
      have hs' := Finset.mem_filter.mp hs
      exact ⟨hZsub hs'.1, hs'.2⟩
    · rintro ⟨hs, hzero⟩
      exact Finset.mem_filter.mpr ⟨hzeta s hs hzero, hzero⟩
  · refine le_trans ?_ hbound
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro ρ hρ hnot
    have hrect := hZsub hρ
    have hr := hrect.1
    rw [Set.uIcc_of_le hre] at hr
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hr.1)


/-- A rectangle-zero count, including analytic multiplicities, is bounded by
the weighted log-derivative contour integral after division by the positive
horizontal margin. The rectangle boundary must be zero-free for the product. -/
theorem exists_zeta_rectangle_count_margin_bound
    (σ y ε α : ℝ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hzpos : 0 < z.im)
    (hα : z.re ≤ α)
    (hborder : ∀ s ∈ RectangleBorder z w, mollifiedZeta σ y ε s ≠ 0) :
    ∃ A : Finset ℂ,
      (∀ s, s ∈ A ↔ s ∈ Rectangle z w ∧ riemannZeta s = 0) ∧
      (α - z.re) * ((∑ ρ ∈ A.filter (fun s => α ≤ s.re),
          analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        (RectangleIntegral' (fun s => (s - (z.re : ℂ)) *
          logDeriv (mollifiedZeta σ y ε) s) z w).re := by
  classical
  obtain ⟨A, hA, hbound⟩ :=
    exists_zeta_rectangle_weighted_zero_bound σ y ε hre him hzpos hborder
  refine ⟨A, hA, ?_⟩
  calc
    (α - z.re) * ((∑ ρ ∈ A.filter (fun s => α ≤ s.re),
        analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) =
      ∑ ρ ∈ A.filter (fun s => α ≤ s.re),
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (α - z.re) := by
          push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ρ hρ
          ring
    _ ≤ ∑ ρ ∈ A.filter (fun s => α ≤ s.re),
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - z.re) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          have hρ' := (Finset.mem_filter.mp hρ).2
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          linarith
    _ ≤ ∑ ρ ∈ A, (analyticOrderNatAt riemannZeta ρ : ℝ) *
        (ρ.re - z.re) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro ρ hρ hnot
          have hrect := (hA ρ).mp hρ |>.1
          have hr := hrect.1
          rw [Set.uIcc_of_le hre] at hr
          exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hr.1)
    _ ≤ _ := hbound

end RiemannResearch.Analysis.ConreyBaluyot
