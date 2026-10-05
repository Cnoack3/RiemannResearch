/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.Analytic.RectangleLogDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Weighted rectangle zero counts and outward boundary avoidance

The weighted identity specializes the proved argument principle in
WeilExplicitFormula/Analytic/RectangleLogDeriv. Finite re/im coordinate
exclusion then gives outward zero-free rectangles with a fixed zero-free
right side, retaining the entire original closed rectangle. This supplies
the boundary limiting step used with the Littlewood route of
Chourasiya--Simonic, arXiv:2507.15184v2, Section 4:
https://arxiv.org/html/2507.15184v2. No simplicity or RH assumption occurs.
-/

noncomputable section
open Complex Set Topology Filter
open scoped BigOperators

namespace Complex

theorem weightedLogExcess_eq_rectangleContour {f : ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (D : Finset ℂ) (hD : ∀ s ∈ Rectangle z w, f s = 0 ↔ s ∈ D)
    (hDsub : (D : Set ℂ) ⊆ Rectangle z w) :
    (∑ ρ ∈ D, ((analyticOrderAt f ρ).toNat : ℝ) * max 0 (ρ.re - z.re)) =
      (RectangleIntegral' (fun s => (s - z) * logDeriv f s) z w).re := by
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => s - z) (Rectangle z w) := by
    intro s hs
    fun_prop
  rw [Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder D hD hDsub]
  change _ = Complex.reAddGroupHom _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hα : z.re ≤ ρ.re := ((mem_Rect hre him ρ).mp (hDsub hρ)).1
  rw [max_eq_right (sub_nonneg.mpr hα)]
  simp [analyticOrderNatAt, Complex.mul_re]

end Complex

namespace Complex

/-- Finite coordinate exclusion produces an outward perturbation whose right
line is unchanged. The original closed rectangle is entirely preserved. -/
theorem exists_zeroFreeRectangle_expansion {F : ℂ → ℂ} {α β H T ε : ℝ}
    (hαβ : α < β) (hHT : H ≤ T) (hε : 0 < ε)
    (hF : AnalyticOnNhd ℂ F
      (Rectangle (((α - ε : ℝ) : ℂ) + ((H - ε : ℝ) : ℂ) * I)
        ((β : ℂ) + ((T + ε : ℝ) : ℂ) * I)))
    (hR : ∀ t ∈ Icc (H - ε) (T + ε), F ((β : ℂ) + (t : ℂ) * I) ≠ 0) :
    ∃ α' H' T' : ℝ, α' ∈ Ioo (α - ε) α ∧ H' ∈ Ioo (H - ε) H ∧
      T' ∈ Ioo T (T + ε) ∧
      (∀ s ∈ RectangleBorder ((α' : ℂ) + (H' : ℂ) * I)
        ((β : ℂ) + (T' : ℂ) * I), F s ≠ 0) ∧
      Rectangle ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I) ⊆
        Rectangle ((α' : ℂ) + (H' : ℂ) * I) ((β : ℂ) + (T' : ℂ) * I) := by
  classical
  let z : ℂ := ((α - ε : ℝ) : ℂ) + ((H - ε : ℝ) : ℂ) * I
  let w : ℂ := (β : ℂ) + ((T + ε : ℝ) : ℂ) * I
  let p : ℂ := (β : ℂ) + ((H - ε : ℝ) : ℂ) * I
  have hre : z.re ≤ w.re := by simp [z, w]; linarith
  have him : z.im ≤ w.im := by simp [z, w]; linarith
  have hbig (s : ℂ) : s ∈ Rectangle z w ↔
      (α - ε ≤ s.re ∧ s.re ≤ β) ∧ (H - ε ≤ s.im ∧ s.im ≤ T + ε) := by
    simp only [Rectangle, mem_reProdIm, z, w, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add, uIcc_of_le (show α - ε ≤ β by linarith),
      uIcc_of_le (show H - ε ≤ T + ε by linarith), mem_Icc]
  have hp : p ∈ Rectangle z w := by
    apply (hbig p).mpr
    simp [p]
    constructor <;> linarith
  have hp0 : F p ≠ 0 := hR (H - ε) ⟨le_rfl, by linarith⟩
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hF hp hp0
  let S : Set ℂ := Rectangle z w ∩ F ⁻¹' {0}
  have hfinre : (Complex.re '' S).Finite := hfin.image Complex.re
  have hfinim : (Complex.im '' S).Finite := hfin.image Complex.im
  obtain ⟨α', hα', hα'not⟩ :=
    ((Ioo_infinite (show α - ε < α by linarith)).sdiff hfinre).nonempty
  obtain ⟨H', hH', hH'not⟩ :=
    ((Ioo_infinite (show H - ε < H by linarith)).sdiff hfinim).nonempty
  obtain ⟨T', hT', hT'not⟩ :=
    ((Ioo_infinite (show T < T + ε by linarith)).sdiff hfinim).nonempty
  let z' : ℂ := (α' : ℂ) + (H' : ℂ) * I
  let w' : ℂ := (β : ℂ) + (T' : ℂ) * I
  have hα'β : α' ≤ β := (hα'.2.trans hαβ).le
  have hH'T' : H' ≤ T' := by linarith [hH'.2, hT'.1]
  have hsmall (s : ℂ) : s ∈ Rectangle z' w' ↔
      (α' ≤ s.re ∧ s.re ≤ β) ∧ (H' ≤ s.im ∧ s.im ≤ T') := by
    simp only [Rectangle, mem_reProdIm, z', w', Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add, uIcc_of_le hα'β, uIcc_of_le hH'T', mem_Icc]
  have hsub : Rectangle z' w' ⊆ Rectangle z w := by
    intro s hs
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hsmall s).mp hs
    apply (hbig s).mpr
    exact ⟨⟨hα'.1.le.trans hr1, hr2⟩, ⟨hH'.1.le.trans hi1, hi2.trans hT'.2.le⟩⟩
  have hborder : ∀ s ∈ RectangleBorder z' w', F s ≠ 0 := by
    intro s hs hzero
    have hsBig := hsub (rectangleBorder_subset_rectangle z' w' hs)
    have hsS : s ∈ S := ⟨hsBig, by simpa using hzero⟩
    have hsRe : s.re ∈ Complex.re '' S := ⟨s, hsS, rfl⟩
    have hsIm : s.im ∈ Complex.im '' S := ⟨s, hsS, rfl⟩
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff,
      z', w', Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add] at hs
    rcases hs with ((⟨_, he⟩ | ⟨he, _⟩) | ⟨_, he⟩) | ⟨he, _⟩
    · exact hH'not (by simpa [he] using hsIm)
    · exact hα'not (by simpa [he] using hsRe)
    · exact hT'not (by simpa [he] using hsIm)
    · have hp' : s = (β : ℂ) + (s.im : ℂ) * I := by
        apply Complex.ext <;> simp [he]
      have himrange := ((hbig s).mp hsBig).2
      apply (hR s.im himrange)
      simpa [← hp'] using hzero
  have hkeep : Rectangle ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I) ⊆
      Rectangle ((α' : ℂ) + (H' : ℂ) * I) ((β : ℂ) + (T' : ℂ) * I) :=
    RectSubRect hα'.2.le hαβ.le le_rfl hH'.2.le hHT hT'.1.le
  exact ⟨α', H', T', hα', hH', hT', hborder, hkeep⟩

end Complex
