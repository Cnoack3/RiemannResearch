/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotZetaRectangle

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- For a nontrivial analytic function on a rectangle, the real parts of its
zeros form a finite set. Thus a vertical segment avoiding all zeros exists in
every nonempty open subinterval of the rectangle's horizontal range. -/
theorem exists_zero_free_vertical_of_nontrivial_rectangle
    (f : ℂ → ℂ) {z w c : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hc : c ∈ Rectangle z w) (hfc : f c ≠ 0)
    (a b : ℝ) (hza : z.re ≤ a) (hab : a < b) (hbw : b ≤ w.re) :
    ∃ x : ℝ, a < x ∧ x < b ∧
      ∀ t ∈ Set.Icc z.im w.im, f ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
  classical
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hf hc hfc
  let S : Finset ℝ := hfin.toFinset.image Complex.re
  obtain ⟨x, hax, hxb, hxS⟩ := exists_between_not_finset S a b hab
  refine ⟨x, hax, hxb, ?_⟩
  intro t ht hz
  let p : ℂ := (x : ℂ) + (t : ℂ) * I
  have hp : p ∈ Rectangle z w := by
    apply (mem_Rect hre him p).2
    have hh : z.re ≤ x ∧ x ≤ w.re ∧ z.im ≤ t ∧ t ≤ w.im :=
      ⟨by linarith, by linarith, ht.1, ht.2⟩
    simpa [p] using hh
  have hxS' : x ∈ S := by
    apply Finset.mem_image.mpr
    refine ⟨p, hfin.mem_toFinset.mpr ⟨hp, hz⟩, ?_⟩
    simp [p]
  exact hxS hxS'


/-- If the upper and lower edges of an analytic rectangle are zero-free,
its two vertical sides can be chosen in arbitrary prescribed interior
intervals, giving a completely zero-free rectangle border. -/
theorem exists_zero_free_rectangle_border_between
    (f : ℂ → ℂ) {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (hbot : ∀ x ∈ Set.Icc z.re w.re, f ((x : ℂ) + (z.im : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.Icc z.re w.re, f ((x : ℂ) + (w.im : ℂ) * I) ≠ 0)
    (α β : ℝ) (hzα : z.re < α) (hαβ : α < β) (hβw : β < w.re) :
    ∃ l r : ℝ, z.re < l ∧ l < α ∧ β < r ∧ r < w.re ∧
      ∀ s ∈ RectangleBorder ((l : ℂ) + (z.im : ℂ) * I)
          ((r : ℂ) + (w.im : ℂ) * I), f s ≠ 0 := by
  have hz : f z ≠ 0 := by
    simpa using hbot z.re ⟨le_rfl, hre⟩
  obtain ⟨l, hl1, hl2, hleft⟩ :=
    exists_zero_free_vertical_of_nontrivial_rectangle f hre him hf
      (left_mem_rect z w) hz z.re α le_rfl hzα (by linarith)
  obtain ⟨r, hr1, hr2, hright⟩ :=
    exists_zero_free_vertical_of_nontrivial_rectangle f hre him hf
      (left_mem_rect z w) hz β w.re (by linarith) hβw le_rfl
  have hlr : l ≤ r := by linarith
  refine ⟨l, r, hl1, hl2, hr1, hr2, ?_⟩
  intro s hs
  have hs' : (((s.re ∈ Set.Icc l r ∧ s.im = z.im) ∨
      (s.re = l ∧ s.im ∈ Set.Icc z.im w.im)) ∨
      (s.re ∈ Set.Icc l r ∧ s.im = w.im)) ∨
      (s.re = r ∧ s.im ∈ Set.Icc z.im w.im) := by
    simpa [RectangleBorder, Complex.mem_reProdIm, Set.uIcc_of_le hlr,
      Set.uIcc_of_le him] using hs
  rcases hs' with (((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩) | ⟨hx, hy⟩)
  · have hh := hbot s.re ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa [← hy, Complex.re_add_im] using hh
  · have hh := hleft s.im hy
    simpa [← hx, Complex.re_add_im] using hh
  · have hh := htop s.re ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa [← hy, Complex.re_add_im] using hh
  · have hh := hright s.im hy
    simpa [← hx, Complex.re_add_im] using hh

end RiemannResearch.Analysis.ConreyBaluyot
