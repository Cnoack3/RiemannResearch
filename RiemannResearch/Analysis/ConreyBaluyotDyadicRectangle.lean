/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotZeroFreeRectangle

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- A normalized continuous horizontal phase with its logarithmic integral
bound, for one fixed complex function and one height. -/
def GoodHorizontalPhase (F : ℂ → ℂ) (b D T t : ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc (1 / 2 : ℝ) b) ∧
    φ b = (F ((b : ℂ) + (t : ℂ) * I)).arg ∧
    (∀ x ∈ Set.Icc (1 / 2 : ℝ) b,
      F ((x : ℂ) + (t : ℂ) * I) =
        (‖F ((x : ℂ) + (t : ℂ) * I)‖ : ℂ) *
          Complex.exp ((φ x : ℂ) * I)) ∧
    ∀ a ∈ Set.Icc (1 / 2 : ℝ) b, ‖∫ x in a..b, φ x‖ ≤ D * Real.log T

/-- For one fixed mollifier of length T^theta, one may choose good horizontal
edges arbitrarily near T and 2T and select vertical sides in arbitrary
separated interior intervals. Both horizontal phase integrals retain their
uniform O(log T) bound. -/
theorem exists_uniform_dyadic_mollifiedZeta_zero_free_rectangle
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ 0 < D ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ α β : ℝ,
            1 / 2 < α → α < β → β < b →
              ∃ t₁ t₂ l r : ℝ, |t₁ - T| < δ ∧ |t₂ - 2 * T| < δ ∧
                1 / 2 < l ∧ l < α ∧ β < r ∧ r < b ∧
                0 < t₁ ∧ t₁ < t₂ ∧
                (∀ s ∈ RectangleBorder ((l : ℂ) + (t₁ : ℂ) * I)
                    ((r : ℂ) + (t₂ : ℂ) * I),
                  mollifiedZeta σ (T ^ θ) ε s ≠ 0) ∧
                GoodHorizontalPhase (mollifiedZeta σ (T ^ θ) ε) b D T t₁ ∧
                GoodHorizontalPhase (mollifiedZeta σ (T ^ θ) ε) b D T t₂ := by
  obtain ⟨η, b, D, H, hη, hη', hb, hD, hH, _, hdyadic⟩ :=
    exists_uniform_mollifiedZeta_dyadic_good_horizontal_argument hε hθ
  refine ⟨η, b, D, H, hη, hη', hb, hD, hH, ?_⟩
  intro T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  have hT0 : 0 < T := by linarith
  have hTmem : T ∈ Set.Icc (T - 1 / 4) (2 * T + 1 / 4) := ⟨by linarith, by linarith⟩
  have h2Tmem : 2 * T ∈ Set.Icc (T - 1 / 4) (2 * T + 1 / 4) := ⟨by linarith, by linarith⟩
  obtain ⟨t₁, ht₁, hfree₁, φ₁, hφ₁, hφb₁, hrep₁, hint₁⟩ :=
    hdyadic T hT σ hσ hση T hTmem δ hδ hδ'
  obtain ⟨t₂, ht₂, hfree₂, φ₂, hφ₂, hφb₂, hrep₂, hint₂⟩ :=
    hdyadic T hT σ hσ hση (2 * T) h2Tmem δ hδ hδ'
  have ht₁pos : 0 < t₁ := by
    have hh := (abs_lt.mp ht₁).1
    linarith
  have htt : t₁ < t₂ := by
    have h1 := (abs_lt.mp ht₁).2
    have h2 := (abs_lt.mp ht₂).1
    linarith
  let z : ℂ := (1 / 2 : ℂ) + (t₁ : ℂ) * I
  let w : ℂ := (b : ℂ) + (t₂ : ℂ) * I
  let F := mollifiedZeta σ (T ^ θ) ε
  have hre : z.re ≤ w.re := by simp [z, w]; linarith
  have him : z.im ≤ w.im := by simpa [z, w] using htt.le
  have hf : AnalyticOnNhd ℂ F (Rectangle z w) := by
    intro s hs
    have hsi : t₁ ≤ s.im := by
      have hi := hs.2
      rw [Set.uIcc_of_le him] at hi
      simpa [z] using hi.1
    have hspos : 0 < s.im := lt_of_lt_of_le ht₁pos hsi
    have hsne : s ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    exact analyticAt_mollifiedZeta σ (T ^ θ) ε hsne
  have hbot : ∀ x ∈ Set.Icc z.re w.re,
      F ((x : ℂ) + (z.im : ℂ) * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Set.Icc (1 / 2 : ℝ) b := by simpa [z, w] using hx
    simpa [z, F] using hfree₁ x hx'
  have htop : ∀ x ∈ Set.Icc z.re w.re,
      F ((x : ℂ) + (w.im : ℂ) * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Set.Icc (1 / 2 : ℝ) b := by simpa [z, w] using hx
    simpa [w, F] using hfree₂ x hx'
  obtain ⟨l, r, hl1, hl2, hr1, hr2, hborder⟩ :=
    exists_zero_free_rectangle_border_between F hre him hf hbot htop α β
      (by simpa [z] using hα) hαβ (by simpa [w] using hβ)
  refine ⟨t₁, t₂, l, r, ht₁, ht₂, ?_, hl2, hr1, ?_, ht₁pos, htt, ?_, ?_, ?_⟩
  · simpa [z] using hl1
  · simpa [w] using hr2
  · simpa [z, w, F] using hborder
  · exact ⟨φ₁, hφ₁, hφb₁, hrep₁, hint₁⟩
  · exact ⟨φ₂, hφ₂, hφb₂, hrep₂, hint₂⟩

/-- The same anchor works for an outward rectangle: its horizontal edges
lie strictly below T and above 2T, so no limiting passage is needed to cover
the closed dyadic height window. The left edge may be selected inside any
prescribed nonempty interval above 1/2. The mollifier remains fixed at T^theta. -/
theorem exists_uniform_dyadic_mollifiedZeta_outward_anchor_rectangle
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ 0 < D ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ a α : ℝ,
            1 / 2 ≤ a → a < α → α < b →
              ∃ t₁ t₂ l : ℝ, T - δ < t₁ ∧ t₁ < T ∧
                2 * T < t₂ ∧ t₂ < 2 * T + δ ∧
                1 / 2 < l ∧ a < l ∧ l < α ∧ 0 < t₁ ∧ t₁ < t₂ ∧
                (∀ s ∈ RectangleBorder ((l : ℂ) + (t₁ : ℂ) * I)
                    ((b : ℂ) + (t₂ : ℂ) * I),
                  mollifiedZeta σ (T ^ θ) ε s ≠ 0) ∧
                (∀ s : ℂ, b ≤ s.re →
                  1 / 2 ≤ (mollifiedZeta σ (T ^ θ) ε s).re) ∧
                GoodHorizontalPhase (mollifiedZeta σ (T ^ θ) ε) b D T t₁ ∧
                GoodHorizontalPhase (mollifiedZeta σ (T ^ θ) ε) b D T t₂ := by
  obtain ⟨η, b, D, H, hη, hη', hb, hD, hH, hanchor, hdyadic⟩ :=
    exists_uniform_mollifiedZeta_dyadic_good_horizontal_argument hε hθ
  refine ⟨η, b, D, H, hη, hη', hb, hD, hH, ?_⟩
  intro T hT σ hσ hση δ hδ hδ' a α ha hα hαb
  have hT0 : 0 < T := by linarith
  obtain ⟨t₁, ht₁, hfree₁, φ₁, hφ₁, hφb₁, hrep₁, hint₁⟩ :=
    hdyadic T hT σ hσ hση (T - δ / 2)
      ⟨by linarith, by linarith⟩ (δ / 2) (by positivity) (by linarith)
  obtain ⟨t₂, ht₂, hfree₂, φ₂, hφ₂, hφb₂, hrep₂, hint₂⟩ :=
    hdyadic T hT σ hσ hση (2 * T + δ / 2)
      ⟨by linarith, by linarith⟩ (δ / 2) (by positivity) (by linarith)
  have ht₁lo : T - δ < t₁ := by have hh := (abs_lt.mp ht₁).1; linarith
  have ht₁hi : t₁ < T := by have hh := (abs_lt.mp ht₁).2; linarith
  have ht₂lo : 2 * T < t₂ := by have hh := (abs_lt.mp ht₂).1; linarith
  have ht₂hi : t₂ < 2 * T + δ := by have hh := (abs_lt.mp ht₂).2; linarith
  have ht₁pos : 0 < t₁ := by linarith
  have htt : t₁ < t₂ := by linarith
  let z : ℂ := (1 / 2 : ℂ) + (t₁ : ℂ) * I
  let w : ℂ := (b : ℂ) + (t₂ : ℂ) * I
  let F := mollifiedZeta σ (T ^ θ) ε
  have hre : z.re ≤ w.re := by simp [z, w]; linarith
  have him : z.im ≤ w.im := by simpa [z, w] using htt.le
  have hf : AnalyticOnNhd ℂ F (Rectangle z w) := by
    intro s hs
    have hsi : t₁ ≤ s.im := by
      have hi := hs.2
      rw [Set.uIcc_of_le him] at hi
      simpa [z] using hi.1
    have hspos : 0 < s.im := lt_of_lt_of_le ht₁pos hsi
    have hsne : s ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    exact analyticAt_mollifiedZeta σ (T ^ θ) ε hsne
  have hz : F z ≠ 0 := by
    simpa [F, z] using hfree₁ (1 / 2) ⟨le_rfl, by linarith⟩
  obtain ⟨l, hal, hlα, hleft⟩ :=
    exists_zero_free_vertical_of_nontrivial_rectangle F hre him hf
      (left_mem_rect z w) hz a α (by simpa [z] using ha) hα
      (by simpa [w] using hαb.le)
  have hl : 1 / 2 < l := ha.trans_lt hal
  have hlb : l ≤ b := by linarith
  have hr : ∀ t ∈ Icc t₁ t₂, F ((b : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _ he
    have hh := hanchor T hT σ hσ hση ((b : ℂ) + (t : ℂ) * I) (by simp)
    change (1 / 2 : ℝ) ≤ (F ((b : ℂ) + (t : ℂ) * I)).re at hh
    rw [he] at hh
    norm_num at hh
  refine ⟨t₁, t₂, l, ht₁lo, ht₁hi, ht₂lo, ht₂hi, hl, hal, hlα,
    ht₁pos, htt, ?_, hanchor T hT σ hσ hση,
    ⟨φ₁, hφ₁, hφb₁, hrep₁, hint₁⟩,
    ⟨φ₂, hφ₂, hφb₂, hrep₂, hint₂⟩⟩
  intro s hs
  have hs' : (((s.re ∈ Icc l b ∧ s.im = t₁) ∨
      (s.re = l ∧ s.im ∈ Icc t₁ t₂)) ∨
      (s.re ∈ Icc l b ∧ s.im = t₂)) ∨
      (s.re = b ∧ s.im ∈ Icc t₁ t₂) := by
    simpa [RectangleBorder, Complex.mem_reProdIm, Set.uIcc_of_le hlb,
      Set.uIcc_of_le htt.le] using hs
  rcases hs' with (((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩) | ⟨hx, hy⟩)
  · have hh := hfree₁ s.re ⟨by linarith [hx.1], hx.2⟩
    simpa [← hy, Complex.re_add_im] using hh
  · have hh := hleft s.im (by simpa [z, w] using hy)
    simpa [F, ← hx, Complex.re_add_im] using hh
  · have hh := hfree₂ s.re ⟨by linarith [hx.1], hx.2⟩
    simpa [← hy, Complex.re_add_im] using hh
  · have hh := hr s.im hy
    simpa [F, ← hx, Complex.re_add_im] using hh

end RiemannResearch.Analysis.ConreyBaluyot
