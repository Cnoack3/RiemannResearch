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
  obtain ⟨η, b, D, H, hη, hη', hb, hD, hH, hdyadic⟩ :=
    exists_uniform_mollifiedZeta_dyadic_good_horizontal_argument hε hθ
  refine ⟨η, b, D, H, hη, hη', hb, hD, hH, ?_⟩
  intro T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  have hT0 : 0 < T := by linarith
  have hTmem : T ∈ Set.Icc T (2 * T) := ⟨le_rfl, by linarith⟩
  have h2Tmem : 2 * T ∈ Set.Icc T (2 * T) := ⟨by linarith, le_rfl⟩
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

end RiemannResearch.Analysis.ConreyBaluyot
