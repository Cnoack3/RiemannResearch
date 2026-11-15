/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotDyadicRectangle

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- For the actual fixed mollifier of length T^theta, the multiplicity count
of the zeta zeros to the right of alpha in a suitably chosen dyadic rectangle
is bounded by the normalized weighted log-derivative contour integral, with
positive horizontal margin alpha - l. Both horizontal phase bounds persist. -/
theorem exists_uniform_dyadic_zeta_rectangle_count_bound
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ 0 < D ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ α β : ℝ,
            1 / 2 < α → α < β → β < b →
              ∃ (t₁ t₂ l r : ℝ) (Z : Finset ℂ),
                |t₁ - T| < δ ∧ |t₂ - 2 * T| < δ ∧
                1 / 2 < l ∧ l < α ∧ β < r ∧ r < b ∧ 0 < t₁ ∧ t₁ < t₂ ∧
                (∀ s ∈ RectangleBorder ((l : ℂ) + (t₁ : ℂ) * I)
                    ((r : ℂ) + (t₂ : ℂ) * I),
                  mollifiedZeta σ (T ^ θ) ε s ≠ 0) ∧
                GoodHorizontalPhase (mollifiedZeta σ (T ^ θ) ε) b D T t₁ ∧
                GoodHorizontalPhase (mollifiedZeta σ (T ^ θ) ε) b D T t₂ ∧
                (∀ s, s ∈ Z ↔ s ∈ Rectangle ((l : ℂ) + (t₁ : ℂ) * I)
                    ((r : ℂ) + (t₂ : ℂ) * I) ∧ riemannZeta s = 0) ∧
                (α - l) * ((∑ ρ ∈ Z.filter (fun s => α ≤ s.re),
                    analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
                  (RectangleIntegral' (fun s => (s - (l : ℂ)) *
                    logDeriv (mollifiedZeta σ (T ^ θ) ε) s)
                      ((l : ℂ) + (t₁ : ℂ) * I)
                      ((r : ℂ) + (t₂ : ℂ) * I)).re := by
  obtain ⟨η, b, D, H, hη, hη', hb, hD, hH, hrect⟩ :=
    exists_uniform_dyadic_mollifiedZeta_zero_free_rectangle hε hθ
  refine ⟨η, b, D, H, hη, hη', hb, hD, hH, ?_⟩
  intro T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  obtain ⟨t₁, t₂, l, r, ht₁, ht₂, hl1, hl2, hr1, hr2, htpos, htt,
    hborder, hphase₁, hphase₂⟩ :=
      hrect T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  let z : ℂ := (l : ℂ) + (t₁ : ℂ) * I
  let w : ℂ := (r : ℂ) + (t₂ : ℂ) * I
  have hre : z.re ≤ w.re := by simp [z, w]; linarith
  have him : z.im ≤ w.im := by simpa [z, w] using htt.le
  have hzpos : 0 < z.im := by simpa [z] using htpos
  have hα' : z.re ≤ α := by simpa [z] using hl2.le
  have hbdr : ∀ s ∈ RectangleBorder z w, mollifiedZeta σ (T ^ θ) ε s ≠ 0 := by
    simpa [z, w] using hborder
  obtain ⟨Z, hZ, hbound⟩ :=
    exists_zeta_rectangle_count_margin_bound σ (T ^ θ) ε α hre him hzpos hα' hbdr
  refine ⟨t₁, t₂, l, r, Z, ht₁, ht₂, hl1, hl2, hr1, hr2, htpos, htt,
    hborder, hphase₁, hphase₂, ?_, ?_⟩
  · simpa [z, w] using hZ
  · simpa [z, w] using hbound

end RiemannResearch.Analysis.ConreyBaluyot
