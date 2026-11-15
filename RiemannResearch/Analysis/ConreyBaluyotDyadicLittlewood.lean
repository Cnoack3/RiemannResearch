/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotLittlewood
import RiemannResearch.Analysis.ConreyBaluyotDyadicRectangle
import Mathlib.Tactic.Linarith

/-!
# Actual dyadic Littlewood rectangles with an exact mollifier remainder

Combine the proved good-height rectangle selection with the exact signed
Littlewood identity. All mollifier parameters stay fixed between the two
horizontal edges. The logarithm lifts in the identity are compatible around
the rectangle; the separately proved bounds for principal-normalized phases
still need a compatibility/winding estimate before they bound these lifts.
-/

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- On the established parameter strip, dyadic rectangles and compatible
logarithm lifts exist with the exact signed zero identity. No zero-free-border
or supplied-phase hypothesis remains in this existence theorem. -/
theorem exists_uniform_dyadic_littlewood_identity
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ α β : ℝ,
            1 / 2 < α → α < β → β < b →
              ∃ (t₁ t₂ l r : ℝ) (Z : Finset ℂ) (B U : ℝ → ℂ),
                |t₁ - T| < δ ∧ |t₂ - 2 * T| < δ ∧
                1 / 2 < l ∧ l < α ∧ β < r ∧ r < b ∧
                0 < t₁ ∧ t₁ < t₂ ∧
                (∀ s ∈ RectangleBorder ((l : ℂ) + (t₁ : ℂ) * I)
                    ((r : ℂ) + (t₂ : ℂ) * I),
                  mollifiedZeta σ (T ^ θ) ε s ≠ 0) ∧
                (∀ s, s ∈ Z ↔ s ∈ Rectangle
                  ((l : ℂ) + (t₁ : ℂ) * I) ((r : ℂ) + (t₂ : ℂ) * I) ∧
                    mollifiedZeta σ (T ^ θ) ε s = 0) ∧
                Continuous B ∧ Continuous U ∧
                (∀ x ∈ Icc l r, exp (B x) =
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t₁ : ℂ) * I)) ∧
                (∀ x ∈ Icc l r, exp (U x) =
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t₂ : ℂ) * I)) ∧
                logRectangleBoundary (mollifiedZeta σ (T ^ θ) ε)
                  (fun x => (B x).im) (fun x => (U x).im) l r t₁ t₂ =
                  2 * Real.pi * ((∑ ρ ∈ Z,
                    (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l)) +
                    ∑ ρ ∈ Z,
                      (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ) *
                        (ρ.re - l)) := by
  obtain ⟨η, b, D, H, hη, hη', hb, _, hH, hrect⟩ :=
    exists_uniform_dyadic_mollifiedZeta_zero_free_rectangle hε hθ
  refine ⟨η, b, H, hη, hη', hb, hH, ?_⟩
  intro T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  obtain ⟨t₁, t₂, l, r, ht₁, ht₂, hl, hlα, hβr, hr, ht₁pos, htt,
      hborder, _, _⟩ :=
    hrect T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  have hlr : l ≤ r := by linarith
  obtain ⟨Z, B, U, hZ, hBc, hUc, hBe, hUe, hid, _⟩ :=
    exists_mollifiedZeta_littlewood_identity_with_remainder
      σ (T ^ θ) ε hlr htt.le ht₁pos hborder
  exact ⟨t₁, t₂, l, r, Z, B, U, ht₁, ht₂, hl, hlα, hβr, hr, ht₁pos, htt,
    hborder, hZ, hBc, hUc, hBe, hUe, hid⟩

end RiemannResearch.Analysis.ConreyBaluyot
