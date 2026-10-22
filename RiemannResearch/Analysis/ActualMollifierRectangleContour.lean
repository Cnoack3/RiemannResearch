/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import RiemannResearch.Analysis.ComplexRectangleZeroCount
import Mathlib.Tactic.FunProp

/-!
# Actual detector orders bounded by the weighted rectangle contour

The actual zeta cutoff is included in the full finite detector-zero set.
All additional detector orders are retained before using their nonnegativity.
The underlying counting route is Chourasiya--Simonic, arXiv:2507.15184v2,
equation (32): https://arxiv.org/html/2507.15184v2. The argument principle,
analyticity, finite zero set and inclusion are proved, with only geometric
and border-nonvanishing domain hypotheses.
-/

noncomputable section
open Complex Set Topology Filter
open scoped BigOperators

namespace RiemannResearch.Analysis.InghamMollifier

theorem zetaDetector_analyticOnNhd_rectangle (X : ℕ) {α β H T : ℝ}
    (hαβ : α ≤ β) (hH : 0 < H) (hHT : H ≤ T) :
    AnalyticOnNhd ℂ (zetaDetector X)
      (Rectangle ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I)) := by
  intro s hs
  have hre : ((α : ℂ) + (H : ℂ) * I).re ≤ ((β : ℂ) + (T : ℂ) * I).re := by
    simpa using hαβ
  have him : ((α : ℂ) + (H : ℂ) * I).im ≤ ((β : ℂ) + (T : ℂ) * I).im := by
    simpa using hHT
  have hi : H ≤ s.im := by
    simpa using ((mem_Rect hre him s).mp hs).2.2.1
  have hs1 : s ≠ 1 := by
    intro he
    simp [he] at hi
    linarith
  exact Complex.quadraticZeroDetector_analyticAt (analyticAt_riemannZeta hs1)
    (mollifier_analyticAt X s)

end RiemannResearch.Analysis.InghamMollifier

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier

theorem detectorLogExcessOnZetaWindow_le_rectangleContour (X : ℕ)
    {α β H T : ℝ} (hαβ : α ≤ β) (hβ : 1 ≤ β) (hH : 0 < H) (hHT : H ≤ T)
    (hborder : ∀ s ∈ RectangleBorder ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I),
      zetaDetector X s ≠ 0) :
    detectorLogExcessOnZetaWindow X H T α ≤
      (RectangleIntegral' (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv (zetaDetector X) s)
        ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I)).re := by
  classical
  let z : ℂ := (α : ℂ) + (H : ℂ) * I
  let w : ℂ := (β : ℂ) + (T : ℂ) * I
  have hre : z.re ≤ w.re := by simpa [z, w] using hαβ
  have him : z.im ≤ w.im := by simpa [z, w] using hHT
  have hf := zetaDetector_analyticOnNhd_rectangle X hαβ hH hHT
  have hzB : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hf
    (rectangleBorder_subset_rectangle z w hzB) (hborder z hzB)
  let D : Finset ℂ := hfin.toFinset
  have hD : ∀ s ∈ Rectangle z w, zetaDetector X s = 0 ↔ s ∈ D := by
    intro s hs
    have hs' : s ∈ Rectangle ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I) := hs
    simp [D, Set.Finite.mem_toFinset, hs']
  have hDsub : (D : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    exact ((Set.Finite.mem_toFinset hfin).mp hs).1
  have hactive : activeLogExcessWindow H T α ⊆ D := by
    intro ρ hρ
    obtain ⟨hzero, hρα, hρβ, hρH, hρT⟩ := activeLogExcessWindow_mem_rectangle X hβ hρ
    apply (hD ρ ?_).mp hzero
    apply (mem_Rect hre him ρ).mpr
    simpa [z, w] using (show α ≤ ρ.re ∧ ρ.re ≤ β ∧ H ≤ ρ.im ∧ ρ.im ≤ T from
      ⟨hρα.le, hρβ.le, hρH.le, hρT⟩)
  have he := Complex.weightedLogExcess_eq_rectangleContour hre him hf hborder D hD hDsub
  have hcap := detectorLogExcessOnZetaWindow_le_finite X D H T α hactive
  have he' : detectorLogExcessFinite X D α =
      (RectangleIntegral' (fun s => (s - ((α : ℂ) + (H : ℂ) * I)) * logDeriv (zetaDetector X) s)
        ((α : ℂ) + (H : ℂ) * I) ((β : ℂ) + (T : ℂ) * I)).re := by
    simpa [detectorLogExcessFinite, z, w] using he
  exact hcap.trans he'.le

end RiemannResearch.Analysis.ActualZeroOrdinate
