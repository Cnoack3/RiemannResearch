/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotDyadicHorizontalArgument
import RiemannResearch.RH.WeilExplicitFormula.Analytic.RectangleLogDeriv
import Mathlib.Tactic.FunProp

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Weighted argument principle for the actual mollified zeta function on a
positive-height rectangle.  The boundary nonvanishing hypothesis is explicit;
the finite zero set includes zeros contributed by the mollifier. -/
theorem mollifiedZeta_rectangle_weighted_zero_identity
    (σ y ε : ℝ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hzpos : 0 < z.im)
    (hborder : ∀ s ∈ RectangleBorder z w, mollifiedZeta σ y ε s ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ s ∈ Rectangle z w, mollifiedZeta σ y ε s = 0 ↔ s ∈ Z) ∧
      (Z : Set ℂ) ⊆ Rectangle z w ∧
      (RectangleIntegral' (fun s => (s - (z.re : ℂ)) *
        logDeriv (mollifiedZeta σ y ε) s) z w).re =
        ∑ ρ ∈ Z, (analyticOrderNatAt (mollifiedZeta σ y ε) ρ : ℝ) *
          (ρ.re - z.re) := by
  classical
  let F := mollifiedZeta σ y ε
  have hf : AnalyticOnNhd ℂ F (Rectangle z w) := by
    intro s hs
    have hsi : z.im ≤ s.im := by
      have hi := hs.2
      rw [Set.uIcc_of_le him] at hi
      exact hi.1
    have hspos : 0 < s.im := lt_of_lt_of_le hzpos hsi
    have hsne : s ≠ 1 := by
      intro he
      have hh := congrArg Complex.im he
      simp at hh
      linarith
    exact analyticAt_mollifiedZeta σ y ε hsne
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => s - (z.re : ℂ))
      (Rectangle z w) := by
    intro s hs
    exact analyticAt_id.sub analyticAt_const
  have hzBorder : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hf
    (rectangleBorder_subset_rectangle z w hzBorder) (hborder z hzBorder)
  let Z := hfin.toFinset
  have hZ : ∀ s ∈ Rectangle z w, F s = 0 ↔ s ∈ Z := by
    intro s hs
    simp [Z, Set.Finite.mem_toFinset, hs]
  have hZsub : (Z : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    exact ((Set.Finite.mem_toFinset _).mp hs).1
  have hres := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    hre him hf hg hborder Z hZ hZsub
  refine ⟨Z, hZ, hZsub, ?_⟩
  have he := congrArg Complex.re hres
  simpa [Complex.mul_re] using he

end RiemannResearch.Analysis.ConreyBaluyot
