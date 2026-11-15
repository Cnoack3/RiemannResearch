/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ComplexLittlewoodBoundary
import RiemannResearch.RH.WeilExplicitFormula.Analytic.RectangleLogDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Littlewood's exact weighted zero identity

Assemble the repository's proved signed boundary identity and weighted
argument principle. The weight is s minus the lower-left corner, so its real
part is Re(s) minus the left boundary. The compatible logarithm lifts retain
all four signed boundary terms.

Provenance: this proof assembles ComplexLittlewoodBoundary (whose source
reference supports the boundary identity) and RectangleLogDeriv. The bottom
lift is principal-normalized at the right corner; the top normalization
follows when the entire right side lies in the complex slit plane.
-/

noncomputable section
open Complex Set
open scoped BigOperators
namespace Complex

/-- The full signed boundary equals the weighted analytic zero mass for compatible logarithm lifts. -/
theorem exists_logRectangleBoundary_eq_weighted_zeros
    {F : ℂ → ℂ} {a b H T : ℝ}
    (hab : a ≤ b) (hHT : H ≤ T)
    (hf : AnalyticOnNhd ℂ F
      (Rectangle ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I)))
    (hborder : ∀ s ∈ RectangleBorder
      ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I), F s ≠ 0) :
    ∃ (Z : Finset ℂ) (B U : ℝ → ℂ),
      (∀ s, s ∈ Z ↔ s ∈ Rectangle
        ((a : ℂ) + (H : ℂ) * I) ((b : ℂ) + (T : ℂ) * I) ∧ F s = 0) ∧
      Continuous B ∧ Continuous U ∧
      (∀ x ∈ Icc a b, exp (B x) = F ((x : ℂ) + (H : ℂ) * I)) ∧
      (∀ x ∈ Icc a b, exp (U x) = F ((x : ℂ) + (T : ℂ) * I)) ∧
      logRectangleBoundary F (fun x => (B x).im) (fun x => (U x).im) a b H T =
        2 * Real.pi * ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) * (ρ.re - a) ∧
      B b = log (F ((b : ℂ) + (H : ℂ) * I)) ∧
      ((∀ t ∈ Icc H T, F ((b : ℂ) + (t : ℂ) * I) ∈ slitPlane) →
        U b = log (F ((b : ℂ) + (T : ℂ) * I))) := by
  classical
  let z : ℂ := (a : ℂ) + (H : ℂ) * I
  let w : ℂ := (b : ℂ) + (T : ℂ) * I
  have hre : z.re ≤ w.re := by simpa [z, w] using hab
  have him : z.im ≤ w.im := by simpa [z, w] using hHT
  have hzBorder : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hf
    (rectangleBorder_subset_rectangle z w hzBorder) (hborder z hzBorder)
  let Z := hfin.toFinset
  have hZexact : ∀ s, s ∈ Z ↔ s ∈ Rectangle z w ∧ F s = 0 := by
    intro s
    simp [Z, Set.Finite.mem_toFinset, z, w]
  have hZ : ∀ s ∈ Rectangle z w, F s = 0 ↔ s ∈ Z := by
    intro s hs
    rw [hZexact]
    exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  have hZsub : (Z : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    exact ((hZexact s).mp hs).1
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => s - z) (Rectangle z w) :=
    fun s _ => analyticAt_id.sub analyticAt_const
  have hres := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv
    hre him hf hg hborder Z hZ hZsub
  have hreal : (RectangleIntegral' (fun s => (s - z) * logDeriv F s) z w).re =
      ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) * (ρ.re - a) := by
    have he := congrArg Complex.re hres
    simpa [Complex.mul_re, z] using he
  obtain ⟨B, U, hBc, hUc, hBe, hUe, hboundary, hBb, hUb⟩ :=
    exists_logRectangleBoundary_eq_contour hab hHT hf hborder
  refine ⟨Z, B, U, hZexact, hBc, hUc, hBe, hUe, ?_, hBb, hUb⟩
  have heq : logRectangleBoundary F (fun x => (B x).im) (fun x => (U x).im)
      a b H T / (2 * Real.pi) =
        ∑ ρ ∈ Z, (analyticOrderNatAt F ρ : ℝ) * (ρ.re - a) :=
    hboundary.symm.trans hreal
  have hh := (div_eq_iff (by positivity : (2 * Real.pi : ℝ) ≠ 0)).mp heq
  nlinarith [hh]
end Complex
