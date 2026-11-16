/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.HurwitzEulerMaclaurin
import RiemannResearch.Analysis.ConreyBaluyotEstermannHurwitzGrowth
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinCollisionShift
import Mathlib.Tactic.Choose
/-!
# Actual Estermann growth and global damped Mellin shifts

The actual quadratic Hurwitz bounds supply quartic Estermann growth, uniform
over numerator classes at each fixed positive modulus. Combining this with
the proved Gamma/damping estimate discharges the analytic provider in both
the distinct-pole and double-pole collision contour shifts.

Constants may depend on the modulus, shifts, strip and positive damping.
No cofinal uniform mollified-zeta moment or Selberg-density claim is made here.

Source: Baluyot, On the Zeros of Riemann's Zeta-function (2017),
Lemma 3.1.3, pp. 96–97 (contour setting):
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
Hurwitz bounds use the corrected Euler--Maclaurin formula, NIST DLMF 25.11.6:
https://dlmf.nist.gov/25.11.E6
-/

open Complex Set
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Actual quartic growth, uniform over all numerator classes at fixed modulus.
Only the two shifted left edges must lie in the Euler--Maclaurin half-plane. -/
theorem exists_estermann_shifted_strip_bound {K : ℕ} [NeZero K]
    (α β : ℂ) {a b : ℝ} (hα : -1 < a + α.re) (hβ : -1 < a + β.re) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 0 < T₀ ∧ ∀ h : ZMod K,
      ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
        ‖estermann h ((r : ℂ) + t * I + α) ((r : ℂ) + t * I + β)‖ ≤ C * |t| ^ 4 := by
  classical
  choose C hC hCb using fun j : ZMod K =>
    HurwitzEulerMaclaurin.exists_hurwitzZeta_shifted_strip_bound
      (ZMod.toAddCircle j) α (b := b) hα
  choose D hD hDb using fun j : ZMod K =>
    HurwitzEulerMaclaurin.exists_hurwitzZeta_shifted_strip_bound
      (ZMod.toAddCircle j) β (b := b) hβ
  let T₀ : ℝ := max (2 * (1 + |α.im|)) (2 * (1 + |β.im|))
  have hCs : 0 ≤ ∑ j, C j := Finset.sum_nonneg (fun j _ => (hC j).le)
  have hDs : 0 ≤ ∑ j, D j := Finset.sum_nonneg (fun j _ => (hD j).le)
  refine ⟨(K : ℝ) ^ (-2 * a - α.re - β.re) * (∑ j, C j) * (∑ j, D j),
    T₀, by positivity, ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity : 0 < 2 * (1 + |α.im|)) (le_max_left _ _)
  · intro h r hr t ht
    exact norm_estermann_shifted_le_of_hurwitz_polynomial_bounds h α β 2 2 C D
      (fun j r hr t ht => hCb j r hr t ((le_max_left _ _).trans ht))
      (fun j r hr t ht => hDb j r hr t ((le_max_right _ _).trans ht)) r hr t ht

/-- The actual Cauchy tail provider for fixed positive damping. -/
theorem exists_estermannMellinKernel_tail_bound {K : ℕ} [NeZero K]
    (h : ZMod K) (α β : ℂ) {lam : ℂ} (hlam : 0 < lam.re)
    {a b : ℝ} (ha : -1 < a) (hα : -1 < a + α.re) (hβ : -1 < a + β.re) :
    ∃ B T₀ : ℝ, 0 ≤ B ∧ 1 ≤ T₀ ∧
      ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ ≤ |t| →
        ‖estermannMellinKernel h α β lam ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹ := by
  obtain ⟨C, T, hC, _, hE⟩ :=
    exists_estermann_shifted_strip_bound (K := K) α β (b := b) hα hβ
  obtain ⟨B, hB, htail⟩ :=
    exists_estermannMellinKernel_tail_bound_of_polynomial_growth
      h α β hlam ha 4 hC (hE h)
  exact ⟨B, max 1 T, hB, le_max_left _ _, htail⟩

/-- The global distinct-pole Mellin shift with the growth hypothesis discharged. -/
theorem estermannDampedSeries_eq_residues_add_mellinIntegral
    {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) {α β w : ℂ}
    (hα : α.re < 1) (hβ : β.re < 1) (hne : α ≠ β) (hw : 0 < w.im)
    {a b : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (haα : -1 < a + α.re) (haβ : -1 < a + β.re)
    (hbα : 1 < b + α.re) (hbβ : 1 < b + β.re) :
    estermannDampedSeries (h : ZMod K) α β w =
      estermannMellinResidueSum (h : ZMod K) α β (-2 * (Real.pi : ℂ) * I * w) +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, estermannMellinKernel (h : ZMod K) α β
            (-2 * (Real.pi : ℂ) * I * w) ((a : ℂ) + I * t) := by
  obtain ⟨C, T, hC, _, hE⟩ :=
    exists_estermann_shifted_strip_bound (K := K) α β (b := b) haα haβ
  exact estermannDampedSeries_eq_residues_add_mellinIntegral_of_polynomial_growth
    h hα hβ hne hw ha ha0 hbα hbβ 4 hC (hE h)

/-- The global double-pole collision shift with no analytic provider hypothesis. -/
theorem estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral
    {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) {w : ℂ} (hw : 0 < w.im)
    {a b : ℝ} (ha : -1 < a) (ha0 : a < 0) (hb : 1 < b) :
    estermannDampedSeries (h : ZMod K) 0 0 w =
      estermannMellinCollisionResidueSum (h : ZMod K) (-2 * (Real.pi : ℂ) * I * w) +
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ, estermannMellinKernel (h : ZMod K) 0 0
            (-2 * (Real.pi : ℂ) * I * w) ((a : ℂ) + I * t) := by
  obtain ⟨C, T, hC, _, hE⟩ := exists_estermann_shifted_strip_bound (K := K) 0 0
    (b := b) (by simpa using ha) (by simpa using ha)
  apply estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_polynomial_growth
    h hw ha ha0 hb 4 hC
  simpa only [add_zero] using hE (h : ZMod K)

end RiemannResearch.Analysis.ConreyBaluyot
