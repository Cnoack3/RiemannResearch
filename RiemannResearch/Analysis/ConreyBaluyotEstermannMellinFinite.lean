/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinShift
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinCollisionShift
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Finite coefficient assembly of the conditional global Estermann shift

The moduli and damping parameters may vary over an arbitrary finite support;
coefficients may be complex and need not factor. Every residue term retains
its coefficient and the remaining integral contains the exact finite sum.
Absolute integrability on the new line is proved from the supplied tail
bounds before the finite sum is moved inside the integral.

For the actual mollifier, index by pairs (h,k) and both signs. The theorem
reducedRationalTwist_isUnit in ConreyBaluyotRationalTwist supplies the unit
classes of H and -H for K = k/gcd(h,k). The actual signed Gaussian correction
belongs to the existing moment theorem and is not absorbed or discarded here.

Source: the finite assembly after the Mellin shift in
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
Section 3.3, pp. 116–117:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the assembly strategy. The tail bounds remain open
analytic obligations; this module does not furnish a uniform moment bound.
-/

open Complex MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Conditional finite assembly across possibly different reduced moduli.
All complex coefficients are retained, and the finite sum is inside the remaining integral. -/
theorem finite_estermannDampedSeries_eq_residues_add_mellinIntegral_of_tail_bound
    {ι : Type*} (S : Finset ι) (K : ι → ℕ) [∀ i, NeZero (K i)]
    (h : ∀ i, (ZMod (K i))ˣ) (A w : ι → ℂ) {α β : ℂ}
    (hα : α.re < 1) (hβ : β.re < 1) (hne : α ≠ β)
    (hw : ∀ i ∈ S, 0 < (w i).im)
    {a b : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hbα : 1 < b + α.re) (hbβ : 1 < b + β.re)
    (B T₀ : ι → ℝ)
    (hbound : ∀ i ∈ S, ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ i ≤ |t| →
      ‖estermannMellinKernel (h i : ZMod (K i)) α β (-2 * (Real.pi : ℂ) * I * w i)
        ((r : ℂ) + t * I)‖ ≤ B i * (1 + t ^ 2)⁻¹) :
    (∑ i ∈ S, A i * estermannDampedSeries (h i : ZMod (K i)) α β (w i)) =
      (∑ i ∈ S, A i * estermannMellinResidueSum (h i : ZMod (K i)) α β
        (-2 * (Real.pi : ℂ) * I * w i)) +
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, ∑ i ∈ S, A i *
          estermannMellinKernel (h i : ZMod (K i)) α β
            (-2 * (Real.pi : ℂ) * I * w i) ((a : ℂ) + I * t) := by
  classical
  have hab : a ≤ b := by linarith
  have hint (i : ι) (hi : i ∈ S) :
      Integrable (fun t : ℝ => A i *
        estermannMellinKernel (h i : ZMod (K i)) α β
          (-2 * (Real.pi : ℂ) * I * w i) ((a : ℂ) + I * t)) := by
    have hlam : 0 < (-2 * (Real.pi : ℂ) * I * w i).re := by
      have he : (-2 * (Real.pi : ℂ) * I * w i).re = 2 * Real.pi * (w i).im := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [he]
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (hw i hi)
    have hlam0 : -2 * (Real.pi : ℂ) * I * w i ≠ 0 := by
      intro he
      rw [he] at hlam
      norm_num at hlam
    apply Integrable.const_mul
    apply integrable_estermannMellinKernel_negative_of_tail_bound
      (B := B i) (T₀ := T₀ i) (h i : ZMod (K i)) α β hα hβ hlam0 ha ha0
    intro t ht
    simpa only [mul_comm I] using hbound i hi a ⟨le_rfl, hab⟩ t ht
  calc
    _ = ∑ i ∈ S, A i *
        (estermannMellinResidueSum (h i : ZMod (K i)) α β
          (-2 * (Real.pi : ℂ) * I * w i) +
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ, estermannMellinKernel (h i : ZMod (K i)) α β
              (-2 * (Real.pi : ℂ) * I * w i) ((a : ℂ) + I * t)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [estermannDampedSeries_eq_residues_add_mellinIntegral_of_tail_bound
        (h i) hα hβ hne (hw i hi) ha ha0 hbα hbβ (hbound i hi)]
    _ = _ := by
      rw [integral_finsetSum S hint]
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
      ring

/-- Conditional collision assembly across possibly different reduced moduli.
All complex coefficients are retained, and the finite sum is inside the remaining integral. -/
theorem finite_estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_tail_bound
    {ι : Type*} (S : Finset ι) (K : ι → ℕ) [∀ i, NeZero (K i)]
    (h : ∀ i, (ZMod (K i))ˣ) (A w : ι → ℂ)
    (hw : ∀ i ∈ S, 0 < (w i).im)
    {a b : ℝ} (ha : -1 < a) (ha0 : a < 0)
    (hb : 1 < b)
    (B T₀ : ι → ℝ)
    (hbound : ∀ i ∈ S, ∀ r ∈ Icc a b, ∀ t : ℝ, T₀ i ≤ |t| →
      ‖estermannMellinKernel (h i : ZMod (K i)) 0 0 (-2 * (Real.pi : ℂ) * I * w i)
        ((r : ℂ) + t * I)‖ ≤ B i * (1 + t ^ 2)⁻¹) :
    (∑ i ∈ S, A i * estermannDampedSeries (h i : ZMod (K i)) 0 0 (w i)) =
      (∑ i ∈ S, A i * estermannMellinCollisionResidueSum (h i : ZMod (K i))
        (-2 * (Real.pi : ℂ) * I * w i)) +
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, ∑ i ∈ S, A i *
          estermannMellinKernel (h i : ZMod (K i)) 0 0
            (-2 * (Real.pi : ℂ) * I * w i) ((a : ℂ) + I * t) := by
  classical
  have hab : a ≤ b := by linarith
  have hint (i : ι) (hi : i ∈ S) :
      Integrable (fun t : ℝ => A i *
        estermannMellinKernel (h i : ZMod (K i)) 0 0
          (-2 * (Real.pi : ℂ) * I * w i) ((a : ℂ) + I * t)) := by
    have hlam : 0 < (-2 * (Real.pi : ℂ) * I * w i).re := by
      have he : (-2 * (Real.pi : ℂ) * I * w i).re = 2 * Real.pi * (w i).im := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [he]
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (hw i hi)
    have hlam0 : -2 * (Real.pi : ℂ) * I * w i ≠ 0 := by
      intro he
      rw [he] at hlam
      norm_num at hlam
    apply Integrable.const_mul
    apply integrable_estermannMellinKernel_negative_of_tail_bound
      (B := B i) (T₀ := T₀ i) (h i : ZMod (K i)) 0 0 (by norm_num) (by norm_num) hlam0 ha ha0
    intro t ht
    simpa only [mul_comm I] using hbound i hi a ⟨le_rfl, hab⟩ t ht
  calc
    _ = ∑ i ∈ S, A i *
        (estermannMellinCollisionResidueSum (h i : ZMod (K i))
          (-2 * (Real.pi : ℂ) * I * w i) +
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ, estermannMellinKernel (h i : ZMod (K i)) 0 0
              (-2 * (Real.pi : ℂ) * I * w i) ((a : ℂ) + I * t)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [estermannDampedSeries_diagonal_eq_residues_add_mellinIntegral_of_tail_bound
        (h i) (hw i hi) ha ha0 hb (hbound i hi)]
    _ = _ := by
      rw [integral_finsetSum S hint]
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
      ring


end RiemannResearch.Analysis.ConreyBaluyot
