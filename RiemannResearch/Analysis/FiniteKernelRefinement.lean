import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Exact finite signed-kernel reconstruction

Source: user-provided argument, `RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`,
Section 39.1.  This file formalizes the finite-sum algebra of reconstruction,
including its exponential centering term.  The kernel-refinement identity and
its exponential moment identity are explicit hypotheses of the application
theorem.  No autocorrelation integral or prime-power cutoff is proved here.
-/

noncomputable section

namespace RiemannResearch.Analysis

open scoped BigOperators

variable {ι κ : Type*}

/-- A finite weighted sum of translates of a kernel. -/
def finiteAtomicConvolution (p : Finset κ) (w b : κ → ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ q ∈ p, w q * g (x - b q)

/-- The double mask acting on a correlation kernel. -/
def doubleRefinement (s : Finset ι) (α t : ι → ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ s, ∑ l ∈ s, α k * α l * g (x + t k - t l)

theorem finiteAtomicConvolution_doubleRefinement
    (p : Finset κ) (w b : κ → ℝ) (s : Finset ι) (α t : ι → ℝ)
    (g : ℝ → ℝ) (x : ℝ) :
    finiteAtomicConvolution p w b (doubleRefinement s α t g) x =
      doubleRefinement s α t (finiteAtomicConvolution p w b g) x := by
  classical
  simp only [finiteAtomicConvolution, doubleRefinement, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro q hq
  have heq : x - b q + t k - t l = x + t k - t l - b q := by ring
  rw [heq]
  ring

theorem doubleRefinement_sub_smul (s : Finset ι) (α t : ι → ℝ)
    (f g : ℝ → ℝ) (m x : ℝ) :
    doubleRefinement s α t (fun y => f y - m * g y) x =
      doubleRefinement s α t f x - m * doubleRefinement s α t g x := by
  classical
  simp only [doubleRefinement, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem doubleRefinement_exp_half (s : Finset ι) (α t : ι → ℝ) (x : ℝ) :
    doubleRefinement s α t (fun y => Real.exp (y / 2)) x =
      Real.exp (x / 2) * (∑ k ∈ s, α k * Real.exp (t k / 2)) *
        (∑ l ∈ s, α l * Real.exp (-(t l) / 2)) := by
  classical
  simp only [doubleRefinement, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have heq : (x + t k - t l) / 2 = x / 2 + t k / 2 + -(t l) / 2 := by ring
  rw [heq, Real.exp_add, Real.exp_add]
  ring

/-- Exact reconstruction of the centered finite atomic discrepancy.
The two displayed hypotheses are the analytic kernel and moment interfaces;
the conclusion preserves all signed terms instead of taking absolute values. -/
theorem finiteCenteredDiscrepancy_refinement
    (p : Finset κ) (w b : κ → ℝ) (s : Finset ι) (α t : ι → ℝ)
    (gH gh : ℝ → ℝ) (mH mh : ℝ)
    (hkernel : gH = doubleRefinement s α t gh)
    (hmoment : mH = mh * (∑ k ∈ s, α k * Real.exp (t k / 2)) *
      (∑ l ∈ s, α l * Real.exp (-(t l) / 2))) (x : ℝ) :
    finiteAtomicConvolution p w b gH x - mH * Real.exp (x / 2) =
      doubleRefinement s α t
        (fun y => finiteAtomicConvolution p w b gh y - mh * Real.exp (y / 2)) x := by
  rw [hkernel, finiteAtomicConvolution_doubleRefinement, doubleRefinement_sub_smul,
    doubleRefinement_exp_half, hmoment]
  ring

/-- Taking absolute values incurs the square of the total mask mass.
For the source's coarse-to-fine mask, this is the factor `N²`; the theorem
does not supply the signed cancellation needed for a better estimate. -/
theorem abs_doubleRefinement_le_mass_sq
    (s : Finset ι) (α t : ι → ℝ) (g : ℝ → ℝ) (x B : ℝ)
    (hα : ∀ k ∈ s, 0 ≤ α k)
    (hg : ∀ k ∈ s, ∀ l ∈ s, |g (x + t k - t l)| ≤ B) :
    |doubleRefinement s α t g x| ≤ B * (∑ k ∈ s, α k) ^ 2 := by
  classical
  unfold doubleRefinement
  calc
    |∑ k ∈ s, ∑ l ∈ s, α k * α l * g (x + t k - t l)| ≤
        ∑ k ∈ s, |∑ l ∈ s, α k * α l * g (x + t k - t l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ s, ∑ l ∈ s, |α k * α l * g (x + t k - t l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ s, ∑ l ∈ s, α k * α l * |g (x + t k - t l)| := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [abs_mul, abs_mul, abs_of_nonneg (hα k hk), abs_of_nonneg (hα l hl)]
    _ ≤ ∑ k ∈ s, ∑ l ∈ s, α k * α l * B := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (hg k hk l hl)
        (mul_nonneg (hα k hk) (hα l hl))
    _ = B * (∑ k ∈ s, α k) ^ 2 := by
      rw [pow_two]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring

end RiemannResearch.Analysis
