/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic.FunProp

/-!
# Strict-to-inclusive transfer for published zero-density estimates

Baluyot, "On the Zeros of Riemann's Zeta-function" (2017), Theorem 1.2.1:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The source parameter is theta = a/2. Its range is 0 < a < 8 / 7.
This file proves the previously missing count-convention interface, including
the critical-line endpoint using the unconditional total-count theorem.
It does not prove the source's mollified second moment or its density bound.
Actual analytic multiplicities, including threshold copies, are retained.
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem rightInclusiveCount_le_rightStrictTail_of_lt
    (T : ℝ) {τ σ : ℝ} (h : τ < σ) :
    rightInclusiveCount T σ ≤ rightStrictTail T (τ - 1 / 2) := by
  apply realSum_mono
  intro ρ hρ
  by_cases hs : σ ≤ ρ.re
  · have ht : 1 / 2 + (τ - 1 / 2) < ρ.re := by linarith
    simp only [if_pos hs, if_pos ht, le_refl]
  · simp only [if_neg hs]
    split_ifs <;> norm_num

/-- Left continuity of a majorant closes the count threshold without removing
copies lying exactly on it. No continuity of the zero count is assumed. -/
theorem rightInclusiveCount_le_of_continuous_strict_majorant
    (T σ : ℝ) (hσ : 1 / 2 < σ) {F : ℝ → ℝ}
    (hF : ContinuousAt F σ)
    (hstrict : ∀ τ ∈ Ioo (1 / 2 : ℝ) σ,
      rightStrictTail T (τ - 1 / 2) ≤ F τ) :
    rightInclusiveCount T σ ≤ F σ := by
  have hlim : Tendsto F (𝓝[<] σ) (𝓝 (F σ)) :=
    hF.continuousWithinAt.tendsto
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hσ)] with τ hτ hh
  exact (rightInclusiveCount_le_rightStrictTail_of_lt T hτ).trans
    (hstrict τ ⟨hh, hτ⟩)

/-- Above the critical line, the strict and inclusive source bounds have the
same exponent, constant and height. -/
theorem rightInclusiveCount_le_of_strict_selberg
    (T C a σ : ℝ) (hT : 0 < T) (hσ : σ ∈ Ioc (1 / 2 : ℝ) 1)
    (hstrict : ∀ τ ∈ Ioc (1 / 2 : ℝ) 1,
      rightStrictTail T (τ - 1 / 2) ≤ C * T ^ (1 - a * (τ - 1 / 2)) * Real.log T) :
    rightInclusiveCount T σ ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  simp_rw [mul_assoc, selberg_power_kernel_eq_exp T a _ hT, mul_assoc] at hstrict ⊢
  apply rightInclusiveCount_le_of_continuous_strict_majorant T σ hσ.1
  · fun_prop
  · intro τ hτ
    exact hstrict τ ⟨hτ.1, hτ.2.le.trans hσ.2⟩

/-- The endpoint sigma=1 / 2 needs the total-count bound. The constant is enlarged
once, uniformly in sigma, and no boundary-zero assumption is introduced. -/
theorem selbergDensityBound_of_strict_and_count
    (T C D a : ℝ) (hT : 1 < T)
    (hcount : (Ncount 0 T : ℝ) ≤ D * T * Real.log T)
    (hstrict : ∀ σ ∈ Ioc (1 / 2 : ℝ) 1,
      rightStrictTail T (σ - 1 / 2) ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T) :
    SelbergDensityBound T (max C D) a := by
  intro σ hσ
  by_cases heq : σ = 1 / 2
  · subst σ
    simp only [sub_self, mul_zero, sub_zero, Real.rpow_one]
    exact (rightInclusiveCount_le_count T (1 / 2)).trans
      (hcount.trans (by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C D) (by linarith))
          (Real.log_nonneg hT.le)))
  · have hs : 1 / 2 < σ := lt_of_le_of_ne hσ.1 (Ne.symm heq)
    apply (rightInclusiveCount_le_of_strict_selberg T C a σ
      (by linarith) ⟨hs, hσ.2⟩ hstrict).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C D) (Real.rpow_nonneg (by linarith) _))
      (Real.log_nonneg hT.le)

/-- Exact equivalence between the conventional strict source statement and
the repository's uniform inclusive statement, with independently chosen
constants and thresholds. This proves an interface, not the density theorem. -/
theorem uniformSelbergDensity_iff_strict (a : ℝ) :
    UniformSelbergDensity a ↔
      ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        ∀ σ ∈ Ioc (1 / 2 : ℝ) 1,
          rightStrictTail T (σ - 1 / 2) ≤ C * T ^ (1 - a * (σ - 1 / 2)) * Real.log T := by
  constructor
  · rintro ⟨C, T₀, hC, hT₀, hD⟩
    refine ⟨C, T₀, hC, hT₀, ?_⟩
    intro T hT σ hσ
    have ht := rightStrictTail_le_inclusive T (σ - 1 / 2)
    have heq : (1 / 2 : ℝ) + (σ - 1 / 2) = σ := by ring
    rw [heq] at ht
    exact ht.trans (hD T hT σ ⟨hσ.1.le, hσ.2⟩)
  · rintro ⟨C, T₀, hC, hT₀, hstrict⟩
    obtain ⟨D, hD, hcount⟩ := exists_count_le_height_log
    refine ⟨max C D, max T₀ 9, le_trans hC (le_max_left _ _),
      lt_of_lt_of_le hT₀ (le_max_left _ _), ?_⟩
    intro T hT
    exact selbergDensityBound_of_strict_and_count T C D a
      (lt_of_lt_of_le hT₀ ((le_max_left _ _).trans hT))
      (hcount T ((le_max_right _ _).trans hT))
      (hstrict T ((le_max_left _ _).trans hT))

/-- Both the factor of two and the excluded endpoint are part of the source
interface. Constants may depend on the selected theta. -/
theorem conreyBaluyotDensity_iff_strict_source :
    ConreyBaluyotDensityHypothesis ↔
      ∀ θ : ℝ, 0 < θ → θ < 4 / 7 →
        ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
          ∀ σ ∈ Ioc (1 / 2 : ℝ) 1,
            rightStrictTail T (σ - 1 / 2) ≤ C * T ^ (1 + θ * (1 - 2 * σ)) * Real.log T := by
  constructor
  · intro h θ hθ hθ'
    obtain ⟨C, T₀, hC, hT₀, hD⟩ :=
      (uniformSelbergDensity_iff_strict (2 * θ)).mp
        (h (2 * θ) (by linarith) (by linarith))
    refine ⟨C, T₀, hC, hT₀, ?_⟩
    intro T hT σ hσ
    rw [show 1 + θ * (1 - 2 * σ) = 1 - (2 * θ) * (σ - 1 / 2) by ring]
    exact hD T hT σ hσ
  · intro h a ha ha'
    apply (uniformSelbergDensity_iff_strict a).mpr
    obtain ⟨C, T₀, hC, hT₀, hD⟩ := h (a / 2) (by linarith) (by linarith)
    refine ⟨C, T₀, hC, hT₀, ?_⟩
    intro T hT σ hσ
    rw [show 1 - a * (σ - 1 / 2) = 1 + (a / 2) * (1 - 2 * σ) by ring]
    exact hD T hT σ hσ

end RiemannResearch.Analysis.ActualZeroOrdinate
