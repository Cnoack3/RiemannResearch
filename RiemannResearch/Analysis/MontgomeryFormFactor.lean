/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryCauchyGram
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.Tactic.Positivity

/-! # Montgomery's raw form factor on actual zero copies

Source: Montgomery (1973), https://websites.umich.edu/~hlm/paircor1.pdf,
and user-provided Montgomery handoff, Sections 1 and 4. No RH is imposed:
the index type is ActualZeroOrdinate.Copies, including every multiplicity and
every nontrivial zero in the positive-height cutoff. The generic Cauchy Gram
proves positivity; no limiting pair-correlation theorem is asserted here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open MontgomeryPoisson ZeroOrdinate ActualZeroOrdinate
variable {ι : Type*} [Fintype ι]

def pairSum (t : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ i, ∑ j, (cauchyWeight (t i-t j) : ℂ) * phase u (t i-t j)

theorem pairSum_eq_kernel (t : ι → ℝ) (u : ℝ) :
    pairSum t u = kernelQuadratic t (fun i => phase u (t i)) := by
  unfold pairSum kernelQuadratic
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [phase_mul_conj, mul_comm]

theorem pairSum_nonneg (t : ι → ℝ) (u : ℝ) : 0 ≤ (pairSum t u).re := by
  rw [pairSum_eq_kernel]
  exact kernelQuadratic_nonneg _ _

theorem pairSum_even (t : ι → ℝ) (u : ℝ) : pairSum t (-u) = pairSum t u := by
  unfold pairSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hw : cauchyWeight (t j-t i) = cauchyWeight (t i-t j) := by
    unfold cauchyWeight
    congr 2
    ring
  rw [hw]
  congr 1
  unfold phase
  congr 1
  push_cast
  ring

theorem pairSum_real (t : ι → ℝ) (u : ℝ) : (pairSum t u).im = 0 := by
  rw [pairSum_eq_kernel, ← finite_gram_complex]
  have h := integral_im (finite_gram_integrable t (fun i => phase u (t i)))
  change (∫ s : ℝ, (((Real.exp (-2*|s|) *
    ‖signal t (fun i => phase u (t i)) s‖^2 : ℝ) : ℂ)).im) =
    (∫ s : ℝ, ((Real.exp (-2*|s|) *
    ‖signal t (fun i => phase u (t i)) s‖^2 : ℝ) : ℂ)).im at h
  simpa only [Complex.ofReal_im, integral_zero] using h.symm

theorem pairSum_gram (t : ι → ℝ) (u : ℝ) :
    (pairSum t u).re =
      ∫ s : ℝ, Real.exp (-2*|s|) * ‖∑ i, phase (u+s) (t i)‖^2 := by
  rw [pairSum_eq_kernel, ← finite_gram]
  simp only [signal, phase_add]

theorem indexed_diagonal (t : ι → ℝ) (u : ℝ) :
    (∑ i, (cauchyWeight (t i-t i) : ℂ) * phase u (t i-t i)) =
      (Fintype.card ι : ℂ) := by
  simp [cauchyWeight, phase]

/-- All actual positive-height zero copies, including off-line zeros. -/
def formFactor (T α : ℝ) : ℝ :=
  (pairSum (copyOrdinate T) (α*Real.log T)).re / (T*Real.log T/(2*Real.pi))

theorem formFactor_nonneg {T : ℝ} (hT : 1 < T) (α : ℝ) :
    0 ≤ formFactor T α := by
  unfold formFactor
  apply div_nonneg (pairSum_nonneg _ _)
  have ht : 0 < T := lt_trans zero_lt_one hT
  have hl : 0 < Real.log T := Real.log_pos hT
  positivity

theorem formFactor_even (T α : ℝ) : formFactor T (-α) = formFactor T α := by
  unfold formFactor
  rw [neg_mul, pairSum_even]

theorem formFactor_gram (T α : ℝ) :
    formFactor T α =
      (∫ s : ℝ, Real.exp (-2*|s|) *
        ‖∑ i : Copies T, phase (α*Real.log T+s) (copyOrdinate T i)‖^2) /
        (T*Real.log T/(2*Real.pi)) := by
  rw [formFactor, pairSum_gram]

theorem actual_indexed_diagonal (T α : ℝ) :
    (∑ i : Copies T,
      (cauchyWeight (copyOrdinate T i-copyOrdinate T i) : ℂ) *
      phase (α*Real.log T) (copyOrdinate T i-copyOrdinate T i)) =
      (Zeta23.Ncount 0 T : ℂ) := by
  rw [indexed_diagonal, card_copies]

end RiemannResearch.Analysis.MontgomeryFormFactor
