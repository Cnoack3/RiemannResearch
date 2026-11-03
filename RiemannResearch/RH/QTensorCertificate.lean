/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteTensorTail
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Complete arithmetic tensor certificates and their conditional RH consumer

Source: Prime Tensor CRT RH Research Project (2 November 2026), section 6.
All rows are actual normalized divisor-wavelet vectors and all columns are
actual Q residue vectors. The certificate includes every omitted coordinate.
The small-certificate premise in the RH consumer is OPEN; no quantitative
arithmetic provider, nor the published RH-to-density theorem, is asserted.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTensorCertificate
open ZetaTwoHilbert ZetaTwoProbability QDivisorHilbert QCovarianceInverse
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteTensorTail
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def rows (r : κ → ℕ+) : κ → QHilbert := fun k => normalizedDivisorWavelet (r k)

theorem rows_orthonormal (r : κ → ℕ+) (hr : Function.Injective r) :
    Orthonormal ℝ (rows r) :=
  normalizedDivisorWavelet_orthonormal.comp r hr

theorem one_mem_rows (r : κ → ℕ+) (hone : ∃ k, r k = 1) :
    qOne ∈ synthesisSpan (rows r) := by
  obtain ⟨k, hk⟩ := hone
  have he : rows r k = qOne := by
    simp [rows, hk, normalizedDivisorWavelet, divisorWavelet_one, qJordanTwo]
  rw [← he]
  exact Submodule.subset_span ⟨k, rfl⟩

def certificate (r : κ → ℕ+) (d : ι → ℕ) (c : ι → ℝ) : ℝ :=
  (∑ k, (inner ℝ (rows r k) (qOne - qSynthesis d c))^2) +
  (∑ i, |c i| * ‖tailMap (rows r) (qResidue (d i))‖)^2

theorem error_le_certificate (r : κ → ℕ+) (hr : Function.Injective r)
    (hone : ∃ k, r k = 1) (d : ι → ℕ) (c : ι → ℝ) :
    ‖qOne - qSynthesis d c‖^2 ≤ certificate r d c := by
  simpa only [certificate, qSynthesis, Fintype.linearCombination_apply] using
    column_certificate (rows r) (rows_orthonormal r hr)
      (fun i => qResidue (d i)) c qOne (one_mem_rows r hone)

theorem tail_norm_eq_sqrt (r : κ → ℕ+) (hr : Function.Injective r) (d : ℕ) :
    ‖tailMap (rows r) (qResidue d)‖ =
      Real.sqrt (‖qResidue d‖^2 -
        ∑ k, (inner ℝ (rows r k) (qResidue d))^2) := by
  rw [← column_tail_sq (rows r) (rows_orthonormal r hr)]
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- The open arithmetic provider is displayed, not discharged. -/
def ArbitrarilySmallCertificates : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ m n : ℕ, ∃ r : Fin m → ℕ+,
    ∃ d : Fin n → {d : ℕ // 2 ≤ d ∧ Squarefree d}, ∃ c : Fin n → ℝ,
      Function.Injective r ∧ (∃ k, r k = 1) ∧
      certificate r (fun i => (d i).val) c < ε

theorem squarefree_closure_of_certificates (h : ArbitrarilySmallCertificates) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨m, n, r, d, c, hr, hone, hc⟩ := h (ε^2) (sq_pos_of_pos hε)
  refine ⟨qSynthesis (fun i => (d i).val) c, ?_, ?_⟩
  · unfold qSynthesis
    apply qSquarefreeCRTSpan.sum_mem
    intro i _
    apply qSquarefreeCRTSpan.smul_mem
    exact Submodule.subset_span ⟨d i, rfl⟩
  · rw [dist_eq_norm]
    have hb := error_le_certificate r hr hone (fun i => (d i).val) c
    nlinarith [norm_nonneg (qOne - qSynthesis (fun i => (d i).val) c)]

/-- Conditional research reduction to Mathlib's literal RiemannHypothesis. -/
theorem riemannHypothesis_of_certificates (h : ArbitrarilySmallCertificates) :
    RiemannHypothesis :=
  QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_squarefree_closure.mpr
      (squarefree_closure_of_certificates h))

end RiemannResearch.RH.QTensorCertificate
