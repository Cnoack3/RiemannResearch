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
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

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

/-!
## A complete rational three-atom certificate

Source: Prime Tensor CRT RH Research Project (2 November 2026), Appendix B.
The finite first-period reciprocal energy bounds the full infinite Q norm.
This Lean bound is deliberately distinguished from the tighter Python
rational enclosure in the companion research memorandum.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTensorCertificate.Benchmark
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative Pareto

def errorVector : QHilbert :=
  qOne - ((1045918/1000000 : ℝ) • qResidue 2 +
    (1069558/1000000 : ℝ) • qResidue 3 +
    (604750/1000000 : ℝ) • qResidue 6)

def residual (n : ℕ) : ℝ :=
  1 - ((1045918/1000000 : ℝ) * residueFraction 2 n +
    (1069558/1000000 : ℝ) * residueFraction 3 n +
    (604750/1000000 : ℝ) * residueFraction 6 n)

theorem errorVector_coordinate (n : ℕ) (hn : n ≠ 0) :
    qSequence errorVector n = residual n := by
  change qSequenceLinear (qOne - ((1045918/1000000 : ℝ) • qResidue 2 +
    (1069558/1000000 : ℝ) • qResidue 3 +
    (604750/1000000 : ℝ) • qResidue 6)) n = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  change qSequence qOne n - ((1045918/1000000 : ℝ) * qSequence (qResidue 2) n +
    (1069558/1000000 : ℝ) * qSequence (qResidue 3) n +
    (604750/1000000 : ℝ) * qSequence (qResidue 6) n) = _
  simp [qSequence_qOne, qOneSequence, hn, qSequence_qResidue, residual]

theorem residual_bound (n : ℕ) : |residual n| ≤ 4 := by
  have hb (d : ℕ) (hd : 0 < d) :
      0 ≤ residueFraction d n ∧ residueFraction d n ≤ 1 := by
    unfold residueFraction
    constructor
    · positivity
    · apply (div_le_one (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
      exact_mod_cast (Nat.mod_lt n hd).le
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have h6 := hb 6 (by decide)
  rw [abs_le]
  unfold residual
  constructor <;> nlinarith

theorem residual_periodic (n : ℕ) : residual (n + 6) = residual n := by
  simp [residual, residueFraction, Nat.add_mod]

theorem complete_norm_lt : ‖errorVector‖^2 < (59 : ℝ)/1000 := by
  have hn : ‖errorVector‖^2 = inversePowerMean 0 (fun n => residual n ^ 2) := by
    rw [qNorm_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    dsimp only
    rw [errorVector_coordinate (n+1) (by omega)]
  have hb := (periodic_qEnergy_comparison 6 (by decide)
    residual residual_bound residual_periodic).2
  have hr : crtReciprocalEnergy 6 residual =
      (53001021710221 : ℝ)/900000000000000 := by
    norm_num [crtReciprocalEnergy, Fin.sum_univ_succ, residual, residueFraction]
  rw [hr] at hb
  rw [hn]
  exact hb.trans_lt (by norm_num)

end RiemannResearch.RH.QTensorCertificate.Benchmark
