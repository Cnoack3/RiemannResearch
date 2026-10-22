import RiemannResearch.RH.QExplicitCandidates
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Lean.Elab.Tactic.Omega

/-!
# Concrete Möbius exact-head candidates in the actual Q Hilbert space

Source: the user's explicit Q candidate construction, 13 October 2026.
The physical Möbius identity is reused from `CanonicalMobiusConditionalHead`;
only its Q encoding and legal-span membership are new specializations.

The formula and exact head are unconditional. Convergence of its sparse
finite averages, or of the fixed inverse-Gram candidate, retains the full
uniform Q error bound as an explicit unresolved arithmetic hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QMobiusExactHead

open ZetaTwoHilbert

/-- Completely explicit arithmetic head interpolant. The conductor-one
term is harmlessly zero; every nonzero atom is legal. -/
def exactHead (N : ℕ) : QHilbert :=
  -(∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) • qResidue d) +
    (((N + 1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum N) • qResidue (N + 1)

/-- This Q vector has exactly the existing canonical Möbius physical sequence. -/
theorem exactHead_sequence (N : ℕ) :
    qSequence (exactHead N) = Pareto.canonicalMobiusHead N := by
  change qSequenceLinear (exactHead N) = _
  unfold exactHead
  simp only [map_add, map_neg, map_sum, map_smul]
  change -(∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) • qSequence (qResidue d)) +
    (((N + 1 : ℕ) : ℝ) * Pareto.mobiusReciprocalSum N) •
      qSequence (qResidue (N + 1)) = _
  simp_rw [qSequence_qResidue]
  funext n
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Pareto.canonicalMobiusHead]

theorem exactHead_exact (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (exactHead N) n = 1 := by
  rw [exactHead_sequence]
  exact Pareto.canonicalMobiusHead_exact N n hn hnN

private theorem positiveResidue_mem_legalSpan (d : ℕ) (hd : 0 < d) :
    qResidue d ∈ QFullResidueProjection.legalSpan := by
  by_cases h1 : d = 1
  · rw [h1, qResidue_one]
    exact Submodule.zero_mem _
  · change qResidue d ∈ Submodule.span ℝ
      (Set.range (fun i : ℕ => qResidue (i + 2)))
    apply Submodule.subset_span
    refine ⟨d - 2, ?_⟩
    have he : d - 2 + 2 = d := by omega
    change qResidue (d - 2 + 2) = qResidue d
    rw [he]

theorem exactHead_mem_legalSpan (N : ℕ) :
    exactHead N ∈ QFullResidueProjection.legalSpan := by
  apply QFullResidueProjection.legalSpan.add_mem
  · apply QFullResidueProjection.legalSpan.neg_mem
    apply QFullResidueProjection.legalSpan.sum_mem
    intro d hd
    exact QFullResidueProjection.legalSpan.smul_mem _
      (positiveResidue_mem_legalSpan d (Finset.mem_Icc.mp hd).1)
  · exact QFullResidueProjection.legalSpan.smul_mem _
      (positiveResidue_mem_legalSpan (N + 1) (Nat.succ_pos N))

/-- Explicit arithmetic candidates plus the still-open uniform actual Q
error bound produce finite legal averages converging to one at rate B/m+4/m². -/
theorem exists_exactHead_averages_of_uniform_bound {B : ℝ}
    (hbound : ∀ N, ‖qOne - exactHead N‖ ^ 2 ≤ B) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      (∀ m, QExactHeadAverages.average exactHead q m ∈
        QFullResidueProjection.legalSpan) ∧
      (∀ m : ℕ, 0 < m →
        ‖qOne - QExactHeadAverages.average exactHead q m‖ ^ 2 ≤
          B / m + 4 / (m : ℝ) ^ 2) ∧
      Tendsto (QExactHeadAverages.average exactHead q) atTop (𝓝 qOne) :=
  QExactHeadAverages.exists_legal_averages_of_bounded_exact_heads
    QFullResidueProjection.legalSpan exactHead exactHead_mem_legalSpan
    hbound exactHead_exact

/-- The same concrete-family arithmetic bound forces convergence of the
fixed genuine inverse-Gram candidates, without altering their coefficients. -/
theorem inverseGram_tendsto_of_exactHead_uniform_bound {B : ℝ}
    (hbound : ∀ N, ‖qOne - exactHead N‖ ^ 2 ≤ B) :
    Tendsto QFullResidueProjection.candidate atTop (𝓝 qOne) :=
  QExplicitCandidates.candidate_tendsto_of_bounded_exact_heads
    exactHead exactHead_mem_legalSpan hbound exactHead_exact

end RiemannResearch.RH.QMobiusExactHead
