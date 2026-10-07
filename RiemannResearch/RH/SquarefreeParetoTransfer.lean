import RiemannResearch.Analysis.SquarefreeStepBridge
import RiemannResearch.RH.ParetoStepIsometry
import RiemannResearch.RH.BaezDuarteCenteredBridge

/-!
# Complete corrected-atom transfer and squarefree approximation necessity

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The finite cell identity is joined here to the existing complete Pareto step
isometry.  Thus the attachment's continuous-to-discrete norm comparison is an
exact equality for actual Hilbert vectors.  Squarefree centered approximation
implies Mathlib's Riemann hypothesis through the established Mellin argument.
No RH-to-damped-approximation theorem is assumed or asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SquarefreeTransfer
open RiemannResearch.Analysis.SquarefreeStepBridge
open BaezDuarte CoefficientStabilization

/-- The literal complete corrected-atom error on the positive tail. -/
def correctedTailError (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∫ x : ℝ in Ioi 1, (1 - ∑ d ∈ s, a d * correctedAtom d x) ^ 2 / x ^ 2

/-- Corrected fractional-part atoms are the actual discrete residues at the
natural floor, everywhere on the nonnegative half-line. -/
theorem correctedAtom_eq_discrete_floor (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    correctedAtom d x = discreteAtom d ⌊x⌋₊ := by
  have hu0 : 0 ≤ x - (⌊x⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hx)
  have hu1 : x - (⌊x⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one x]
  have hcell := correctedAtom_cell d ⌊x⌋₊ (x - (⌊x⌋₊ : ℝ)) hu0 hu1
  rw [show (⌊x⌋₊ : ℝ) + (x - (⌊x⌋₊ : ℝ)) = x by ring] at hcell
  exact hcell

theorem finite_corrected_trial_eq_sequence (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    (∑ d ∈ s, a d * correctedAtom d x) =
      hilbertSequence (finiteResidueSum s a) ⌊x⌋₊ := by
  rw [finiteResidueSum_sequence s a hs]
  apply Finset.sum_congr rfl
  intro d hd
  rw [correctedAtom_eq_discrete_floor d hx]
  rfl

/-- Complete norm equality, with no finite physical cutoff or asymptotic
sampling argument. -/
theorem correctedTailError_eq_hilbert_norm_sq (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    correctedTailError s a = ‖hilbertOne - finiteResidueSum s a‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  rw [← paretoStep_energy_identity _
    (hilbertSequence_square_summable (hilbertOne - finiteResidueSum s a))]
  unfold correctedTailError
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 ≤ x := le_trans zero_le_one (le_of_lt hx)
  have hk : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using le_of_lt hx)
  have hseq := congrFun
    (hilbertSequenceLinear.map_sub hilbertOne (finiteResidueSum s a)) ⌊x⌋₊
  change hilbertSequence (hilbertOne - finiteResidueSum s a) ⌊x⌋₊ =
    hilbertSequence hilbertOne ⌊x⌋₊ - hilbertSequence (finiteResidueSum s a) ⌊x⌋₊ at hseq
  dsimp only
  rw [hseq, hilbertOne_sequence,
    ← finite_corrected_trial_eq_sequence s a hs hx0]
  simp [zeroAnchor, show ⌊x⌋₊ ≠ 0 by omega]

/-- The two existing continuum formulations have exactly the same complete
error, although one uses inverted Lebesgue coordinates. -/
theorem centeredError_eq_ofReal_correctedTailError (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    centeredError s a = ENNReal.ofReal (correctedTailError s a) := by
  rw [centeredError_eq_hilbert_norm_sq s a hs,
    correctedTailError_eq_hilbert_norm_sq s a hs]

/-- The squarefree restriction is part of the approximation statement, not
an additional axiom about an external published theorem. -/
def SquarefreeCenteredApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ d ∈ s, 0 < d) ∧ (∀ d ∈ s, Squarefree d) ∧
      centeredError s a < ENNReal.ofReal ε

theorem squarefreeCenteredApproximation_implies_centeredApproximation
    (h : SquarefreeCenteredApproximation) : CenteredApproximation := by
  intro ε hε
  obtain ⟨s, a, hs, hsf, he⟩ := h ε hε
  exact ⟨s, a, hs, he⟩

/-- Squarefree approximation suffices for RH through the actual complete
Pareto Mellin separation argument. The reverse implication needs the
unformalized conditional analytic approximation theorem. -/
theorem riemannHypothesis_of_squarefreeCenteredApproximation
    (h : SquarefreeCenteredApproximation) : RiemannHypothesis := by
  have hmem := centeredApproximation_iff_one_mem.mp
    (squarefreeCenteredApproximation_implies_centeredApproximation h)
  exact riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn) (closedSpace_le_legalClosure hmem)

end RiemannResearch.RH.Pareto.SquarefreeTransfer
