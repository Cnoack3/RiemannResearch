import RiemannResearch.RH.RamanujanCoefficientConstraints
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.FiniteGramMultipleConstraint
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Simultaneous prescribed legal coefficients in Ramanujan coordinates

Source: user-requested continuation of the duality structure, 23 October 2026.
Any distinct finite selection of original residue coefficients in the legal
stage can be prescribed simultaneously. The restricted arithmetic source
Gram is automatically positive definite; no invertibility assumption is
imposed. Its inverse gives the exact price and the unique packet optimizer.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanMultipleConstraints
open Pareto RamanujanCanonicalOptimizer RamanujanCoefficientConstraints
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteGramMultipleConstraint

variable {κ : Type*} [Fintype κ]

/-- A simultaneous finite system of original legal coefficient sources. -/
def sources (n : ℕ) (e : κ ↪ Fin n) (j : κ) : Fin n → ℝ :=
  coordinateSource n ((e j).val + 2)

def rows (n : ℕ) (e : κ ↪ Fin n) : κ → ThresholdHilbert :=
  sourceRows (finitePacket_independent n) (sources n e)

/-- The inverse-Gram row family has full rank because each original residue
atom is a legal packet synthesis and interpolates the corresponding unit row. -/
theorem rows_independent (n : ℕ) (e : κ ↪ Fin n) :
    LinearIndependent ℝ (rows n e) := by
  classical
  apply sourceRows_independent_of_interpolants
  intro j
  have hg : CoefficientStabilization.residueAtom (e j).val ∈
      Submodule.span ℝ (Set.range (fun i : Fin n =>
        ramanujanPacketHilbert (i.val + 2))) := by
    rw [finitePacket_span_eq]
    exact Submodule.subset_span ⟨e j, rfl⟩
  rw [← Fintype.range_linearCombination] at hg
  obtain ⟨a, ha⟩ := hg
  refine ⟨a, ?_⟩
  intro i
  change (∑ k, a k * coordinateSource n ((e i).val + 2) k) = _
  rw [← coordinateSource_pairing,
    ← coefficient_packet_synthesis n a ((e i).val + 2) (by omega), ha,
    CoefficientStabilization.coefficientCLM_biorthogonal]
  have he : (e i).val = (e j).val ↔ i = j := by
    constructor
    · intro h
      exact e.injective (Fin.ext h)
    · rintro rfl
      rfl
  simp only [he]

/-- The full arithmetic matrix `B H⁻¹ Bᵀ`, with no diagonal approximation. -/
def constraintGram (n : ℕ) (e : κ ↪ Fin n) : Matrix κ κ ℝ :=
  gramMatrix (rows n e)

theorem constraintGram_entry (n : ℕ) (e : κ ↪ Fin n) (i j : κ) :
    constraintGram n e i j = ∑ k,
      inverseSource (finitePacket_independent n) (coordinateSource n ((e j).val + 2)) k *
        coordinateSource n ((e i).val + 2) k :=
  sourceRows_gram (finitePacket_independent n) (sources n e) i j

theorem constraintGram_det_pos [DecidableEq κ] (n : ℕ) (e : κ ↪ Fin n) :
    0 < (constraintGram n e).det := gramMatrix_det_pos (rows_independent n e)

def defect (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (j : κ) : ℝ :=
  t j - packetMultipleCoefficient n ((e j).val + 2)

theorem mismatch_eq (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    mismatch (finitePacket_independent n) (sources n e) hilbertOne t = defect n e t := by
  funext j
  unfold mismatch defect packetMultipleCoefficient
  rw [coordinateSource_pairing]
  rfl

def constrainedCoefficients (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : Fin n → ℝ :=
  RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients
    (finitePacket_independent n) (sources n e) (rows_independent n e) hilbertOne t

def constrainedCandidate (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (constrainedCoefficients n e t)

def constraintCost (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : ℝ :=
  capacity (rows_independent n e) (defect n e t)

/-- The explicit two-inverse coefficient correction, retaining all cross couplings. -/
theorem coefficients_exact (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    constrainedCoefficients n e t = packetCoefficients n +
      ∑ j, inverseSource (rows_independent n e) (defect n e t) j •
        inverseSource (finitePacket_independent n) (coordinateSource n ((e j).val + 2)) := by
  unfold constrainedCoefficients
  unfold RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients
  rw [mismatch_eq]
  rfl

theorem prescribed_coordinates (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (j : κ) :
    packetMultipleTransform n (constrainedCoefficients n e t) ((e j).val + 2) = t j := by
  rw [coordinateSource_pairing]
  exact coefficients_source (finitePacket_independent n) (sources n e)
    (rows_independent n e) hilbertOne t j

theorem candidate_coordinates (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (j : κ) :
    CoefficientStabilization.coefficientCLM ((e j).val + 2)
      (constrainedCandidate n e t) = t j := by
  rw [constrainedCandidate, coefficient_packet_synthesis _ _ _ (by omega)]
  exact prescribed_coordinates n e t j

/-- The exact minimum is the original projection error plus one full source-Gram cost. -/
theorem candidate_error_exact (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    ‖hilbertOne - constrainedCandidate n e t‖ ^ 2 =
      1 - packetMass n + constraintCost n e t := by
  have h := coefficients_energy (finitePacket_independent n) (sources n e)
    (rows_independent n e) hilbertOne t
  rw [mismatch_eq] at h
  change ‖hilbertOne - constrainedCandidate n e t‖ ^ 2 =
    ‖hilbertOne - packetCandidate n‖ ^ 2 + constraintCost n e t at h
  rw [packet_error] at h
  exact h

theorem cost_inverseGram [DecidableEq κ] (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    constraintCost n e t = dotProduct (defect n e t)
      ((constraintGram n e)⁻¹.mulVec (defect n e t)) := by
  rw [constraintGram, gramMatrix_inverseSource (rows_independent n e)]
  unfold constraintCost capacity dotProduct
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem constrained_completion (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (a : Fin n → ℝ)
    (ha : ∀ j, packetMultipleTransform n a ((e j).val + 2) = t j) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
    1 - packetMass n + constraintCost n e t +
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - constrainedCoefficients n e t)‖ ^ 2 := by
  have hc : ∀ j, (∑ i, a i * sources n e j i) = t j := by
    intro j
    exact (coordinateSource_pairing n ((e j).val + 2) a).symm.trans (ha j)
  have h := coefficients_completion (finitePacket_independent n) (sources n e)
    (rows_independent n e) hilbertOne t a hc
  change _ = ‖hilbertOne - constrainedCandidate n e t‖ ^ 2 + _ at h
  rw [candidate_error_exact] at h
  exact h

theorem constrained_optimal_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (a : Fin n → ℝ)
    (ha : ∀ j, packetMultipleTransform n a ((e j).val + 2) = t j) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - packetMass n + constraintCost n e t ↔ a = constrainedCoefficients n e t := by
  constructor
  · intro he
    apply coefficients_unique (finitePacket_independent n) (sources n e)
      (rows_independent n e) hilbertOne t a
    · intro j
      exact (coordinateSource_pairing n ((e j).val + 2) a).symm.trans (ha j)
    · change _ = ‖hilbertOne - constrainedCandidate n e t‖ ^ 2
      rwa [candidate_error_exact]
  · rintro rfl
    exact candidate_error_exact n e t

end RiemannResearch.RH.RamanujanMultipleConstraints
