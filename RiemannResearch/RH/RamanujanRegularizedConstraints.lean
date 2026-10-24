import RiemannResearch.Analysis.FiniteRegularizedConstraints
import RiemannResearch.RH.RamanujanCoefficientConstraints
import RiemannResearch.RH.RamanujanMultipleConstraints
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.RamanujanCoefficientLimits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Soft original-coordinate constraints for actual Ramanujan legal approximants

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
Arbitrary finite conductor requests, including repeated or offstage rows,
define a strictly convex penalized problem in the actual packet Gram metric.
The optimizer, full normal equations, two complete remainders, and exact
hard-constraint comparison are constructed without row-rank assumptions.
All statements are finite and impose no asymptotic regularization hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanRegularizedConstraints
open Pareto RamanujanCanonicalOptimizer RamanujanCoefficientConstraints
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteRegularizedConstraints

variable {κ : Type*} [Fintype κ]

def constraintMatrix (n : ℕ) (m : κ → ℕ) : Matrix κ (Fin n) ℝ :=
  fun j => coordinateSource n (m j)

theorem observe_eq (n : ℕ) (m : κ → ℕ) (a : Fin n → ℝ) (j : κ) :
    observe (constraintMatrix n m) a j = packetMultipleTransform n a (m j) :=
  (coordinateSource_pairing n (m j) a).symm

def regularizedCoefficients (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : Fin n → ℝ :=
  RiemannResearch.Analysis.FiniteRegularizedConstraints.coefficients
    (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

def regularizedCandidate (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (regularizedCoefficients n m t ρ)

def coordinateMismatch (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ j, (packetMultipleTransform n a (m j) - t j) ^ 2

def penalizedError (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (a : Fin n → ℝ) : ℝ :=
  ‖hilbertOne - Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 +
      ρ ^ 2 * coordinateMismatch n m t a

theorem objective_eq (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (a : Fin n → ℝ) :
    objective (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (constraintMatrix n m) hilbertOne t ρ a = penalizedError n m t ρ a := by
  simp only [objective, mismatchEnergy, observe_eq, penalizedError, coordinateMismatch]

theorem regularizedGram_posDef (n : ℕ) (m : κ → ℕ) (ρ : ℝ) :
    (finitePacketGram n + ρ ^ 2 •
      ((constraintMatrix n m).transpose * constraintMatrix n m)).PosDef := by
  have h := RiemannResearch.Analysis.FiniteRegularizedConstraints.regularizedGram_posDef
    (finitePacket_independent n) (constraintMatrix n m) ρ
  rwa [regularizedGram_matrix] at h

/-- Both the original complete Gram and all mixed coordinate penalty terms remain. -/
theorem coefficients_inverseGram (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    regularizedCoefficients n m t ρ =
      (finitePacketGram n + ρ ^ 2 •
        ((constraintMatrix n m).transpose * constraintMatrix n m))⁻¹.mulVec
      (fun i : Fin n => ArithmeticFunction.vonMangoldt (i.val + 2) +
        ρ ^ 2 * ∑ j, coordinateSource n (m j) i * t j) := by
  have h := RiemannResearch.Analysis.FiniteRegularizedConstraints.coefficients_inverseGram
    (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ
  rw [regularizedGram_matrix] at h
  have hs : source (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (constraintMatrix n m) hilbertOne t ρ =
      (fun i : Fin n => ArithmeticFunction.vonMangoldt (i.val + 2) +
        ρ ^ 2 * ∑ j, coordinateSource n (m j) i * t j) := by
    funext i
    simp only [source, packet_inner_one, constraintMatrix]
  rw [hs] at h
  exact h

theorem coefficients_normal (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (i : Fin n) :
    inner ℝ (ramanujanPacketHilbert (i.val + 2)) (regularizedCandidate n m t ρ) +
      ρ ^ 2 * ∑ j, coordinateSource n (m j) i *
        packetMultipleTransform n (regularizedCoefficients n m t ρ) (m j) =
      ArithmeticFunction.vonMangoldt (i.val + 2) +
        ρ ^ 2 * ∑ j, coordinateSource n (m j) i * t j := by
  have h := RiemannResearch.Analysis.FiniteRegularizedConstraints.coefficients_normal
    (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ i
  simpa only [source, packet_inner_one, observe_eq, regularizedCoefficients,
    regularizedCandidate, constraintMatrix] using h

/-- The penalized minimum is the full inverse-Gram value of the augmented source. -/
theorem minimum_exact (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    penalizedError n m t ρ (regularizedCoefficients n m t ρ) =
      1 + ρ ^ 2 * ∑ j, (t j) ^ 2 -
        ∑ i : Fin n, regularizedCoefficients n m t ρ i *
          (ArithmeticFunction.vonMangoldt (i.val + 2) +
            ρ ^ 2 * ∑ j, coordinateSource n (m j) i * t j) := by
  have h := RiemannResearch.Analysis.FiniteRegularizedConstraints.coefficients_energy
    (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ
  rw [objective_eq] at h
  simpa only [source, packet_inner_one, hilbertOne_norm_sq, regularizedCoefficients,
    constraintMatrix] using h

/-- Exact completion retains physical and original-coordinate displacement. -/
theorem penalized_completion (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (a : Fin n → ℝ) :
    penalizedError n m t ρ a =
      penalizedError n m t ρ (regularizedCoefficients n m t ρ) +
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - regularizedCoefficients n m t ρ)‖ ^ 2 +
      ρ ^ 2 * ∑ j, (packetMultipleTransform n (a - regularizedCoefficients n m t ρ) (m j)) ^ 2 := by
  have h := RiemannResearch.Analysis.FiniteRegularizedConstraints.coefficients_completion
    (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ a
  simpa only [objective_eq, observationEnergy, observe_eq, regularizedCoefficients] using h

theorem penalized_optimal_iff (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) (a : Fin n → ℝ) :
    penalizedError n m t ρ a = penalizedError n m t ρ (regularizedCoefficients n m t ρ) ↔
      a = regularizedCoefficients n m t ρ := by
  simpa only [objective_eq, regularizedCoefficients] using
    RiemannResearch.Analysis.FiniteRegularizedConstraints.coefficients_optimal_iff
      (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ a

/-- The soft mismatch is the literal original continuous-coefficient mismatch. -/
theorem candidate_coordinate (n : ℕ) (m : κ → ℕ) (hm : ∀ j, 1 < m j)
    (t : κ → ℝ) (ρ : ℝ) (j : κ) :
    CoefficientStabilization.coefficientCLM (m j) (regularizedCandidate n m t ρ) =
      packetMultipleTransform n (regularizedCoefficients n m t ρ) (m j) :=
  coefficient_packet_synthesis n (regularizedCoefficients n m t ρ) (m j) (hm j)

/-- The exact hard-constraint inverse-Gram cost pays both soft displacement terms. -/
theorem hard_cost_tradeoff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (ρ : ℝ) :
    ‖Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (regularizedCoefficients n (fun j => (e j).val + 2) t ρ - packetCoefficients n)‖ ^ 2 +
      ρ ^ 2 * coordinateMismatch n (fun j => (e j).val + 2) t
        (regularizedCoefficients n (fun j => (e j).val + 2) t ρ) ≤
      RamanujanMultipleConstraints.constraintCost n e t := by
  have hfeas : ∀ j, observe (constraintMatrix n (fun j => (e j).val + 2))
      (RamanujanMultipleConstraints.constrainedCoefficients n e t) j = t j := by
    intro j
    rw [observe_eq]
    exact RamanujanMultipleConstraints.prescribed_coordinates n e t j
  have h := feasible_comparator (finitePacket_independent n)
    (constraintMatrix n (fun j => (e j).val + 2)) hilbertOne t ρ
    (RamanujanMultipleConstraints.constrainedCoefficients n e t) hfeas
  rw [objective_eq] at h
  change penalizedError n (fun j => (e j).val + 2) t ρ
    (regularizedCoefficients n (fun j => (e j).val + 2) t ρ) ≤
      ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 at h
  rw [RamanujanMultipleConstraints.candidate_error_exact] at h
  unfold penalizedError at h
  rw [packet_completion] at h
  linarith

/-- A finite quantitative penalty bound with the sharp actual hard-constraint cost. -/
theorem coordinateMismatch_le_hard_cost (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) :
    coordinateMismatch n (fun j => (e j).val + 2) t
      (regularizedCoefficients n (fun j => (e j).val + 2) t ρ) ≤
        RamanujanMultipleConstraints.constraintCost n e t / ρ ^ 2 := by
  have h := hard_cost_tradeoff n e t ρ
  apply (le_div_iff₀ (sq_pos_iff.mpr hρ)).mpr
  nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
    (regularizedCoefficients n (fun j => (e j).val + 2) t ρ - packetCoefficients n)‖]

theorem coordinateMismatch_decreases (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (ρ σ : ℝ) (hρσ : ρ ^ 2 ≤ σ ^ 2) :
    coordinateMismatch n m t (regularizedCoefficients n m t σ) ≤
      coordinateMismatch n m t (regularizedCoefficients n m t ρ) := by
  simpa only [mismatchEnergy, observe_eq, coordinateMismatch, regularizedCoefficients] using
    mismatch_antitone_of_sq_le (finitePacket_independent n) (constraintMatrix n m)
      hilbertOne t ρ σ hρσ

theorem fit_error_increases (n : ℕ) (m : κ → ℕ) (t : κ → ℝ)
    (ρ σ : ℝ) (hρσ : ρ ^ 2 ≤ σ ^ 2) :
    ‖hilbertOne - regularizedCandidate n m t ρ‖ ^ 2 ≤
      ‖hilbertOne - regularizedCandidate n m t σ‖ ^ 2 :=
  fit_error_monotone_of_sq_le (finitePacket_independent n) (constraintMatrix n m)
    hilbertOne t ρ σ hρσ

/-- Zero penalty recovers the canonical legal packet optimizer exactly. -/
theorem regularizedCoefficients_zero (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) :
    regularizedCoefficients n m t 0 = packetCoefficients n :=
  coefficients_zero (finitePacket_independent n) (constraintMatrix n m) hilbertOne t

/-- The tradeoff retains both full signed displacement energies. -/
theorem penalty_difference_exact (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ σ : ℝ) :
    (σ ^ 2 - ρ ^ 2) *
      (coordinateMismatch n m t (regularizedCoefficients n m t ρ) -
        coordinateMismatch n m t (regularizedCoefficients n m t σ)) =
      2 * ‖regularizedCandidate n m t ρ - regularizedCandidate n m t σ‖ ^ 2 +
      (ρ ^ 2 + σ ^ 2) * ∑ j,
        (packetMultipleTransform n
          (regularizedCoefficients n m t ρ - regularizedCoefficients n m t σ) (m j)) ^ 2 := by
  have h := RiemannResearch.Analysis.FiniteRegularizedConstraints.penalty_difference_exact
    (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ σ
  simpa only [mismatchEnergy, observationEnergy, observe_eq, coordinateMismatch,
    regularizedCoefficients, regularizedCandidate, map_sub] using h

end RiemannResearch.RH.RamanujanRegularizedConstraints
