import RiemannResearch.RH.RamanujanMultipleConstraints
import RiemannResearch.RH.RamanujanMultipleCapacityLimits
import RiemannResearch.RH.RamanujanMultipleAffineLimits
import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.Analysis.FiniteGramDeterminantCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sharp determinant certificates for legal Ramanujan error budgets

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
The matrix being bordered is the actual full source Gram `B H⁻¹ Bᵀ`.
Its new corner is the proposed error budget minus the unconstrained error;
its off-diagonal source is the complete vector of prescribed-coordinate
mismatches. The determinant sign characterizes existence of a legal fit
within that budget, both at a finite packet stage and in the full closed
legal space. Singular certificates identify the unique minimizing fit.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanConstraintDeterminants
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramDeterminantCertificates

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def finiteCertificate (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (E : ℝ) :
    Matrix (Option κ) (Option κ) ℝ :=
  bordered (RamanujanMultipleConstraints.rows n e)
    (RamanujanMultipleConstraints.defect n e t) (E - (1 - packetMass n))

/-- The normalized determinant is the exact budget slack, with the full
inverse source-Gram cost and the canonical approximation error retained. -/
theorem finiteCertificate_ratio (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (E : ℝ) :
    (finiteCertificate n e t E).det / (RamanujanMultipleConstraints.constraintGram n e).det =
      E - (1 - packetMass n + RamanujanMultipleConstraints.constraintCost n e t) := by
  have h := bordered_det_ratio (RamanujanMultipleConstraints.rows_independent n e)
    (RamanujanMultipleConstraints.defect n e t) (E - (1 - packetMass n))
  change (finiteCertificate n e t E).det /
      (RamanujanMultipleConstraints.constraintGram n e).det =
    E - (1 - packetMass n) - RamanujanMultipleConstraints.constraintCost n e t at h
  linarith

theorem finiteCertificate_nonneg_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (E : ℝ) :
    0 ≤ (finiteCertificate n e t E).det ↔
      1 - packetMass n + RamanujanMultipleConstraints.constraintCost n e t ≤ E := by
  unfold finiteCertificate
  rw [bordered_det_nonneg_iff (RamanujanMultipleConstraints.rows_independent n e)]
  change RamanujanMultipleConstraints.constraintCost n e t ≤ E - (1 - packetMass n) ↔ _
  constructor <;> intro h <;> linarith

theorem finiteCertificate_pos_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (E : ℝ) :
    0 < (finiteCertificate n e t E).det ↔
      1 - packetMass n + RamanujanMultipleConstraints.constraintCost n e t < E := by
  unfold finiteCertificate
  rw [bordered_det_pos_iff (RamanujanMultipleConstraints.rows_independent n e)]
  change RamanujanMultipleConstraints.constraintCost n e t < E - (1 - packetMass n) ↔ _
  constructor <;> intro h <;> linarith

theorem finiteCertificate_zero_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (E : ℝ) :
    (finiteCertificate n e t E).det = 0 ↔
      E = 1 - packetMass n + RamanujanMultipleConstraints.constraintCost n e t := by
  unfold finiteCertificate
  rw [bordered_det_zero_iff (RamanujanMultipleConstraints.rows_independent n e)]
  change E - (1 - packetMass n) = RamanujanMultipleConstraints.constraintCost n e t ↔ _
  constructor <;> intro h <;> linarith

/-- A determinant sign alone is a complete attained finite error-budget test. -/
theorem finite_budget_feasible_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (E : ℝ) :
    (∃ a : Fin n → ℝ,
      (∀ j, packetMultipleTransform n a ((e j).val + 2) = t j) ∧
        ‖hilbertOne - Fintype.linearCombination ℝ
          (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 ≤ E) ↔
      0 ≤ (finiteCertificate n e t E).det := by
  rw [finiteCertificate_nonneg_iff]
  constructor
  · rintro ⟨a, ha, hE⟩
    have h := RamanujanMultipleConstraints.constrained_completion n e t a ha
    have hs := sq_nonneg ‖Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (a - RamanujanMultipleConstraints.constrainedCoefficients n e t)‖
    linarith
  · intro hE
    refine ⟨RamanujanMultipleConstraints.constrainedCoefficients n e t,
      RamanujanMultipleConstraints.prescribed_coordinates n e t, ?_⟩
    change ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 ≤ E
    rwa [RamanujanMultipleConstraints.candidate_error_exact]

/-- Evaluated at a feasible trial's error, the certificate equals its complete
packet-Gram displacement from the actual constrained optimizer. -/
theorem finite_trial_determinant_completion (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (a : Fin n → ℝ) (ha : ∀ j, packetMultipleTransform n a ((e j).val + 2) = t j) :
    (finiteCertificate n e t
      (‖hilbertOne - Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2)).det /
        (RamanujanMultipleConstraints.constraintGram n e).det =
      ‖Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (a - RamanujanMultipleConstraints.constrainedCoefficients n e t)‖ ^ 2 := by
  rw [finiteCertificate_ratio]
  have h := RamanujanMultipleConstraints.constrained_completion n e t a ha
  linarith

theorem finite_trial_determinant_zero_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (a : Fin n → ℝ) (ha : ∀ j, packetMultipleTransform n a ((e j).val + 2) = t j) :
    (finiteCertificate n e t
      (‖hilbertOne - Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2)).det = 0 ↔
      a = RamanujanMultipleConstraints.constrainedCoefficients n e t := by
  rw [finiteCertificate_zero_iff]
  exact RamanujanMultipleConstraints.constrained_optimal_iff n e t a ha

/-- The determinant polynomial detects the complete finite constraint cost
for every real update parameter, including negative parameters. -/
theorem finite_source_determinant_polynomial (n : ℕ) (e : κ ↪ Fin n)
    (t : κ → ℝ) (z : ℝ) :
    (RamanujanMultipleConstraints.constraintGram n e + z • Matrix.vecMulVec
      (RamanujanMultipleConstraints.defect n e t)
      (RamanujanMultipleConstraints.defect n e t)).det /
      (RamanujanMultipleConstraints.constraintGram n e).det =
        1 + z * RamanujanMultipleConstraints.constraintCost n e t :=
  source_determinant_polynomial (RamanujanMultipleConstraints.rows_independent n e) _ z

def closedCertificate (e : κ ↪ ℕ) (t : κ → ℝ) (E : ℝ) : Matrix (Option κ) (Option κ) ℝ :=
  bordered (RamanujanMultipleCapacityLimits.limitRows e)
    (RamanujanMultipleAffineLimits.limitDefect e t) (E - limitEnergy)

theorem closedCertificate_ratio (e : κ ↪ ℕ) (t : κ → ℝ) (E : ℝ) :
    (closedCertificate e t E).det / (RamanujanMultipleCapacityLimits.limitGram e).det =
      E - (limitEnergy + RamanujanMultipleAffineLimits.limitCost e t) := by
  have h := bordered_det_ratio (RamanujanMultipleCapacityLimits.limitRows_independent e)
    (RamanujanMultipleAffineLimits.limitDefect e t) (E - limitEnergy)
  change (closedCertificate e t E).det / (RamanujanMultipleCapacityLimits.limitGram e).det =
    E - limitEnergy - RamanujanMultipleAffineLimits.limitCost e t at h
  linarith

theorem closedCertificate_nonneg_iff (e : κ ↪ ℕ) (t : κ → ℝ) (E : ℝ) :
    0 ≤ (closedCertificate e t E).det ↔
      limitEnergy + RamanujanMultipleAffineLimits.limitCost e t ≤ E := by
  unfold closedCertificate
  rw [bordered_det_nonneg_iff (RamanujanMultipleCapacityLimits.limitRows_independent e)]
  change RamanujanMultipleAffineLimits.limitCost e t ≤ E - limitEnergy ↔ _
  constructor <;> intro h <;> linarith

theorem closedCertificate_zero_iff (e : κ ↪ ℕ) (t : κ → ℝ) (E : ℝ) :
    (closedCertificate e t E).det = 0 ↔
      E = limitEnergy + RamanujanMultipleAffineLimits.limitCost e t := by
  unfold closedCertificate
  rw [bordered_det_zero_iff (RamanujanMultipleCapacityLimits.limitRows_independent e)]
  change E - limitEnergy = RamanujanMultipleAffineLimits.limitCost e t ↔ _
  constructor <;> intro h <;> linarith

/-- The same sharp determinant certificate controls the entire closed legal
space, with the unresolved canonical residual still present. -/
theorem closed_budget_feasible_iff (e : κ ↪ ℕ) (t : κ → ℝ) (E : ℝ) :
    (∃ y : ThresholdHilbert, y ∈ closedSpace ∧
      (∀ j, coefficientCLM (e j + 2) y = t j) ∧ ‖hilbertOne - y‖ ^ 2 ≤ E) ↔
      0 ≤ (closedCertificate e t E).det := by
  rw [closedCertificate_nonneg_iff]
  constructor
  · rintro ⟨y, hy, ht, hE⟩
    have h := RamanujanMultipleAffineLimits.affineLimitCandidate_completion e t y hy ht
    have hs := sq_nonneg ‖y - RamanujanMultipleAffineLimits.affineLimitCandidate e t‖
    linarith
  · intro hE
    refine ⟨RamanujanMultipleAffineLimits.affineLimitCandidate e t,
      RamanujanMultipleAffineLimits.affineLimitCandidate_mem e t,
      RamanujanMultipleAffineLimits.affineLimitCandidate_coordinates e t, ?_⟩
    rwa [RamanujanMultipleAffineLimits.affineLimitCandidate_error]

theorem closed_trial_determinant_completion (e : κ ↪ ℕ) (t : κ → ℝ)
    (y : ThresholdHilbert) (hy : y ∈ closedSpace)
    (ht : ∀ j, coefficientCLM (e j + 2) y = t j) :
    (closedCertificate e t (‖hilbertOne - y‖ ^ 2)).det /
      (RamanujanMultipleCapacityLimits.limitGram e).det =
        ‖y - RamanujanMultipleAffineLimits.affineLimitCandidate e t‖ ^ 2 := by
  rw [closedCertificate_ratio]
  have h := RamanujanMultipleAffineLimits.affineLimitCandidate_completion e t y hy ht
  linarith

theorem closed_trial_determinant_zero_iff (e : κ ↪ ℕ) (t : κ → ℝ)
    (y : ThresholdHilbert) (hy : y ∈ closedSpace)
    (ht : ∀ j, coefficientCLM (e j + 2) y = t j) :
    (closedCertificate e t (‖hilbertOne - y‖ ^ 2)).det = 0 ↔
      y = RamanujanMultipleAffineLimits.affineLimitCandidate e t := by
  rw [closedCertificate_zero_iff]
  exact RamanujanMultipleAffineLimits.affineLimitCandidate_optimal_iff e t y hy ht

theorem closed_source_determinant_polynomial (e : κ ↪ ℕ) (t : κ → ℝ) (z : ℝ) :
    (RamanujanMultipleCapacityLimits.limitGram e + z • Matrix.vecMulVec
      (RamanujanMultipleAffineLimits.limitDefect e t)
      (RamanujanMultipleAffineLimits.limitDefect e t)).det /
      (RamanujanMultipleCapacityLimits.limitGram e).det =
        1 + z * RamanujanMultipleAffineLimits.limitCost e t :=
  source_determinant_polynomial (RamanujanMultipleCapacityLimits.limitRows_independent e) _ z

end RiemannResearch.RH.RamanujanConstraintDeterminants
