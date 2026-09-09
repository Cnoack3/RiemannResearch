import RiemannResearch.RH.ParetoGibbsSpectralGap
import RiemannResearch.RH.ParetoGibbsConvergence
import RiemannResearch.RH.GibbsLegalSeed
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The open arithmetic obligations in the Gibbs research proposal

Source: RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md.
These are precise propositions awaiting proofs, not axioms or asserted theorems.
In particular, the existence of legal repairs is not supplied by the analytic
contraction results. The threshold-to-RH bridge is separately recorded.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Open arithmetic construction: a finite legal mean-one orbit with vanishing
actual Gibbs repair errors. -/
def GibbsArithmeticRepairTarget : Prop :=
  Analysis.ContractiveRepair.HasVanishingRepairOrbit
    (hilbertLegalSubspace {2, 3}) hilbertGibbsContinuous hilbertMeanContinuous

/-- The stronger invariance proposal; no preservation theorem is assumed. -/
def GibbsLegalInvarianceTarget : Prop :=
  ∀ f ∈ hilbertLegalClosure {2, 3}, hilbertGibbs f ∈ hilbertLegalClosure {2, 3}

/-- The analytic identification needed before labelling the formal closure
criterion an RH equivalence. It remains unproved in this development. -/
def ThresholdRiemannHypothesisBridgeTarget : Prop :=
  (hilbertOne ∈ hilbertLegalClosure {2, 3}) ↔ RiemannHypothesis

/-- A concrete stronger repair budget from the proposal. The coefficients are
signed and every positive integer dilation is available through the legal span. -/
def GibbsRelativeArithmeticRepairTarget : Prop :=
  ∃ (η : ℝ) (F : ℕ → ThresholdHilbert), 0 ≤ η ∧ η < 1 - Real.pi / 4 ∧
    (∀ n, F n ∈ hilbertLegalSubspace {2, 3}) ∧
    (∀ n, hilbertMeanContinuous (F n) = 1) ∧
    ∀ n, ‖F (n+1) - hilbertGibbs (F n)‖ ≤ η * ‖F n - hilbertOne‖

/-- Invariance would already put the target in the closed legal space.
This reduction uses the unconditional strong convergence theorem and does
not require the separate sharp-gap target. -/
theorem hilbertOne_mem_legalClosure_of_gibbs_invariance
    (hinv : GibbsLegalInvarianceTarget) : hilbertOne ∈ hilbertLegalClosure {2, 3} := by
  have hmem : ∀ n, hilbertGibbsIterate n initialLegalMeanOne ∈
      hilbertLegalClosure {2, 3} := by
    intro n
    induction n with
    | zero =>
      exact (hilbertLegalSubspace {2, 3}).le_topologicalClosure initialLegalMeanOne_legal
    | succ n ih => exact hinv _ ih
  have hlim := hilbertGibbsIterate_tendsto initialLegalMeanOne
  rw [initialLegalMeanOne_mean, one_smul] at hlim
  exact (hilbertLegalSubspace {2, 3}).isClosed_topologicalClosure.mem_of_tendsto
    hlim (Filter.Eventually.of_forall hmem)

/-- The proposed invariance route requires its arithmetic construction and
the explicit RH identification, but no external numerical gap value. -/
theorem riemannHypothesis_of_gibbs_invariance
    (hbridge : ThresholdRiemannHypothesisBridgeTarget)
    (hinv : GibbsLegalInvarianceTarget) : RiemannHypothesis :=
  hbridge.mp (hilbertOne_mem_legalClosure_of_gibbs_invariance hinv)

/-- A fully explicit conditional consumer. Neither open input is proved here. -/
theorem riemannHypothesis_of_gibbs_repair
    (hbridge : ThresholdRiemannHypothesisBridgeTarget)
    (hrepair : GibbsArithmeticRepairTarget) :
    RiemannHypothesis :=
  hbridge.mp (hilbertGibbs_legal_repair_iff_closure_unconditional.mp hrepair)

end
end RiemannResearch.RH.Pareto
