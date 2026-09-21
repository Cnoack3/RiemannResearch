import RiemannResearch.RH.ArgumentDoublingGenerators
import RiemannResearch.Analysis.ResidualZeroSensors

/-!
# The same limiting residual at every actual off-line zero

Source: user-provided stringent not-RH conditions, 2026-09-21, group 19.
The value theorem is proved for the actual infinite closed-span residual.
The higher-jet target records the simultaneous multiplicity constraints and
remains OPEN: the existing finite numerator jet theorem does not by itself
justify derivatives after passage to the Hilbert-space closure.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- All actual right-half-strip zeros test the same fixed limiting residual;
the vector is not independently chosen for each zero. -/
theorem limitResidual_mellin_at_zero
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    paretoMellin limitResidual ρ = 1 / ρ := by
  have hp : limitProjection ∈ closedSpace :=
    closedSpace.starProjection_apply_mem hilbertOne
  have hz := paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) ρ hhalf hρ1 hzero (closedSpace_le_legalClosure hp)
  change paretoMellinContinuous ρ hhalf (hilbertOne - limitProjection) = _
  rw [map_sub]
  change paretoMellin hilbertOne ρ - paretoMellin limitProjection ρ = _
  rw [paretoMellin_one ρ hhalf, hz, sub_zero]

/-- The actual limiting projection has zero Mellin value at every such zero,
while the residual necessarily has a nonzero value there. -/
theorem limitProjection_and_residual_zero_constraints
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) < ρ.re) (hρ1 : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    paretoMellin limitProjection ρ = 0 ∧ paretoMellin limitResidual ρ ≠ 0 := by
  have hp : limitProjection ∈ closedSpace :=
    closedSpace.starProjection_apply_mem hilbertOne
  refine ⟨paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) ρ hhalf hρ1 hzero (closedSpace_le_legalClosure hp), ?_⟩
  rw [limitResidual_mellin_at_zero ρ hhalf hρ1 hzero]
  apply div_ne_zero one_ne_zero
  intro h
  norm_num [h] at hhalf

/-- OPEN higher-jet closure target. Multiplicity is the actual analytic zeta
multiplicity `Zeta23.zeroMult`; no assumed multiplicity labels are substituted.
Every condition concerns the same `closedSpace` and `limitResidual`. -/
def ClosedSpaceMellinMultiplicityTarget : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ j : ℕ, j < Zeta23.zeroMult ρ →
      (∀ f : ThresholdHilbert, f ∈ closedSpace →
        iteratedDeriv j (paretoMellin f) ρ = 0) ∧
      iteratedDeriv j (paretoMellin limitResidual) ρ =
        (-1 : ℂ) ^ j * (Nat.factorial j : ℂ) / ρ ^ (j + 1)

end RiemannResearch.RH.Pareto.CoefficientStabilization
