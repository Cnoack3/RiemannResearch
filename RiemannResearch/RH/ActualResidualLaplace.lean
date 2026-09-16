import RiemannResearch.RH.CoupledResidualAnalyticTargets
import RiemannResearch.RH.ParetoFiniteResidueCharge
import RiemannResearch.Analysis.PeriodicResidueLaplaceAtZero

/-!
# Exact Laplace data of the actual finite Pareto residual

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 9. The coefficients are supplied by the checked actual-fit residue
representation. Positivity and common-period divisibility follow from the
actual conductor set. The residual has its periodic value `1` at zero.

No Bernoulli expansion or nonzero-derivative order is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoupledResidual
open RiemannResearch.Analysis.FiniteResidueCharge

/-- Each actual conductor is positive and divides the concrete factorial period. -/
theorem conductor_dvd_residualPeriod (M : ℕ) (i : conductorSet M) :
    0 < (i : ℕ) ∧ (i : ℕ) ∣ residualPeriod M := by
  have h := i.property
  simp only [conductorSet, dilatedConductors, Finset.mem_union,
    Finset.mem_image, Finset.mem_Icc] at h
  have hb : 0 < (i : ℕ) ∧ (i : ℕ) ≤ 3 * M := by
    rcases h with (h | ⟨m, hm, hi⟩) | ⟨m, hm, hi⟩ <;> constructor <;> omega
  exact ⟨hb.1, Nat.dvd_factorial hb.1 (by omega)⟩

private theorem actual_laplace_eq_charge (M : ℕ) (b : conductorSet M → ℝ)
    (he : ∀ n, hilbertSequence (fit M) n = ∑ i, b i * residue (i : ℕ) n)
    (t : ℝ) :
    periodicLaplaceAverage M t =
      RiemannResearch.Analysis.FiniteResidueCharge.periodicLaplaceAverage
        b (fun i : conductorSet M => (i : ℕ)) t (residualPeriod M) := by
  unfold periodicLaplaceAverage periodicResidual
    RiemannResearch.Analysis.FiniteResidueCharge.periodicLaplaceAverage
  simp only [he, residue, neg_mul]

/-- Constructed finite residue charges give the actual residual's exact
positive-parameter Laplace formula and its removable value at zero. -/
theorem actual_residual_laplace_data (M : ℕ) :
    ∃ b : conductorSet M → ℝ, (∑ i, b i = 0) ∧
      (∀ n, hilbertSequence (fit M) n = ∑ i, b i * residue (i : ℕ) n) ∧
      (∀ t : ℝ, 0 < t → periodicLaplaceAverage M t =
        1 + ∑ i, b i * (((i : ℕ) : ℝ) / (Real.exp (((i : ℕ) : ℝ) * t) - 1))) ∧
      periodicLaplaceAverage M 0 =
        constantTerm b (fun i : conductorSet M => ((i : ℕ) : ℝ)) := by
  obtain ⟨b, hb, he⟩ := fit_charge_representation M
  have hL : 0 < residualPeriod M := Nat.factorial_pos _
  have hn : ∀ i : conductorSet M, 0 < (i : ℕ) :=
    fun i => (conductor_dvd_residualPeriod M i).1
  have hd : ∀ i : conductorSet M, (i : ℕ) ∣ residualPeriod M :=
    fun i => (conductor_dvd_residualPeriod M i).2
  refine ⟨b, hb, he, ?_, ?_⟩
  · intro t ht
    rw [actual_laplace_eq_charge M b he t]
    exact periodicLaplaceAverage_eq b _ t ht (residualPeriod M) hL hn hd hb
  · rw [actual_laplace_eq_charge M b he 0]
    exact periodicLaplaceAverage_zero b _ (residualPeriod M) hL hn hd hb

/-- The actual finite residual average is continuous at zero. Its denominator
has value equal to the positive factorial period. -/
theorem actual_residual_laplace_continuousAt_zero (M : ℕ) :
    ContinuousAt (periodicLaplaceAverage M) 0 := by
  obtain ⟨b, hb, he⟩ := fit_charge_representation M
  have hk : periodicLaplaceAverage M =
      (fun t => RiemannResearch.Analysis.FiniteResidueCharge.periodicLaplaceAverage
        b (fun i : conductorSet M => (i : ℕ)) t (residualPeriod M)) :=
    funext (actual_laplace_eq_charge M b he)
  rw [hk]
  exact continuousAt_periodicLaplaceAverage_zero b _ (residualPeriod M)
    (Nat.factorial_pos _)

end RiemannResearch.RH.Pareto.CoupledResidual
