import RiemannResearch.RH.IntegerDPPClosure

/-!
# Finite signed Gram certificates for the limiting vacancy

Source: user request to formalize the remaining zero-vacancy endpoint
(2026-09-20). The finite bound is an application of the existing exact
inverse-Gram Cauchy--Schwarz inequality. The equivalence below uses the
actual finite optimizers and monotonicity of the actual tail capacity.
All mixed Gram terms are retained.

The final theorem is a conditional research reduction: the arithmetic
provider must produce trials of arbitrarily large source-to-energy ratio.
This file does not construct that provider or prove zero limiting vacancy.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertConstraints

/-- The reciprocal-source pairing of an arbitrary finite arithmetic trial. -/
def finiteTrialSource (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, c i * reciprocalSource n i

/-- The energy of the complete infinite physical tail of a finite trial.
Only its conductor support is truncated; no physical tail is discarded. -/
def finiteTrialEnergy (n : ℕ) (c : Fin n → ℝ) : ℝ :=
  ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2

/-- The trial energy includes every signed mixed Gram entry. -/
theorem finiteTrialEnergy_eq_gram (n : ℕ) (c : Fin n → ℝ) :
    finiteTrialEnergy n c =
      ∑ i : Fin n, ∑ j : Fin n,
        c i * c j * inner ℝ (tailAtom i.val) (tailAtom j.val) := by
  rw [finiteTrialEnergy, ← real_inner_self_eq_norm_sq]
  simp only [Fintype.linearCombination_apply]
  rw [sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every nonzero-energy trial gives a finite variational upper bound on
the vacancy. The bound improves precisely when source squared dominates
the full signed Gram energy. -/
theorem vacancy_le_finiteTrial_bound (n : ℕ) (c : Fin n → ℝ)
    (hE : 0 < finiteTrialEnergy n c) :
    vacancy n ≤ 2 * finiteTrialEnergy n c /
      (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) := by
  have hs := source_sq_le_capacity_mul_energy
    (finiteTailAtom_independent n) (reciprocalSource n) c
  change finiteTrialSource n c ^ 2 ≤ tailCapacity n * finiteTrialEnergy n c at hs
  have hC : 0 < tailCapacity n + 2 := by
    linarith [tailCapacity_nonneg n]
  have hD : 0 < finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c := by
    nlinarith [sq_nonneg (finiteTrialSource n c)]
  rw [vacancy_eq_capacity]
  apply (div_le_div_iff₀ hC hD).mpr
  nlinarith

/-- Zero limiting vacancy is exactly the availability of finite signed
arithmetic trials with arbitrarily large source-to-energy ratio.
The unbounded family is an unresolved arithmetic provider, not supplied
by the existence of each finite inverse Gram matrix. -/
theorem limitingVacancy_zero_iff_finiteTrial_certificates :
    limitingVacancy = 0 ↔
      ∀ B : ℝ, ∃ (n : ℕ) (c : Fin n → ℝ),
        0 < finiteTrialEnergy n c ∧
          B * finiteTrialEnergy n c < finiteTrialSource n c ^ 2 := by
  constructor
  · intro hz B
    have ht : Tendsto tailCapacity atTop atTop :=
      vacancy_tendsto_zero_iff.mp
        (vacancy_tendsto_zero_iff_limitingVacancy_zero.mpr hz)
    obtain ⟨n, hn⟩ := eventually_atTop.mp
      ((tendsto_atTop.mp ht) (max B 0 + 1))
    have hnC : max B 0 + 1 ≤ tailCapacity n := hn n le_rfl
    have hC : 0 < tailCapacity n := by
      linarith [le_max_right B (0 : ℝ)]
    have hBC : B < tailCapacity n := by
      linarith [le_max_left B (0 : ℝ)]
    let c := inverseSource (finiteTailAtom_independent n) (reciprocalSource n)
    have hA : finiteTrialSource n c = tailCapacity n := rfl
    have hE : finiteTrialEnergy n c = tailCapacity n := by
      change ‖minimumVector (finiteTailAtom_independent n) (reciprocalSource n)‖ ^ 2 =
        capacity (finiteTailAtom_independent n) (reciprocalSource n)
      exact (capacity_eq_norm_sq (finiteTailAtom_independent n)
        (reciprocalSource n)).symm
    refine ⟨n, c, ?_, ?_⟩
    · simpa only [hE] using hC
    · rw [hE, hA]
      simpa only [pow_two] using mul_lt_mul_of_pos_right hBC hC
  · intro h
    have ht : Tendsto tailCapacity atTop atTop := by
      apply tendsto_atTop.mpr
      intro B
      obtain ⟨n, c, hE, hB⟩ := h B
      have hs := source_sq_le_capacity_mul_energy
        (finiteTailAtom_independent n) (reciprocalSource n) c
      change finiteTrialSource n c ^ 2 ≤ tailCapacity n * finiteTrialEnergy n c at hs
      have hBC : B < tailCapacity n := by
        by_contra hBC
        have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hBC) hE.le
        exact (not_lt_of_ge (hs.trans hmul)) hB
      exact eventually_atTop.mpr ⟨n, fun m hnm =>
        hBC.le.trans (tailCapacity_monotone hnm)⟩
    exact vacancy_tendsto_zero_iff_limitingVacancy_zero.mp
      (vacancy_tendsto_zero_iff.mpr ht)

/-- CONDITIONAL RESEARCH REDUCTION. The explicit finite-witness family is
the open arithmetic obligation; no unconditional provider is asserted. -/
theorem riemannHypothesis_of_finiteTrial_certificates
    (h : ∀ B : ℝ, ∃ (n : ℕ) (c : Fin n → ℝ),
      0 < finiteTrialEnergy n c ∧
        B * finiteTrialEnergy n c < finiteTrialSource n c ^ 2) :
    RiemannHypothesis :=
  riemannHypothesis_of_vacancy_tendsto_zero
    (vacancy_tendsto_zero_iff_limitingVacancy_zero.mpr
      (limitingVacancy_zero_iff_finiteTrial_certificates.mpr h))

end RiemannResearch.RH.Pareto.IntegerDPP
