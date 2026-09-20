import RiemannResearch.Probability.DeterminantalProcess
import RiemannResearch.Probability.DeterminantalEntry
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.RH.IntegerDPPKernel
import RiemannResearch.RH.IntegerDPPSchur

/-!
# DPP probability, the odd-carry criterion, and the RH endpoint

Source: user-provided DPP and CRT/orbit Markdown handoffs (2026-09-20).
This module assembles the actual arithmetic kernels and capacities. A random
process is explicitly required to satisfy `IsDPP`; general existence and a
nested coupling of the arithmetic DPPs are not asserted by these theorems.
The deterministic equivalences have no such probabilistic assumption.
The remaining RH obligation is odd-carry membership, equivalently vacancy
decay, capacity divergence, or divergence of the actual hazard/Schur sums.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Probability.DPP
open RiemannResearch.Analysis.ProjectionDPP

theorem integerKernel_principal_posSemidef (n m : ℕ) (a : Fin m → ℕ) :
    (Matrix.of (fun i j => integerKernel n (a i) (a j))).PosSemidef :=
  principal_posSemidef (finiteSpace n) countingBasis a

theorem limitingKernel_principal_posSemidef (m : ℕ) (a : Fin m → ℕ) :
    (Matrix.of (fun i j => limitingKernel (a i) (a j))).PosSemidef :=
  principal_posSemidef closedSpace countingBasis a

theorem integerKernel_diagonal_bounds (n i : ℕ) :
    0 ≤ integerKernel n i i ∧ integerKernel n i i ≤ 1 :=
  diagonal_bounds (finiteSpace n) countingBasis i (countingBasis_norm_sq i)

theorem limitingKernel_diagonal_one_iff (i : ℕ) :
    limitingKernel i i = 1 ↔ countingBasis i ∈ closedSpace :=
  diagonal_one_iff closedSpace countingBasis i (countingBasis_norm_sq i)

theorem odd_carry_iff_capacity_tendsto :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d → doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      Tendsto tailCapacity atTop atTop :=
  odd_carry_iff_vacancy_tendsto_zero.trans vacancy_tendsto_zero_iff

theorem odd_carry_iff_hazard_not_summable :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d → doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      ¬Summable hazard :=
  odd_carry_iff_vacancy_tendsto_zero.trans vacancy_tendsto_zero_iff_hazard_not_summable

theorem odd_carry_iff_hazard_sum_tendsto :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d → doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      Tendsto (fun N => ∑ j ∈ Finset.range N, hazard j) atTop atTop :=
  odd_carry_iff_vacancy_tendsto_zero.trans vacancy_tendsto_zero_iff_hazard_sum_tendsto

theorem odd_carry_iff_schur_sum_tendsto :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d → doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      Tendsto (fun N => ∑ j ∈ Finset.range N,
        (schurEta j) ^ 2 / schurSigma j) atTop atTop := by
  simpa only [← capacity_eq_sum_schur] using odd_carry_iff_capacity_tendsto

section Probability
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Set ℕ}

/-- The physical site 1 is counting coordinate 0. -/
theorem dpp_first_site_vacancy (n : ℕ) (h : IsDPP μ X (integerKernel n)) :
    μ.real {ω | 0 ∉ X ω} = vacancy n := by
  rw [h.vacancy, vacancy_eq_kernel_complement]

theorem limiting_dpp_first_site_vacancy (h : IsDPP μ X limitingKernel) :
    μ.real {ω | 0 ∉ X ω} = limitingVacancy := by
  rw [h.vacancy, limitingVacancy_eq_kernel_complement]

/-- Given the nested arithmetic DPP coupling, the actual deterministic hazard
is exactly the probability of entry conditioned on current absence. -/
theorem dpp_entry_probability_eq_hazard
    (Z : ℕ → Ω → Set ℕ) (hZ : ∀ n, IsDPP μ (Z n) (integerKernel n))
    (hmono : ∀ n ω, Z n ω ⊆ Z (n + 1) ω) (n : ℕ) :
    μ.real {ω | 0 ∈ Z (n + 1) ω ∧ 0 ∉ Z n ω} /
      μ.real {ω | 0 ∉ Z n ω} = hazard n := by
  have hq : 0 < μ.real {ω | 0 ∉ Z n ω} := by
    rw [dpp_first_site_vacancy n (hZ n)]
    exact vacancy_pos n
  rw [(hZ n).entry_ratio (hZ (n + 1)) (hmono n) 0 hq,
    dpp_first_site_vacancy (n + 1) (hZ (n + 1)), dpp_first_site_vacancy n (hZ n)]
  rfl

theorem odd_carry_iff_first_site_ae (h : IsDPP μ X limitingKernel) :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d → doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      (∀ᵐ ω ∂μ, 0 ∈ X ω) :=
  limitingKernel_first_site_one_iff_odd_carry.symm.trans (h.mem_ae_iff 0).symm

theorem odd_carry_iff_full_occupation_ae (h : IsDPP μ X limitingKernel) :
    (∀ d : ℕ, ∀ hd : 3 ≤ d, Odd d → doublingCarryHilbert d (by omega) ∈ closedSpace) ↔
      (∀ᵐ ω ∂μ, X ω = Set.univ) := by
  rw [h.full_occupation_ae_iff]
  constructor
  · intro ho i
    apply (limitingKernel_diagonal_one_iff i).mpr
    rw [odd_carry_iff_closedSpace_eq_top.mp ho]
    trivial
  · intro hd
    exact limitingKernel_first_site_one_iff_odd_carry.mp (hd 0)

theorem riemannHypothesis_of_dpp_first_site_ae (h : IsDPP μ X limitingKernel)
    (hsite : ∀ᵐ ω ∂μ, 0 ∈ X ω) : RiemannHypothesis :=
  riemannHypothesis_of_odd_carry ((odd_carry_iff_first_site_ae h).mpr hsite)

theorem finite_dpp_first_site_probability_tendsto
    (μs : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μs n)]
    (Xs : ℕ → Ω → Set ℕ) (h : ∀ n, IsDPP (μs n) (Xs n) (integerKernel n)) :
    Tendsto (fun n => (μs n).real {ω | 0 ∉ Xs n ω}) atTop (𝓝 limitingVacancy) := by
  have he : (fun n => (μs n).real {ω | 0 ∉ Xs n ω}) = vacancy :=
    funext fun n => dpp_first_site_vacancy n (h n)
  rw [he]
  exact vacancy_tendsto

theorem riemannHypothesis_of_dpp_vacancy_tendsto_zero
    (μs : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μs n)]
    (Xs : ℕ → Ω → Set ℕ) (h : ∀ n, IsDPP (μs n) (Xs n) (integerKernel n))
    (hvanish : Tendsto (fun n => (μs n).real {ω | 0 ∉ Xs n ω}) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have he : (fun n => (μs n).real {ω | 0 ∉ Xs n ω}) = vacancy :=
    funext fun n => dpp_first_site_vacancy n (h n)
  rw [he] at hvanish
  exact riemannHypothesis_of_vacancy_tendsto_zero hvanish

end Probability
end RiemannResearch.RH.Pareto.IntegerDPP
