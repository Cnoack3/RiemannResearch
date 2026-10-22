import RiemannResearch.Analysis.ContractiveProducts
import RiemannResearch.RH.BurnolZeroFactors

/-!
# Exact cutoff and logarithmic identities for Burnol factors

Derived algebraic consequences of the product in Burnol, Theorem 1.2,
https://arxiv.org/abs/math/9910055. A sequence may repeat a zero to encode
multiplicity; the logarithmic theorem also accepts explicit multiplicities.
No sequence is claimed here to enumerate the actual zeta zeros.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Burnol

/-- The exact finite defect, with every earlier factor retained. -/
theorem cutoff_defect (ρ : ℕ → ℂ) (h0 : ∀ k, ρ k ≠ 0) (N : ℕ) :
    1 - Real.partialProduct (fun k => factorSq (ρ k)) N =
      ∑ k ∈ Finset.range N,
        Real.partialProduct (fun j => factorSq (ρ j)) k *
          ((2 * (ρ k).re - 1) / Complex.normSq (ρ k)) := by
  rw [Real.one_sub_partialProduct_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_sub_factorSq (h0 k)]

/-- Multiplicity contributes a geometric sum, not merely a linear defect. -/
theorem multiplicity_defect {ρ : ℂ} (h0 : ρ ≠ 0) (m : ℕ) :
    1 - factorSq ρ ^ m = ((2 * ρ.re - 1) / Complex.normSq ρ) *
      ∑ k ∈ Finset.range m, factorSq ρ ^ k := by
  rw [Real.one_sub_pow_eq_mul_sum, one_sub_factorSq h0]

/-- Contractive zero factors have an exact infinite weighted defect sum. -/
theorem hasSum_cutoff_defects (ρ : ℕ → ℂ) (h0 : ∀ k, ρ k ≠ 0)
    (hhalf : ∀ k, 1 / 2 ≤ (ρ k).re) {L : ℝ}
    (hL : Tendsto (Real.partialProduct (fun k => factorSq (ρ k))) atTop (𝓝 L)) :
    HasSum (fun k => Real.partialProduct (fun j => factorSq (ρ j)) k *
      ((2 * (ρ k).re - 1) / Complex.normSq (ρ k))) (1 - L) := by
  simpa only [one_sub_factorSq (h0 _)] using
    Real.hasSum_partialProduct_defects (fun k => factorSq (ρ k))
      (fun k => factorSq_nonneg _) (fun k => factorSq_le_one (hhalf k)) hL

/-- The squared cutoff product equals the exponential of minus twice the
multiplicity-weighted logarithmic zero sum. -/
theorem cutoff_eq_exp_log_sum (ρ : ℕ → ℂ) (m : ℕ → ℕ)
    (h0 : ∀ k, ρ k ≠ 0) (h1 : ∀ k, ρ k ≠ 1) (N : ℕ) :
    Real.partialProduct (fun k => factorSq (ρ k) ^ m k) N =
      Real.exp (-2 * ∑ k ∈ Finset.range N,
        (m k : ℝ) * Real.log ‖ρ k / (1 - ρ k)‖) := by
  rw [Real.partialProduct_eq_exp_sum_log _ (fun k => pow_pos (factorSq_pos (h0 k) (h1 k)) _)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.log_pow, log_factorSq (h0 k) (h1 k)]
  ring

end RiemannResearch.RH.Burnol
