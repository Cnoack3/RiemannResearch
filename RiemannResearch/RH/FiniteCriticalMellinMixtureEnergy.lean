import RiemannResearch.RH.CriticalMellinGramLimits
import RiemannResearch.RH.CriticalMellinMixtureEnergy
import Mathlib.Algebra.Star.BigOperators

set_option autoImplicit false

/-!
# Exact logarithmic energy for finite critical Mellin mixtures

Source: user-provided critical-frequency energy argument. Finite expansion
uses the actual modes and all conjugate cross terms. The only analytic input
is the proved pairwise limit in `CriticalMellinGramLimits`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

variable {ι : Type*} [Fintype ι]

def finiteCriticalMixture (a : ι → ℂ) (γ : ι → ℝ) (n : ℕ) : ℂ :=
  ∑ j, a j * mellinMode (MellinFrequency.criticalPoint (γ j)) n

def finiteCriticalCoefficientEnergy (a : ι → ℂ) (γ : ι → ℝ) : ℝ :=
  ∑ j, ‖a j * MellinFrequency.criticalPoint (γ j)‖ ^ 2

private theorem complex_norm_sq_mul_star (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  simp [Complex.sq_norm, Complex.star_def, Complex.mul_conj]

private theorem finiteCriticalMixture_energy_expansion
    (a : ι → ℂ) (γ : ι → ℝ) (n : ℕ) :
    (paretoWeight n : ℂ) * ((‖finiteCriticalMixture a γ n‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ k, (a j * star (a k)) *
        ((paretoWeight n : ℂ) *
          mellinMode (MellinFrequency.criticalPoint (γ j)) n *
          star (mellinMode (MellinFrequency.criticalPoint (γ k)) n)) := by
  classical
  rw [complex_norm_sq_mul_star]
  simp only [finiteCriticalMixture, star_sum, star_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The exact finite double Gram formula, including every complex cross term. -/
theorem finiteCriticalMixture_logEnergy_eq_gram
    (a : ι → ℂ) (γ : ι → ℝ) (N : ℕ) :
    (logEnergy (finiteCriticalMixture a γ) N : ℂ) =
      ∑ j, ∑ k, a j * star (a k) * criticalCross (γ j) (γ k) N := by
  classical
  have hp : (partialEnergy (finiteCriticalMixture a γ) N : ℂ) =
      ∑ j, ∑ k, (a j * star (a k)) *
        (∑ n ∈ Finset.range N, (paretoWeight n : ℂ) *
          mellinMode (MellinFrequency.criticalPoint (γ j)) n *
          star (mellinMode (MellinFrequency.criticalPoint (γ k)) n)) := by
    rw [partialEnergy, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_mul, finiteCriticalMixture_energy_expansion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  rw [logEnergy, Complex.ofReal_div, hp]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [criticalCross]
  ring

private theorem finiteCriticalMixture_diagonal
    (a : ι → ℂ) (γ : ι → ℝ) (hγ : Function.Injective γ) :
    (∑ j, ∑ k, a j * star (a k) *
      (if γ j = γ k then MellinFrequency.criticalPoint (γ j) *
        star (MellinFrequency.criticalPoint (γ k)) else 0)) =
      (finiteCriticalCoefficientEnergy a γ : ℂ) := by
  classical
  simp_rw [hγ.eq_iff]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [finiteCriticalCoefficientEnergy, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [complex_norm_sq_mul_star, star_mul]
  ring

/-- Distinct critical frequencies have exactly their diagonal logarithmic
energy. This statement assumes neither arithmetic annihilation nor RH. -/
theorem finiteCriticalMixture_logEnergy_tendsto
    (a : ι → ℂ) (γ : ι → ℝ) (hγ : Function.Injective γ) :
    Tendsto (logEnergy (finiteCriticalMixture a γ)) atTop
      (𝓝 (finiteCriticalCoefficientEnergy a γ)) := by
  classical
  have h : Tendsto
      (fun N => ∑ j, ∑ k, a j * star (a k) * criticalCross (γ j) (γ k) N)
      atTop (𝓝 (∑ j, ∑ k, a j * star (a k) *
        (if γ j = γ k then MellinFrequency.criticalPoint (γ j) *
          star (MellinFrequency.criticalPoint (γ k)) else 0))) := by
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_finsetSum
    intro k hk
    exact tendsto_const_nhds.mul (criticalCross_tendsto (γ j) (γ k))
  simp_rw [← finiteCriticalMixture_logEnergy_eq_gram] at h
  rw [finiteCriticalMixture_diagonal a γ hγ] at h
  simpa only [Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto _).comp h

/-- A finite mixture of distinct critical modes can have finite Pareto
energy only when every coefficient vanishes. -/
theorem finite_criticalMixture_coefficients_zero_of_summable
    (a : ι → ℂ) (γ : ι → ℝ) (hγ : Function.Injective γ)
    (hs : Summable (fun n => paretoWeight n * ‖finiteCriticalMixture a γ n‖ ^ 2)) :
    ∀ j, a j = 0 := by
  classical
  have he : finiteCriticalCoefficientEnergy a γ = 0 :=
    tendsto_nhds_unique (finiteCriticalMixture_logEnergy_tendsto a γ hγ)
      (summable_logEnergy_tendsto_zero (finiteCriticalMixture a γ) hs)
  intro j
  have hle : ‖a j * MellinFrequency.criticalPoint (γ j)‖ ^ 2 ≤
      finiteCriticalCoefficientEnergy a γ := by
    change ‖a j * MellinFrequency.criticalPoint (γ j)‖ ^ 2 ≤
      ∑ k, ‖a k * MellinFrequency.criticalPoint (γ k)‖ ^ 2
    exact Finset.single_le_sum
      (f := fun k : ι => ‖a k * MellinFrequency.criticalPoint (γ k)‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  rw [he] at hle
  have hz : a j * MellinFrequency.criticalPoint (γ j) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (a j * MellinFrequency.criticalPoint (γ j))]
  exact (mul_eq_zero.mp hz).resolve_right
    (MellinFrequency.criticalPoint_ne_zero (γ j))

end RiemannResearch.RH.Pareto.SpectralObstruction
