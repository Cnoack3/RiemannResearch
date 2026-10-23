import RiemannResearch.RH.IntegratedRamanujanGram
import RiemannResearch.RH.ParetoGramMeanOptimizer
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ParetoFiniteErrorObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The actual finite Ramanujan inverse-mean optimizer

Source: user-provided September 11, 2026 conversation. This assembles the
proved finite Gram inverse with the full Pareto mean-one optimizer. Neither
invertibility nor normal equations are assumed. Nonzero signal follows, in
particular, whenever conductor 2 belongs to the finite set. No uniform bound
or limiting approximation is asserted.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanOptimizer
open FiniteSchur
noncomputable section

def family (s : Finset ℕ) (i : s) : ℕ → ℝ := ramanujanPacket i

def bound (s : Finset ℕ) (i : s) : ℝ :=
  ∑ d ∈ i.val.divisors, |(ArithmeticFunction.moebius (i.val / d) : ℝ)| * (d : ℝ)

theorem family_bounded (s : Finset ℕ) :
    ∀ i k, |family s i k| ≤ bound s i := fun i k => ramanujanPacket_abs_le i k

def meanVector (s : Finset ℕ) (i : s) : ℝ := paretoMean (family s i)

def coefficients (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) : s → ℝ :=
  ramanujanGramSolve s hs (meanVector s)

def projection (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) : ℕ → ℝ :=
  combination (family s) (coefficients s hs)

def mass (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) : ℝ :=
  paretoMean (projection s hs)

def optimizer (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) : ℕ → ℝ :=
  normalizedProjection (family s) (coefficients s hs)

theorem normal_equations (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (i : s) :
    paretoInner (family s i) (projection s hs) = meanVector s i := by
  rw [projection, ← gramApply_eq_inner (family_bounded s)]
  exact congrFun (ramanujanGramSolve_normal_equations s hs (meanVector s)) i

theorem mass_eq_inverse_mean_quadratic (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    mass s hs = ∑ i : s, coefficients s hs i * meanVector s i := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  unfold mass projection
  rw [← paretoInner_one_right, inner_combination_left (family_bounded s) h1]
  simp only [paretoInner_one_right, meanVector]

theorem projection_energy (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    paretoInner (projection s hs) (projection s hs) = mass s hs :=
  projection_mean_eq_energy (family_bounded s) (coefficients s hs)
    (normal_equations s hs)

theorem mass_pos (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (hm : ∃ i : s, meanVector s i ≠ 0) : 0 < mass s hs := by
  have hnonneg : 0 ≤ mass s hs := by
    rw [← projection_energy s hs]
    exact paretoInner_self_nonneg _
  by_contra hpos
  have hz : mass s hs = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
  have henergy : paretoInner (projection s hs) (projection s hs) = 0 := by
    rw [projection_energy, hz]
  have hvalues := (paretoInner_self_zero_iff_positive
    (combination_bounded (family_bounded s) (coefficients s hs))).mp henergy
  have hzero : projection s hs = 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [projection, combination, family, ramanujanPacket, residue]
    · exact hvalues k (Nat.pos_of_ne_zero hk)
  obtain ⟨i, hi⟩ := hm
  apply hi
  have hn := normal_equations s hs i
  simpa [hzero, paretoInner] using hn.symm

theorem nonzero_mean_of_two_mem (s : Finset ℕ) (h2 : 2 ∈ s) :
    ∃ i : s, meanVector s i ≠ 0 := by
  refine ⟨⟨2, h2⟩, ?_⟩
  change paretoMean (ramanujanPacket 2) ≠ 0
  rw [ramanujanPacket_prime_eq_residue 2 (by decide),
    paretoMean_residue 2 (by decide)]
  exact ne_of_gt (Real.log_pos (by norm_num))

theorem projection_error (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) :
    paretoError (projection s hs) = 1 - mass s hs :=
  projection_error_exact (family_bounded s) (coefficients s hs)
    (normal_equations s hs)

theorem projection_minimizes (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d) (b : s → ℝ) :
    paretoError (projection s hs) ≤ paretoError (combination (family s) b) := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  exact residual_minimizes (family_bounded s) h1 (coefficients s hs)
    (by intro i; simpa only [paretoInner_one_right, projection, meanVector] using normal_equations s hs i) b

theorem optimizer_mean (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (hm : ∃ i : s, meanVector s i ≠ 0) : paretoMean (optimizer s hs) = 1 :=
  normalizedProjection_mean (family_bounded s) (coefficients s hs)
    (ne_of_gt (mass_pos s hs hm))

theorem optimizer_variance (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (hm : ∃ i : s, meanVector s i ≠ 0) :
    paretoVariance (optimizer s hs) = (mass s hs)⁻¹ - 1 :=
  normalizedProjection_variance (family_bounded s) (coefficients s hs)
    (normal_equations s hs) (ne_of_gt (mass_pos s hs hm))

theorem optimizer_completion (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (hm : ∃ i : s, meanVector s i ≠ 0) (b : s → ℝ)
    (hb : paretoMean (combination (family s) b) = 1) :
    paretoVariance (combination (family s) b) = (mass s hs)⁻¹ - 1 +
      paretoInner (fun k => combination (family s) b k - optimizer s hs k)
        (fun k => combination (family s) b k - optimizer s hs k) :=
  normalizedProjection_completion (family_bounded s) (coefficients s hs) b
    (normal_equations s hs) (ne_of_gt (mass_pos s hs hm)) hb

theorem optimizer_minimizes (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (hm : ∃ i : s, meanVector s i ≠ 0) (b : s → ℝ)
    (hb : paretoMean (combination (family s) b) = 1) :
    paretoVariance (optimizer s hs) ≤ paretoVariance (combination (family s) b) :=
  normalizedProjection_minimizes (family_bounded s) (coefficients s hs) b
    (normal_equations s hs) (ne_of_gt (mass_pos s hs hm)) hb

theorem combination_legal (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (ha : ∀ d ∈ s, 2 ∣ d ∨ 3 ∣ d) (b : s → ℝ) :
    combination (family s) b ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  have he : combination (family s) b = ∑ i : s, b i • ramanujanPacket i := by
    ext k
    simp [combination, family]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact ramanujanPacket_twoSeed_mem i (by have := hs i i.property; omega)
    (ha i i.property)

theorem optimizer_legal (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (ha : ∀ d ∈ s, 2 ∣ d ∨ 3 ∣ d) :
    optimizer s hs ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  exact (legalSeedSpan ({2, 3} : Set ℕ)).smul_mem _
    (combination_legal s hs ha (coefficients s hs))

/-- Every packet combination vanishes at every common multiple of its conductors. -/
theorem combination_zero_at_common_multiple (s : Finset ℕ) (b : s → ℝ)
    (Q : ℕ) (hQ : ∀ d ∈ s, d ∣ Q) :
    combination (family s) b Q = 0 := by
  unfold combination family
  apply Finset.sum_eq_zero
  intro i _
  rw [ramanujanPacket_eq_zero_of_dvd (hQ i i.property), mul_zero]
/-- Quantitative finite-space obstruction, uniform over the optimizer coefficients. -/
theorem mass_le_one_sub_common_multiple (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) (Q : ℕ) (hQ : ∀ d ∈ s, d ∣ Q) :
    mass s hs ≤ 1 - positiveWeight Q := by
  have hf := positiveWeight_le_error_of_zero
    (combination_bounded (family_bounded s) (coefficients s hs))
    (combination_zero_at_common_multiple s (coefficients s hs) Q hQ)
  change positiveWeight Q ≤ paretoError (projection s hs) at hf
  rw [projection_error] at hf
  linarith
/-- Every finite positive conductor family has strictly positive full error. -/
theorem mass_lt_one_general (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) : mass s hs < 1 := by
  have hQ : 0 < ∏ d ∈ s, d := Finset.prod_pos (fun d hd => lt_trans Nat.zero_lt_one (hs d hd))
  have hQR : 0 < ((∏ d ∈ s, d : ℕ) : ℝ) := by exact_mod_cast hQ
  have hw : 0 < positiveWeight (∏ d ∈ s, d) := by unfold positiveWeight; positivity
  have := mass_le_one_sub_common_multiple s hs (∏ d ∈ s, d)
    (fun d hd => Finset.dvd_prod_of_mem id hd)
  linarith
theorem optimizer_variance_pos (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) (hm : ∃ i : s, meanVector s i ≠ 0) :
    0 < paretoVariance (optimizer s hs) := by
  rw [optimizer_variance s hs hm]
  apply sub_pos.mpr
  rw [inv_eq_one_div, lt_div_iff₀ (mass_pos s hs hm)]
  simpa using mass_lt_one_general s hs

/-- Every finite allowed conductor set containing 2 has an explicit legal
mean-one optimizer. All analytic quantities refer to the complete Pareto law.
There are no inverse, normal-equation, or nonzero-denominator assumptions. -/
theorem optimizer_spec_of_two_mem (s : Finset ℕ) (hs : ∀ d ∈ s, 1 < d)
    (ha : ∀ d ∈ s, 2 ∣ d ∨ 3 ∣ d) (h2 : 2 ∈ s) :
    0 < mass s hs ∧
    optimizer s hs ∈ legalSeedSpan ({2, 3} : Set ℕ) ∧
    paretoMean (optimizer s hs) = 1 ∧
    paretoVariance (optimizer s hs) = (mass s hs)⁻¹ - 1 ∧
    ∀ b : s → ℝ, paretoMean (combination (family s) b) = 1 →
      paretoVariance (optimizer s hs) ≤ paretoVariance (combination (family s) b) := by
  have hm := nonzero_mean_of_two_mem s h2
  exact ⟨mass_pos s hs hm, optimizer_legal s hs ha, optimizer_mean s hs hm,
    optimizer_variance s hs hm, optimizer_minimizes s hs hm⟩

end
end RiemannResearch.RH.Pareto.RamanujanOptimizer
