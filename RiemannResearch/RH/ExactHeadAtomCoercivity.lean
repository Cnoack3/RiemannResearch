import RiemannResearch.RH.ExactHeadAtomOptimizer
import Mathlib.Tactic

/-!
# Quantitative coercivity for proper cumulative gcd atoms
First differences give explicit coefficient bounds in the actual complete
Pareto weighted energy. This supplies finite nondegeneracy without a
numerical inverse, a condition-number assumption, or a squarefree period.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomCoercivity
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.Analysis.FiniteProfileEnergy

theorem sample_sq_le_energy (P : ℕ) (hP : 0 < P) (F : ℕ → ℝ) (hF0 : F 0 = 0)
    (r : ℕ) (hr : r < P) :
    F r ^ 2 ≤ (r : ℝ) * ((r : ℝ) + 1) *
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) F := by
  by_cases hz : r = 0
  · simp [hz,hF0]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hz
  have hmem : r ∈ Finset.Icc 1 (P - 1) := Finset.mem_Icc.mpr ⟨hrpos,by omega⟩
  have hs := Finset.single_le_sum
    (f := fun n => progressionWeight P n * F n ^ 2)
    (fun n _ => mul_nonneg (progressionWeight_nonneg P n) (sq_nonneg _)) hmem
  have hl := mul_le_mul_of_nonneg_right (positiveWeight_le_progressionWeight P r hP)
    (sq_nonneg (F r))
  have hden : 0 < (r : ℝ) * ((r : ℝ) + 1) := by positivity
  have heq : ((r : ℝ) * ((r : ℝ) + 1)) * (positiveWeight r * F r ^ 2) = F r ^ 2 := by
    unfold positiveWeight
    field_simp
  have hb := mul_le_mul_of_nonneg_left (hl.trans hs) hden.le
  rwa [heq] at hb

/-- Every proper-divisor coefficient is quantitatively observable in the
complete Pareto energy: c_d^2 <= 4 d^2 E. -/
theorem coefficient_sq_le_energy (P : ℕ) (hP : 0 < P) (D : Finset ℕ) (c : ℕ → ℝ)
    (d : ℕ) (hd : d ∈ D) (hdpos : 0 < d) (hdP : d ∣ P) (hdlt : d < P) :
    c d ^ 2 ≤ 4 * (d : ℝ) ^ 2 *
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (synthesis P D c) := by
  have h1 := sample_sq_le_energy P hP (synthesis P D c) (synthesis_zero P D c) d hdlt
  have h0 := sample_sq_le_energy P hP (synthesis P D c) (synthesis_zero P D c)
    (d - 1) (by omega)
  have hdR : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have hh : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hdpos
    linarith
  rw [hdR] at h0
  rw [← synthesis_divisor_jump P D c d hd hdpos hdP]
  nlinarith [sq_nonneg (synthesis P D c d + synthesis P D c (d - 1))]

theorem coefficient_energy_bound (P : ℕ) (hP : 0 < P) (D : Finset ℕ) (c : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ∣ P ∧ d < P) :
    (∑ d ∈ D, c d ^ 2) ≤ (4 * ∑ d ∈ D, (d : ℝ) ^ 2) *
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (synthesis P D c) := by
  calc
    _ ≤ ∑ d ∈ D, 4 * (d : ℝ) ^ 2 *
        energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (synthesis P D c) := by
      apply Finset.sum_le_sum
      intro d hd
      exact coefficient_sq_le_energy P hP D c d hd (hD d hd).1
        (hD d hd).2.1 (hD d hd).2.2
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem proper_synthesis_energy_pos (P : ℕ) (hP : 0 < P) (D : Finset ℕ) (c : ℕ → ℝ)
    (hD : ∀ d ∈ D, 0 < d ∧ d ∣ P ∧ d < P)
    (hc : ∃ d ∈ D, c d ≠ 0) :
    0 < energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (synthesis P D c) := by
  have hnonneg := energy_nonneg (Finset.Icc 1 (P - 1)) (progressionWeight P)
    (synthesis P D c) (fun r _ => progressionWeight_nonneg P r)
  obtain ⟨d,hd,hcd⟩ := hc
  have hb := coefficient_sq_le_energy P hP D c d hd (hD d hd).1
    (hD d hd).2.1 (hD d hd).2.2
  by_contra! hn
  have he : energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (synthesis P D c) = 0 :=
    le_antisymm hn hnonneg
  rw [he,mul_zero] at hb
  exact (not_lt_of_ge hb) (sq_pos_of_ne_zero hcd)

end RiemannResearch.RH.Pareto.ExactHeadAtomCoercivity
