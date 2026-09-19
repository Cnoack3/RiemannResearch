import RiemannResearch.RH.ParetoPeriodicRegrouping
import RiemannResearch.LinearAlgebra.WeightedFiniteCovariance

/-!
# Actual Pareto probabilities under controlled conductor enlargement

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
equations (3.1)--(3.5). The fine masses retain the full infinite Pareto tail.
This module does not replace them by uniform residue weights.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
noncomputable section

/-- Exact conditional probabilities on one fiber of `N → N*b`. -/
def conductorFiberProbability (N b r : ℕ) (j : Fin b) : ℝ :=
  progressionWeight (N*b) (r+N*j.val) / progressionWeight N r

/-- Actual weighted packet mean on one conductor fiber. -/
def conductorFiberMean (N b r : ℕ) (x : Fin b → ℝ) : ℝ :=
  ∑ j, conductorFiberProbability N b r j * x j

theorem conductorFiberProbability_pos (N b r : ℕ)
    (hN : 0 < N) (hb : 0 < b) (hr : 0 < r) (j : Fin b) :
    0 < conductorFiberProbability N b r j := by
  apply div_pos
  · exact progressionWeight_pos (N*b) (r+N*j.val) (Nat.mul_pos hN hb) (by omega)
  · exact progressionWeight_pos N r hN hr

theorem conductorFiberProbability_sum (N b r : ℕ)
    (hN : 0 < N) (hb : 0 < b) (hr : 0 < r) :
    (∑ j, conductorFiberProbability N b r j) = 1 := by
  unfold conductorFiberProbability
  rw [← Finset.sum_div, ← progressionWeight_compatibility N b r hN hb]
  exact div_self (ne_of_gt (progressionWeight_pos N r hN hr))

theorem conductorFiberProbability_mass (N b r : ℕ)
    (hN : 0 < N) (hr : 0 < r) (j : Fin b) :
    progressionWeight N r * conductorFiberProbability N b r j =
      progressionWeight (N*b) (r+N*j.val) := by
  unfold conductorFiberProbability
  field_simp [ne_of_gt (progressionWeight_pos N r hN hr)]

/-- Fine fiber fluctuations are orthogonal to every constant on the fiber. -/
theorem conductorFiber_fluctuation_sum (N b r : ℕ)
    (hN : 0 < N) (hb : 0 < b) (hr : 0 < r) (x : Fin b → ℝ) :
    (∑ j, progressionWeight (N*b) (r+N*j.val) *
      (x j - conductorFiberMean N b r x)) = 0 := by
  calc
    _ = progressionWeight N r * ∑ j, conductorFiberProbability N b r j *
        (x j - conductorFiberMean N b r x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, conductorFiberProbability_mass N b r hN hr j]
    _ = 0 := by
      rw [show (∑ j, conductorFiberProbability N b r j *
        (x j - conductorFiberMean N b r x)) = 0 from
        normalized_centered_sum _ x (conductorFiberProbability_sum N b r hN hb hr)]
      simp

/-- A full signed covariance entry computed from the actual fine masses. -/
theorem conductorFiber_covariance (N b r : ℕ)
    (hN : 0 < N) (hb : 0 < b) (hr : 0 < r) (x y : Fin b → ℝ) :
    (∑ j, progressionWeight (N*b) (r+N*j.val) *
      (x j - conductorFiberMean N b r x) * (y j - conductorFiberMean N b r y)) =
      progressionWeight N r * ((∑ j, conductorFiberProbability N b r j * x j * y j) -
        conductorFiberMean N b r x * conductorFiberMean N b r y) := by
  calc
    _ = progressionWeight N r * ∑ j, conductorFiberProbability N b r j *
        (x j - conductorFiberMean N b r x) * (y j - conductorFiberMean N b r y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, ← mul_assoc, conductorFiberProbability_mass N b r hN hr j]
    _ = _ := by
      unfold conductorFiberMean
      rw [normalized_centered_product _ x y
        (conductorFiberProbability_sum N b r hN hb hr)]

/-- Pairwise formula for each covariance entry, including the off-diagonal signs. -/
theorem conductorFiber_covariance_pairwise (N b r : ℕ)
    (hN : 0 < N) (hb : 0 < b) (hr : 0 < r) (x y : Fin b → ℝ) :
    (∑ j, progressionWeight (N*b) (r+N*j.val) *
      (x j - conductorFiberMean N b r x) * (y j - conductorFiberMean N b r y)) =
      (1/2 : ℝ) * progressionWeight N r * ∑ j, ∑ t,
        conductorFiberProbability N b r j * conductorFiberProbability N b r t *
          (x j - x t) * (y j - y t) := by
  rw [conductorFiber_covariance N b r hN hb hr x y]
  have h := normalized_centered_product_pairwise
    (conductorFiberProbability N b r) x y (conductorFiberProbability_sum N b r hN hb hr)
  rw [normalized_centered_product _ x y
    (conductorFiberProbability_sum N b r hN hb hr)] at h
  change progressionWeight N r * ((∑ j, conductorFiberProbability N b r j * x j * y j) -
    (∑ j, conductorFiberProbability N b r j * x j) *
      (∑ j, conductorFiberProbability N b r j * y j)) = _
  rw [h]
  ring

/-- The full innovation covariance is the sum over every old residue fiber. -/
theorem conductor_covariance (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (x y : Fin N → Fin b → ℝ) :
    (∑ r : Fin N, ∑ j : Fin b,
      progressionWeight (N*b) (r.val+1+N*j.val) *
        (x r j - conductorFiberMean N b (r.val+1) (x r)) *
        (y r j - conductorFiberMean N b (r.val+1) (y r))) =
      ∑ r : Fin N, progressionWeight N (r.val+1) *
        ((∑ j : Fin b, conductorFiberProbability N b (r.val+1) j * x r j * y r j) -
          conductorFiberMean N b (r.val+1) (x r) *
          conductorFiberMean N b (r.val+1) (y r)) := by
  apply Finset.sum_congr rfl
  intro r _
  exact conductorFiber_covariance N b (r.val+1) hN hb (by omega) (x r) (y r)

/-- Global signed pairwise covariance with all off-diagonal fiber terms. -/
theorem conductor_covariance_pairwise (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (x y : Fin N → Fin b → ℝ) :
    (∑ r : Fin N, ∑ j : Fin b,
      progressionWeight (N*b) (r.val+1+N*j.val) *
        (x r j - conductorFiberMean N b (r.val+1) (x r)) *
        (y r j - conductorFiberMean N b (r.val+1) (y r))) =
      (1/2 : ℝ) * ∑ r : Fin N, progressionWeight N (r.val+1) *
        ∑ j : Fin b, ∑ t : Fin b,
          conductorFiberProbability N b (r.val+1) j *
            conductorFiberProbability N b (r.val+1) t *
            (x r j - x r t) * (y r j - y r t) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [conductorFiber_covariance_pairwise N b (r.val+1) hN hb (by omega) (x r) (y r)]
  ring

end
end RiemannResearch.RH.Pareto
