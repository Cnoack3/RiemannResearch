import RiemannResearch.RH.QDivisorDPP
import RiemannResearch.RH.QDivisorHilbertBasis
import Mathlib.LinearAlgebra.Matrix.Rank
import RiemannResearch.Analysis.FiniteFeatureKernel
import RiemannResearch.Probability.DeterminantalMoments
import RiemannResearch.Probability.DeterminantalWindow
import Mathlib.Tactic.Ring

/-!
# Exact finite-rank and moving-window laws of the Q divisor DPP

Source: user-provided finite-rank occupation argument, 13 October 2026.
Moment and gap statements reuse the existing DPP providers.
These identities assert no scaling limit or RH result.
Counting coordinate i denotes physical integer i+1.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoHilbert QDivisorHilbert
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Analysis.FiniteFeature
open RiemannResearch.Probability.DPP

def basisFeatures (N : ℕ) (i : ℕ) (r : Fin N) : ℝ :=
  normalizedDivisorWavelet (basisIndex r) i

theorem basisKernel_eq_featureKernel (N : ℕ) :
    basisKernel N = featureKernel (basisFeatures N) := by
  funext i j
  exact basisKernel_eq_sum N i j

theorem basisKernel_principal_rank_le (N m : ℕ) (e : Fin m → ℕ) :
    (Matrix.of (fun i j => basisKernel N (e i) (e j))).rank ≤ N := by
  rw [basisKernel_eq_featureKernel]
  exact principal_rank_le (basisFeatures N) e

theorem basisKernel_principal_det_eq_zero (N m : ℕ)
    (e : Fin m → ℕ) (hm : N < m) :
    (Matrix.of (fun i j => basisKernel N (e i) (e j))).det = 0 := by
  rw [basisKernel_eq_featureKernel]
  exact principal_det_eq_zero (basisFeatures N) e hm

/-- Exact probability zero, not merely an asymptotic upper bound. -/
theorem basisLaw_occupation_eq_zero_of_dimension_lt (N m : ℕ)
    (e : Fin m ↪ ℕ) (hm : N < m) :
    (basisLaw N).real {x | ∀ i, x (e i) = true} = 0 := by
  have hc := (basisLaw_isDPP N).correlation m e
  change (basisLaw N).real {x | ∀ i, x (e i) = true} =
    (Matrix.of (fun i j => basisKernel N (e i) (e j))).det at hc
  rw [hc]
  exact basisKernel_principal_det_eq_zero N m e hm

theorem basisLaw_succ_window_occupation_eq_zero (N : ℕ)
    (e : Fin (N + 1) ↪ ℕ) :
    (basisLaw N).real {x | ∀ i, x (e i) = true} = 0 :=
  basisLaw_occupation_eq_zero_of_dimension_lt N (N + 1) e (Nat.lt_succ_self N)

theorem basisKernel_symm (N i j : ℕ) :
    basisKernel N i j = basisKernel N j i :=
  kernel_symmetric (basisSpace N) countingBasis i j

theorem basisLaw_two_point (N i j : ℕ) (hij : i ≠ j) :
    (basisLaw N).real {x | x i = true ∧ x j = true} =
      basisKernel N i i * basisKernel N j j - (basisKernel N i j) ^ 2 := by
  have h := (basisLaw_isDPP N).two_point hij
  change (basisLaw N).real {x | x i = true ∧ x j = true} = _ at h
  rw [basisKernel_symm N j i] at h
  simpa only [pow_two] using h

theorem basisLaw_occupancy_covariance (N i j : ℕ) (hij : i ≠ j) :
    (basisLaw N).real {x | x i = true ∧ x j = true} -
      (basisLaw N).real {x | x i = true} *
        (basisLaw N).real {x | x j = true} = -(basisKernel N i j) ^ 2 := by
  have hi := (basisLaw_isDPP N).occupation i
  have hj := (basisLaw_isDPP N).occupation j
  change (basisLaw N).real {x | x i = true} = basisKernel N i i at hi
  change (basisLaw N).real {x | x j = true} = basisKernel N j j at hj
  rw [basisLaw_two_point N i j hij, hi, hj]
  ring

/-- The embedding and its cardinality may be chosen afresh at every N. -/
theorem basisLaw_moving_expected_count (m : ℕ → ℕ)
    (e : (N : ℕ) → Fin (m N) ↪ ℕ) (N : ℕ) :
    (∫ x, windowCount (fun x => {i | x i = true}) (e N) x ∂basisLaw N) =
      ∑ i, basisKernel N (e N i) (e N i) :=
  (basisLaw_isDPP N).expected_windowCount (e N)

theorem basisLaw_moving_expected_vacancies (m : ℕ → ℕ)
    (e : (N : ℕ) → Fin (m N) ↪ ℕ) (N : ℕ) :
    (∫ x, (m N : ℝ) - windowCount (fun x => {i | x i = true}) (e N) x
      ∂basisLaw N) =
        (m N : ℝ) - ∑ i, basisKernel N (e N i) (e N i) := by
  rw [integral_sub (integrable_const _)
    ((basisLaw_isDPP N).windowCount_integrable (e N)),
    (basisLaw_isDPP N).expected_windowCount (e N)]
  simp

theorem basisLaw_moving_variance (m : ℕ → ℕ)
    (e : (N : ℕ) → Fin (m N) ↪ ℕ) (N : ℕ) :
    ProbabilityTheory.variance
      (windowCount (fun x => {i | x i = true}) (e N)) (basisLaw N) =
        (∑ i, basisKernel N (e N i) (e N i)) -
          ∑ i, ∑ j, (basisKernel N (e N i) (e N j)) ^ 2 := by
  have hterm (i j : Fin (m N)) :
      basisKernel N (e N i) (e N j) * basisKernel N (e N j) (e N i) =
        (basisKernel N (e N i) (e N j)) ^ 2 := by
    rw [basisKernel_symm N (e N j) (e N i)]
    ring
  simpa only [hterm] using (basisLaw_isDPP N).variance_windowCount (e N)

theorem basisLaw_moving_gap (m : ℕ → ℕ)
    (e : (N : ℕ) → Fin (m N) ↪ ℕ) (N : ℕ) :
    (basisLaw N).real {x | ∀ i, x (e N i) = false} =
      (1 - Matrix.of (fun i j => basisKernel N (e N i) (e N j))).det := by
  have hK : (Matrix.of (fun i j : Fin (m N) =>
      basisKernel N (e N i) (e N j))).PosSemidef :=
    principal_posSemidef (basisSpace N) countingBasis (e N)
  have hI : (1 - Matrix.of (fun i j : Fin (m N) =>
      basisKernel N (e N i) (e N j))).PosSemidef := by
    apply identity_sub_principal_posSemidef (basisSpace N) countingBasis (e N)
    intro i j
    simp only [countingBasis_inner, (e N).injective.eq_iff]
  have h := (basisLaw_isDPP N).finite_gap (e N)
    (fun S => exactWeight_nonneg _ hK hI S)
  simpa using h

/-- Simultaneous movement of window size and location does not alter the rank bound. -/
theorem basisLaw_moving_occupation_obstruction (m : ℕ → ℕ)
    (e : (N : ℕ) → Fin (m N) ↪ ℕ) (N : ℕ) (hm : N < m N) :
    (basisLaw N).real {x | ∀ i, x (e N i) = true} = 0 :=
  basisLaw_occupation_eq_zero_of_dimension_lt N (m N) (e N) hm

end RiemannResearch.RH.QDivisorDPP
