/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.CompensatedSourceCertificate
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
/-!
# Finite Gram capacity under translation by Hilbert observations

Source: continuation of the user-provided Pareto capacity handoff
(2026-09-21), for the source-translation strategy. These general identities
retain the exact signed mixed pairing. The RH application is in
ParetoCoprimeDefectVariational.
-/

noncomputable section
open scoped BigOperators
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
namespace RiemannResearch.Analysis.FiniteGramCapacity
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem minimumVector_sub_observed {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    minimumVector hv (b - cross v z) =
      minimumVector hv b - minimumVector hv (cross v z) := by
  simp only [minimumVector, map_sub]
theorem capacity_sub_observed_exact {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    capacity hv (b - cross v z) =
      capacity hv b - 2 * inner ℝ (minimumVector hv b) z +
        capacity hv (cross v z) := by
  have hpair : inner ℝ (minimumVector hv b) (minimumVector hv (cross v z)) =
      inner ℝ (minimumVector hv b) z := by
    unfold minimumVector
    rw [inner_synthesis_left, inner_synthesis_left]
    apply Finset.sum_congr rfl
    intro i _
    change _ * inner ℝ (v i) (minimumVector hv (cross v z)) = _
    rw [minimumVector_observation]
    rfl
  rw [capacity_eq_norm_sq, minimumVector_sub_observed, norm_sub_sq_real,
    hpair, ← capacity_eq_norm_sq, ← capacity_eq_norm_sq]
theorem capacity_sub_observed_le {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    capacity hv (b - cross v z) ≤ 2 * capacity hv b + 2 * ‖z‖^2 := by
  have hp := minimumVector_minimizes hv (cross v z) z (fun _ => rfl)
  have hnorm := sq_nonneg ‖minimumVector hv b + minimumVector hv (cross v z)‖
  rw [norm_add_sq_real] at hnorm
  rw [capacity_eq_norm_sq, minimumVector_sub_observed]
  rw [capacity_eq_norm_sq, norm_sub_sq_real]
  nlinarith
theorem capacity_le_sub_observed {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (z : H) :
    capacity hv b ≤ 2 * capacity hv (b - cross v z) + 2 * ‖z‖^2 := by
  have h := capacity_sub_observed_le hv (b - cross v z) (-z)
  have he : b - cross v z - cross v (-z) = b := by
    funext i
    simp [cross]
  simpa only [he, norm_neg] using h

/-! The exact observed inverse-Gram radius and its sharp compensated certificates.
Source: RH_Actual_Arithmetic_Advances_2026-10-07.pdf, Section 7, for the
source-radius strategy; the complete observation residual identity strengthens
that strategy without an inverse operator norm assumption. These eighteen
declarations passed the coherent pinned-source Lean check on 9 October 2026.
-/
open RiemannResearch.Analysis.CompensatedSourceCertificate

theorem capacity_sqrt_eq_minimumVector_norm {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) :
    Real.sqrt (capacity hv b) = ‖minimumVector hv b‖ := by
  rw [capacity_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem minimumVector_observed_norm_le {v : ι → H}
    (hv : LinearIndependent ℝ v) (z : H) :
    ‖minimumVector hv (cross v z)‖ ≤ ‖z‖ := by
  have hs := minimumVector_minimizes hv (cross v z) z (fun _ => rfl)
  nlinarith [norm_nonneg (minimumVector hv (cross v z)), norm_nonneg z]

/-- The optimal observation radius uses the complete signed Gram inverse,
without an inverse operator bound or a bound on the unobserved target part. -/
theorem capacity_sub_observed_sqrt_radius_observed {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    |Real.sqrt (capacity hv (b-cross v z)) - Real.sqrt (capacity hv b)| ≤
      Real.sqrt (capacity hv (cross v z)) := by
  rw [capacity_sqrt_eq_minimumVector_norm, capacity_sqrt_eq_minimumVector_norm,
    capacity_sqrt_eq_minimumVector_norm]
  have h := abs_norm_sub_norm_le
    (minimumVector hv (b-cross v z)) (minimumVector hv b)
  have he : minimumVector hv (b-cross v z) - minimumVector hv b =
      -minimumVector hv (cross v z) := by
    rw [minimumVector_sub_observed]
    abel
  rw [he, norm_neg] at h
  exact h

/-- The sharper radius never exceeds the complete target error radius. -/
theorem capacity_observed_le_norm_sq {v : ι → H}
    (hv : LinearIndependent ℝ v) (z : H) :
    capacity hv (cross v z) ≤ ‖z‖^2 := by
  rw [capacity_eq_norm_sq]
  exact minimumVector_minimizes hv (cross v z) z (fun _ => rfl)

/-- Exact amount saved by replacing the complete target norm with its observed
part: the unobserved residual energy is subtracted, rather than discarded. -/
theorem capacity_observed_exact {v : ι → H}
    (hv : LinearIndependent ℝ v) (z : H) :
    capacity hv (cross v z) =
      ‖z‖^2 - ‖z - minimumVector hv (cross v z)‖^2 := by
  have hc := feasible_norm_sq_completion hv (cross v z) z (fun _ => rfl)
  rw [capacity_eq_norm_sq]
  linarith only [hc]

/-- The complete Gram inverse is used before any target perturbation bound. -/
theorem capacity_sub_observed_sqrt_radius {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    |Real.sqrt (capacity hv (b-cross v z)) - Real.sqrt (capacity hv b)| ≤ ‖z‖ := by
  have h := capacity_sub_observed_sqrt_radius_observed hv b z
  have hr : Real.sqrt (capacity hv (cross v z)) ≤ ‖z‖ := by
    rw [capacity_sqrt_eq_minimumVector_norm]
    exact minimumVector_observed_norm_le hv z
  exact h.trans hr

/-- Orientation used by the scalar certificate API, with the sharper exact
observed target-error capacity as its budget. -/
theorem capacity_sub_observed_sqrt_budget_observed {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    |Real.sqrt (capacity hv b) - Real.sqrt (capacity hv (b-cross v z))| ≤
      Real.sqrt (capacity hv (cross v z)) := by
  rw [abs_sub_comm]
  exact capacity_sub_observed_sqrt_radius_observed hv b z

/-- Complete observed compensation is a certificate for the original gain. -/
theorem capacity_sub_observed_gainCertificate_observed_le {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    gainCertificate (capacity hv (b-cross v z)) (capacity hv (cross v z)) ≤
      capacity hv b := by
  exact gainCertificate_le_gain (capacity_nonneg hv b)
    (capacity_nonneg hv (cross v z))
    (capacity_sub_observed_sqrt_budget_observed hv b z)

/-- The observed certificate dominates the certificate formed with the full
target norm. The exact source `b-cross v z` is identical on both sides. -/
theorem capacity_sub_observed_gainCertificate_le_observed {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    gainCertificate (capacity hv (b-cross v z)) (‖z‖^2) ≤
      gainCertificate (capacity hv (b-cross v z)) (capacity hv (cross v z)) := by
  have hs := Real.sqrt_le_sqrt (capacity_observed_le_norm_sq hv z)
  have hm :
      max (Real.sqrt (capacity hv (b-cross v z)) - Real.sqrt (‖z‖^2)) 0 ≤
        max (Real.sqrt (capacity hv (b-cross v z)) -
          Real.sqrt (capacity hv (cross v z))) 0 :=
    max_le_max (sub_le_sub_left hs _) le_rfl
  have hnL : 0 ≤
      max (Real.sqrt (capacity hv (b-cross v z)) - Real.sqrt (‖z‖^2)) 0 :=
    le_max_right _ _
  have hnR : 0 ≤
      max (Real.sqrt (capacity hv (b-cross v z)) -
        Real.sqrt (capacity hv (cross v z))) 0 :=
    le_max_right _ _
  have hp := mul_nonneg (sub_nonneg.mpr hm) (add_nonneg hnR hnL)
  unfold gainCertificate radiusCertificate
  nlinarith only [hp]

/-- Retaining the observed error, rather than the full target error, sharpens
the relative compensation budget without changing any signed source. -/
theorem capacity_sub_observed_gainCertificate_observed_relative_lower {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) (ε : ℝ)
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1/2)
    (hbudget : capacity hv (cross v z) ≤ ε^2 * capacity hv b) :
    (1-2*ε)^2 * capacity hv b ≤
      gainCertificate (capacity hv (b-cross v z)) (capacity hv (cross v z)) := by
  exact gainCertificate_relative_lower (capacity_nonneg hv b)
    (capacity_nonneg hv (cross v z))
    (capacity_sub_observed_sqrt_budget_observed hv b z) hε hhalf hbudget

/-- Quarter retention from the strictly weaker observed-error budget. -/
theorem capacity_sub_observed_gainCertificate_observed_quarter {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H)
    (hbudget : capacity hv (cross v z) ≤ capacity hv b / 16) :
    capacity hv b / 4 ≤
      gainCertificate (capacity hv (b-cross v z)) (capacity hv (cross v z)) := by
  exact gainCertificate_quarter (capacity_nonneg hv b)
    (capacity_nonneg hv (cross v z))
    (capacity_sub_observed_sqrt_budget_observed hv b z) hbudget

/-- Signed-source comparison in any stated radius, with no inverse norm bound. -/
theorem capacity_sub_observed_sqrt_radius_le {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) (t : ℝ)
    (ht : ‖z‖ ≤ t) :
    |Real.sqrt (capacity hv (b-cross v z)) - Real.sqrt (capacity hv b)| ≤ t :=
  (capacity_sub_observed_sqrt_radius hv b z).trans ht

/-- Orientation and squared radius used by the scalar certificate API. -/
theorem capacity_sub_observed_sqrt_budget {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    |Real.sqrt (capacity hv b) - Real.sqrt (capacity hv (b-cross v z))| ≤
      Real.sqrt (‖z‖^2) := by
  rw [Real.sqrt_sq (norm_nonneg z), abs_sub_comm]
  exact capacity_sub_observed_sqrt_radius hv b z

/-- The signed compensated certificate is a lower bound on the original
complete Gram capacity. No bound on the inverse Gram operator is required. -/
theorem capacity_sub_observed_gainCertificate_le {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    gainCertificate (capacity hv (b-cross v z)) (‖z‖^2) ≤ capacity hv b := by
  exact gainCertificate_le_gain (capacity_nonneg hv b) (sq_nonneg ‖z‖)
    (capacity_sub_observed_sqrt_budget hv b z)

/-- Sharp retained-gain envelope for the actual finite Gram source. -/
theorem capacity_sub_observed_gainCertificate_sharp_lower {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) :
    (max (Real.sqrt (capacity hv b) - 2*‖z‖) 0)^2 ≤
      gainCertificate (capacity hv (b-cross v z)) (‖z‖^2) := by
  have h := gainCertificate_sharp_lower (capacity_nonneg hv b) (sq_nonneg ‖z‖)
    (capacity_sub_observed_sqrt_budget hv b z)
  simpa only [Real.sqrt_sq (norm_nonneg z)] using h

/-- A relative target-error budget retains the optimal `(1-2ε)^2`
fraction of the complete original capacity. -/
theorem capacity_sub_observed_gainCertificate_relative_lower {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H) (ε : ℝ)
    (hε : 0 ≤ ε) (hhalf : ε ≤ 1/2)
    (hbudget : ‖z‖^2 ≤ ε^2 * capacity hv b) :
    (1-2*ε)^2 * capacity hv b ≤
      gainCertificate (capacity hv (b-cross v z)) (‖z‖^2) := by
  exact gainCertificate_relative_lower (capacity_nonneg hv b) (sq_nonneg ‖z‖)
    (capacity_sub_observed_sqrt_budget hv b z) hε hhalf hbudget

/-- Quarter retention requires only the complete target-error budget. -/
theorem capacity_sub_observed_gainCertificate_quarter {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H)
    (hbudget : ‖z‖^2 ≤ capacity hv b / 16) :
    capacity hv b / 4 ≤
      gainCertificate (capacity hv (b-cross v z)) (‖z‖^2) := by
  exact gainCertificate_quarter (capacity_nonneg hv b) (sq_nonneg ‖z‖)
    (capacity_sub_observed_sqrt_budget hv b z) hbudget

/-- A directly reusable two-sided finite certificate under the quarter budget. -/
theorem capacity_sub_observed_gainCertificate_sandwich {v : ι → H}
    (hv : LinearIndependent ℝ v) (b : ι → ℝ) (z : H)
    (hbudget : ‖z‖^2 ≤ capacity hv b / 16) :
    capacity hv b / 4 ≤
        gainCertificate (capacity hv (b-cross v z)) (‖z‖^2) ∧
      gainCertificate (capacity hv (b-cross v z)) (‖z‖^2) ≤ capacity hv b :=
  ⟨capacity_sub_observed_gainCertificate_quarter hv b z hbudget,
    capacity_sub_observed_gainCertificate_le hv b z⟩

end RiemannResearch.Analysis.FiniteGramCapacity
