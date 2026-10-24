/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Certified lower-Gram bounds for constrained approximation

Source: user-directed complete-Gram experiments, 24 October 2026.
The exact completion below supports rational primal/dual certificates for the
RH head-repair computations. A lower Gram matrix is sufficient; no numerical
inverse of the true Gram or independence of the constraints is assumed.
The second remainder records the full Gram discrepancy, including all mixed
terms, and cannot be silently omitted from the equality.
-/

namespace RiemannResearch.Analysis.ConstrainedGramCertificates

variable {E K H : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup K] [Module ℝ K]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Exact constrained primal/dual gap for a symmetric lower-Gram form.
The two remainders become nonnegative once lower-Gram certification is supplied. -/
theorem feasible_lower_gram_completion
    (Φ : E →ₗ[ℝ] H) (C : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : H) (b : K) (dual : K →ₗ[ℝ] ℝ) (z a : E)
    (hsym : ∀ v w, L v w = L w v)
    (hnormal : ∀ v, L z v = inner ℝ x (Φ v) + dual (C v))
    (hfeasible : C a = b) :
    ‖x - Φ a‖ ^ 2 =
      (‖x‖ ^ 2 + 2 * dual b - L z z) +
        L (a - z) (a - z) + (‖Φ a‖ ^ 2 - L a a) := by
  have hcross : L z a = inner ℝ x (Φ a) + dual b := by
    rw [hnormal, hfeasible]
  have hsq : L (a - z) (a - z) = L a a - 2 * L z a + L z z := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsym a z]
    ring
  rw [norm_sub_sq_real, hsq, hcross]
  ring

/-- A rational lower-Gram normal solution gives a rigorous lower certificate
for every feasible coefficient vector. -/
theorem feasible_lower_gram_certificate
    (Φ : E →ₗ[ℝ] H) (C : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : H) (b : K) (dual : K →ₗ[ℝ] ℝ) (z : E)
    (hsym : ∀ v w, L v w = L w v)
    (hnormal : ∀ v, L z v = inner ℝ x (Φ v) + dual (C v))
    (hpos : ∀ v, 0 ≤ L v v)
    (hlower : ∀ v, L v v ≤ ‖Φ v‖ ^ 2)
    (a : E) (hfeasible : C a = b) :
    ‖x‖ ^ 2 + 2 * dual b - L z z ≤ ‖x - Φ a‖ ^ 2 := by
  rw [feasible_lower_gram_completion Φ C L x b dual z a hsym hnormal hfeasible]
  linarith [hpos (a - z), hlower a]

/-- The certificate also bounds an attained constrained minimum. A feasible
primal candidate independently supplies its upper endpoint. -/
theorem attained_minimum_interval
    (Φ : E →ₗ[ℝ] H) (C : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x : H) (b : K) (dual : K →ₗ[ℝ] ℝ) (z : E)
    (hsym : ∀ v w, L v w = L w v)
    (hnormal : ∀ v, L z v = inner ℝ x (Φ v) + dual (C v))
    (hpos : ∀ v, 0 ≤ L v v)
    (hlower : ∀ v, L v v ≤ ‖Φ v‖ ^ 2)
    (emin : ℝ)
    (hmin : IsLeast {e : ℝ | ∃ a : E, C a = b ∧ ‖x - Φ a‖ ^ 2 = e} emin)
    (a : E) (ha : C a = b) {upper : ℝ} (hupper : ‖x - Φ a‖ ^ 2 ≤ upper) :
    ‖x‖ ^ 2 + 2 * dual b - L z z ≤ emin ∧ emin ≤ upper := by
  constructor
  · obtain ⟨a₀, ha₀, he⟩ := hmin.1
    rw [← he]
    exact feasible_lower_gram_certificate Φ C L x b dual z hsym hnormal hpos hlower a₀ ha₀
  · exact (hmin.2 ⟨a, ha, rfl⟩).trans hupper

/-- Subtracting a certified projection-defect interval isolates the actual
normal repair energy, without confusing it with the constrained residual. -/
theorem repair_cost_interval (δ repair total δlo δhi elo ehi : ℝ)
    (hid : total = δ + repair)
    (hδlo : δlo ≤ δ) (hδhi : δ ≤ δhi)
    (helo : elo ≤ total) (hehi : total ≤ ehi) :
    elo - δhi ≤ repair ∧ repair ≤ ehi - δlo := by
  constructor <;> linarith

end RiemannResearch.Analysis.ConstrainedGramCertificates
