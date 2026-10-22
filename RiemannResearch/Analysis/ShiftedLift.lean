import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative shifted lifts in a real Hilbert space

Source: user-provided shifted-lift argument recorded in
RH/ActualResidualRegularityRoutes20260924.md, Route 3.
The source supports the statement and proof strategy. This module verifies
only Hilbert-space identities and finite-subspace minimization consequences;
it supplies no arithmetic rate and makes no assertion of RH.

For a finite lift family, take V to be its span. The hypothesis hnormal below
is exactly the corresponding finite normal-equation condition. Thus a
separately obtained matrix solution gives the displayed attained minimum
without requiring an RH-strength assumption.
-/

noncomputable section

namespace RiemannResearch.Analysis.ShiftedLift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The difference map D = I - S. -/
def difference (S : H →ₗ[ℝ] H) : H →ₗ[ℝ] H := LinearMap.id - S

@[simp] theorem difference_apply (S : H →ₗ[ℝ] H) (v : H) :
    difference S v = v - S v := rfl

/-- Squared error of a lift, with a quadratic norm penalty. -/
def regularizedEnergy (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (v : H) : ℝ :=
  ‖difference S v - a‖ ^ 2 + t ^ 2 * ‖v‖ ^ 2

/-- Exact shifted-lift identity. -/
theorem residual_sq_eq_error_sq_add_double_inner_shift
    (S : H →ₗ[ℝ] H) (hS : ∀ x : H, ‖S x‖ = ‖x‖)
    (a v : H) (horth : inner ℝ a v = 0) :
    ‖a‖ ^ 2 = ‖difference S v - a‖ ^ 2 +
      2 * inner ℝ (difference S v - a) (S v) := by
  change ‖a‖ ^ 2 = ‖v - S v - a‖ ^ 2 + 2 * inner ℝ (v - S v - a) (S v)
  have he : v - S v - a = (v - a) - S v := by
    abel
  have hdiff : ‖v - a‖ ^ 2 = ‖v‖ ^ 2 + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm a v, horth]
    ring
  rw [he, norm_sub_sq_real]
  simp only [inner_sub_left, real_inner_self_eq_norm_sq, hS]
  rw [hdiff]
  ring

/-- A quantitative consequence of the shifted-lift identity. -/
theorem residual_sq_le_regularized_scaled
    (S : H →ₗ[ℝ] H) (hS : ∀ x : H, ‖S x‖ = ‖x‖)
    (a v : H) (horth : inner ℝ a v = 0) (t : ℝ) (ht : 0 < t) :
    ‖a‖ ^ 2 ≤ ((1 + t) / t) * regularizedEnergy S a t v := by
  have hid := residual_sq_eq_error_sq_add_double_inner_shift S hS a v horth
  have hinner : inner ℝ (difference S v - a) (S v) ≤
      ‖difference S v - a‖ * ‖v‖ := by
    calc
      inner ℝ (difference S v - a) (S v) ≤
          ‖difference S v - a‖ * ‖S v‖ :=
        real_inner_le_norm _ _
      _ = ‖difference S v - a‖ * ‖v‖ := by rw [hS]
  have hfirst : ‖a‖ ^ 2 ≤
      ‖difference S v - a‖ ^ 2 + 2 * (‖difference S v - a‖ * ‖v‖) := by
    linarith
  have htfirst := mul_le_mul_of_nonneg_right hfirst (le_of_lt ht)
  have hsq : 0 ≤ (‖difference S v - a‖ - t * ‖v‖) ^ 2 := sq_nonneg _
  have ht3p : 0 ≤ t ^ 3 * ‖v‖ ^ 2 := by positivity
  have hmul : ‖a‖ ^ 2 * t ≤
      (1 + t) * (‖difference S v - a‖ ^ 2 + t ^ 2 * ‖v‖ ^ 2) := by
    nlinarith
  calc
    ‖a‖ ^ 2 ≤
        ((1 + t) * (‖difference S v - a‖ ^ 2 + t ^ 2 * ‖v‖ ^ 2)) / t :=
      (le_div_iff₀ ht).mpr (by simpa [mul_comm] using hmul)
    _ = ((1 + t) / t) * regularizedEnergy S a t v := by
      unfold regularizedEnergy
      ring

/-- Exact completion of the regularized energy at a normal solution. -/
theorem regularizedEnergy_completion
    (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (V : Submodule ℝ H)
    (v₀ v : H) (hv₀ : v₀ ∈ V) (hv : v ∈ V)
    (hnormal : ∀ w ∈ V,
      inner ℝ (difference S v₀ - a) (difference S w) +
        t ^ 2 * inner ℝ v₀ w = 0) :
    regularizedEnergy S a t v =
      regularizedEnergy S a t v₀ +
        (‖difference S (v - v₀)‖ ^ 2 + t ^ 2 * ‖v - v₀‖ ^ 2) := by
  have hw : v - v₀ ∈ V := V.sub_mem hv hv₀
  have hcross := hnormal (v - v₀) hw
  have hD : difference S v - a =
      (difference S v₀ - a) + difference S (v - v₀) := by
    simp only [difference_apply, map_sub]
    abel
  have hvsplit : v = v₀ + (v - v₀) := by
    abel
  have hnorm : ‖v‖ ^ 2 =
      ‖v₀‖ ^ 2 + 2 * inner ℝ v₀ (v - v₀) + ‖v - v₀‖ ^ 2 := by
    calc
      ‖v‖ ^ 2 = ‖v₀ + (v - v₀)‖ ^ 2 :=
        congrArg (fun x : H => ‖x‖ ^ 2) hvsplit
      _ = _ := norm_add_sq_real _ _
  unfold regularizedEnergy
  rw [hD, norm_add_sq_real, hnorm]
  linarith

/-- The exact minimum value at a normal solution. -/
theorem regularizedEnergy_eq_norm_sq_sub_pairing
    (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (V : Submodule ℝ H)
    (v₀ : H) (hv₀ : v₀ ∈ V)
    (hnormal : ∀ w ∈ V,
      inner ℝ (difference S v₀ - a) (difference S w) +
        t ^ 2 * inner ℝ v₀ w = 0) :
    regularizedEnergy S a t v₀ =
      ‖a‖ ^ 2 - inner ℝ (difference S v₀) a := by
  have hn := hnormal v₀ hv₀
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at hn
  unfold regularizedEnergy
  rw [norm_sub_sq_real]
  rw [real_inner_comm a (difference S v₀)]
  linarith

/-- The regularized energy is attained at every normal solution in the lift
subspace. -/
theorem regularizedEnergy_isLeast
    (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (V : Submodule ℝ H)
    (v₀ : H) (hv₀ : v₀ ∈ V)
    (hnormal : ∀ w ∈ V,
      inner ℝ (difference S v₀ - a) (difference S w) +
        t ^ 2 * inner ℝ v₀ w = 0) :
    IsLeast {E : ℝ | ∃ v : H, v ∈ V ∧ regularizedEnergy S a t v = E}
      (regularizedEnergy S a t v₀) := by
  constructor
  · exact ⟨v₀, hv₀, rfl⟩
  · rintro E ⟨v, hv, rfl⟩
    rw [regularizedEnergy_completion S a t V v₀ v hv₀ hv hnormal]
    exact le_add_of_nonneg_right (by positivity)

end RiemannResearch.Analysis.ShiftedLift
